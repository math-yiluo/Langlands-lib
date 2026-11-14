import Langlands.Automorphic.PrincipalSeriesGammaMatchStatement
import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.HighlyRamified.UniverseTransport
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Correspondence.SupercuspidalOperationRealization

/-!
# Generic principal series with a prescribed central character

For every quasi-character `ω` of `K^×` and every rank `r + 1` there are quasi-characters
`μ_1, …, μ_(r+1)` with product `ω` and a generic irreducible admissible object that is a
subquotient of `i(μ_1, …, μ_(r+1))` and has central character `ω`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic.StableTwist

open Langlands.Correspondence Langlands.GeneralLinear

universe u uU uU' uW

section Subquotient

variable {G : Type*} [Group G] {U : Type uU} {U' : Type uU'} {W : Type uW}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W]

/-- Every representation is a subquotient of itself. -/
theorem isSubquotientOf_self (ρ : Representation ℂ G U) : IsSubquotientOf ρ ρ := by
  refine ⟨⊤, ⟨(⊤ : Submodule ℂ U).subtype, fun g => ?_⟩, ?_⟩
  · ext y
    rfl
  · intro w
    exact ⟨⟨w, Submodule.mem_top⟩, rfl⟩

/-- A subquotient of `ρ` is a subquotient of every representation equivalent to `ρ`. -/
theorem isSubquotientOf_of_equiv_left {ρ : Representation ℂ G U}
    {ρ' : Representation ℂ G U'} {π : Representation ℂ G W} (e : ρ.Equiv ρ')
    (h : IsSubquotientOf ρ π) : IsSubquotientOf ρ' π := by
  obtain ⟨S, f, hf⟩ := h
  have key : ∀ (g : G) (y : U'), e.symm (ρ' g y) = ρ g (e.symm y) := fun g y =>
    Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g y
  let S' : Subrepresentation ρ' :=
    ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g y hy => by
      rw [Submodule.mem_comap] at hy ⊢
      change e.symm (ρ' g y) ∈ S.toSubmodule
      rw [key]
      exact S.apply_mem_toSubmodule g hy⟩
  let r : S'.toSubmodule →ₗ[ℂ] S.toSubmodule :=
    e.symm.toLinearMap.restrict (fun y hy => hy)
  have hr : ∀ (g : G) (y : S'.toSubmodule),
      r (S'.toRepresentation g y) = S.toRepresentation g (r y) := by
    intro g y
    apply Subtype.ext
    exact key g y
  refine ⟨S', ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun y => ?_⟩, ?_⟩
  · change f.toLinearMap (r (S'.toRepresentation g y)) = π g (f.toLinearMap (r y))
    rw [hr]
    exact Representation.IntertwiningMap.isIntertwining _ _ f g (r y)
  · intro w
    obtain ⟨x, rfl⟩ := hf w
    have hx : e.symm.toLinearMap (e x) ∈ S.toSubmodule := by
      change e.symm (e x) ∈ S.toSubmodule
      rw [Representation.Equiv.symm_apply_apply]
      exact x.2
    refine ⟨⟨e x, hx⟩, ?_⟩
    change f.toLinearMap (r ⟨e x, hx⟩) = f.toLinearMap x
    congr 1
    apply Subtype.ext
    exact e.symm_apply_apply (x : U)

/-- A common character twist preserves the subquotient relation. -/
theorem isSubquotientOf_twist {ρ : Representation ℂ G U} {π : Representation ℂ G W}
    (χ : G →* ℂˣ) (h : IsSubquotientOf ρ π) :
    IsSubquotientOf (Langlands.twist χ ρ) (Langlands.twist χ π) := by
  obtain ⟨S, f, hf⟩ := h
  let S' : Subrepresentation (Langlands.twist χ ρ) :=
    ⟨S.toSubmodule, fun g v hv => by
      change ((χ g : ℂˣ) : ℂ) • ρ g v ∈ S.toSubmodule
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  refine ⟨S', ⟨f.toLinearMap, fun g => LinearMap.ext fun y => ?_⟩, hf⟩
  have h1 : S'.toRepresentation g y = ((χ g : ℂˣ) : ℂ) • S.toRepresentation g y := rfl
  change f.toLinearMap (S'.toRepresentation g y) = ((χ g : ℂˣ) : ℂ) • π g (f.toLinearMap y)
  rw [h1, map_smul]
  congr 1
  exact Representation.IntertwiningMap.isIntertwining _ _ f g y

end Subquotient

section PrincipalSeries

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance principalSeriesModelTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance principalSeriesModelGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

local instance principalSeriesModelGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopologicalGroup n

/-- A quasi-character as a smooth character of `K^×`. -/
def quasiSmoothCharacter (η : QuasiCharacter K) :
    Induction.SmoothCharacter ℂ K.Carrierˣ :=
  ⟨η.toMonoidHom, RankinSelberg.quasicharacter_isOpen_ker K.canonicalTopologicalData η⟩

/-- The twist of the rank-one block `μ ∘ det` by `η ∘ det` is `(μ η) ∘ det`. -/
def characterBlockTwistEquiv (μ η : QuasiCharacter K) :
    (Langlands.twist (determinantQuasiCharacter K 1 η)
      (characterRepresentation (determinantQuasiCharacter K 1 μ))).Equiv
      (characterRepresentation (determinantQuasiCharacter K 1 (μ * η))) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) fun g => by
    apply LinearMap.ext
    intro v
    change ((η (GeneralLinear.determinant g) : ℂˣ) : ℂ) •
        (((μ (GeneralLinear.determinant g) : ℂˣ) : ℂ) • v) =
      ((μ (GeneralLinear.determinant g) * η (GeneralLinear.determinant g) : ℂˣ) : ℂ) • v
    rw [smul_smul, Units.val_mul, mul_comm]

/-- The determinant twist of a normalized principal series by `η` is the principal series
of the twisted characters. -/
def principalSeriesTwistEquiv {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter K)
    (η : QuasiCharacter K) :
    (Langlands.twist (determinantQuasiCharacter K r.succPNat η)
      (principalSeries K r μ)).Equiv (principalSeries K r (fun i => μ i * η)) :=
  (K.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv (borelShape r)
    (quasiSmoothCharacter K η) _).trans
    (K.canonicalTopologicalData.normalizedProductInducedEquiv (borelShape r)
      (fun i => characterBlockTwistEquiv K (μ i) η))

/-- **Twisted generic constituent.** If `π` has a generic representative that is a
subquotient of `i(μ)`, then every twist of `π` by `η` has a generic representative that
is a subquotient of `i(μ η)`. -/
theorem exists_generic_subquotient_twist {r : ℕ} (ψ : NontrivialAdditiveCharacter K)
    (μ : Fin (r + 1) → QuasiCharacter K) (η : QuasiCharacter K)
    {π πη : AutomorphicClass.{u, u} K r.succPNat}
    (hπ : ∃ A : AutomorphicObject.{u, u} K r.succPNat,
      automorphicClassOf K A = π ∧
        (Whittaker.IsGeneric ψ r A.obj.representation ∧
           IsSubquotientOf (principalSeries K r μ) A.obj.representation))
    (htw : IsCharacterTwist K η π πη) :
    ∃ B : AutomorphicObject.{u, u} K r.succPNat,
      automorphicClassOf K B = πη ∧
        (Whittaker.IsGeneric ψ r B.obj.representation ∧
           IsSubquotientOf (principalSeries K r (fun i => μ i * η)) B.obj.representation) := by
  obtain ⟨A, rfl, hgen, hsub⟩ := hπ
  obtain ⟨A', B, hA', rfl, ⟨e⟩⟩ := htw
  obtain ⟨e'⟩ := (automorphicClassOf_eq_iff K A' A).mp hA'
  let f : (Langlands.twist (determinantQuasiCharacter K r.succPNat η)
      A.obj.representation).Equiv B.obj.representation :=
    (Langlands.twistEquiv _ e'.symm).trans e
  refine ⟨B, rfl, ?_, ?_⟩
  · exact (Whittaker.isGeneric_iff_of_equiv ψ r f).mp
      (RankinSelberg.isGeneric_quasicharacter_twist K.canonicalTopologicalData ψ η hgen)
  · exact (Unramified.isSubquotientOf_iff_of_equiv f).mp
      (isSubquotientOf_of_equiv_left (principalSeriesTwistEquiv K μ η)
        (isSubquotientOf_twist _ hsub))

/-- Every class has a twist by every quasi-character. -/
theorem exists_isCharacterTwist {n : ℕ+} (η : QuasiCharacter K)
    (π : AutomorphicClass.{u, u} K n) : ∃ πη, IsCharacterTwist K η π πη :=
  ⟨_, (isCharacterTwist_iff_eq_twist K η
    (isOpen_ker_determinantQuasiCharacter K n η) π _).mpr rfl⟩

/-- The normalized principal series `i(μ_1, …, μ_(r+1))` has central character
`∏ μ_i`. -/
theorem principalSeries_hasGLCentralCharacter {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter K) :
    Classification.HasGLCentralCharacter K.Carrier (r + 1) (principalSeries K r μ)
      (∏ i, (μ i).toMonoidHom) := by
  unfold principalSeries
  refine K.canonicalTopologicalData.hasScalarCharacter_normalizedProductInduced (borelShape r)
    (fun i => ?_)
  intro a v
  change ((determinantQuasiCharacter K 1 (μ i)
    (GeneralLinear.scalar a) : ℂˣ) : ℂ) • v = _
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  show (((μ i).toMonoidHom
    (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a)) : ℂˣ) : ℂ) • v = _
  rw [hd]

/-- The rank-one supercuspidal object of a norm-one quasi-character is square-integrable
modulo the center. -/
theorem rankOneSupercuspidal_isSquareIntegrable (η : QuasiCharacter K)
    (hη : ∀ a, ‖((η a : ℂˣ) : ℂ)‖ = 1) :
    K.canonicalTopologicalData.IsSquareIntegrable
      (rankOneSupercuspidalObject.{u, u} K η).obj.representation := by
  let T := K.canonicalTopologicalData
  refine Unramified.isSquareIntegrable_of_unitaryScalar K T _
    (rankOneSupercuspidalObject.{u, u} K η).property.2.1
    (determinantQuasiCharacter K 1 η)
    (isOpen_ker_determinantQuasiCharacter K 1 η) ?_ ?_
  · intro g
    exact hη _
  · intro g v
    rfl

/-- The rank-one cuspidal datum of a quasi-character. -/
def rankOneCuspidalDatum (η : QuasiCharacter K) :
    K.canonicalTopologicalData.CuspidalDatum.{u, u} where
  rank := 1
  rank_pos := Nat.one_pos
  cls := (rankOneSupercuspidalObject.{u, u} K η).isoClass

/-- The normalized principal series `i(μ_1, …, μ_m)`, with the lifted rank-one character
objects as factors. -/
def characterBlock {m : ℕ} (μ : Fin m → QuasiCharacter K) :
    SmoothRep.{0, u, u} ℂ (GeneralLinear m K.Carrier) :=
  (K.canonicalTopologicalData.normalizedProductInductionFunctor (BlockShape.singletons m)).obj
    (fun k => (rankOneSupercuspidalObject.{u, u} K (μ k)).obj)

/-- A normalized principal series of norm-one quasi-characters is generic: it is the
product of the singleton segments `[μ_k]`, which are segment heads and pairwise unlinked
(Zelevinsky's classification, `genericSegmentProductExhaustion`). -/
theorem characterBlock_isGeneric (ψ : NontrivialAdditiveCharacter K) {n : ℕ}
    (μ : Fin (n + 1) → QuasiCharacter K) (hμ : ∀ k a, ‖((μ k a : ℂˣ) : ℂ)‖ = 1) :
    Whittaker.IsGeneric ψ n (characterBlock K μ).representation := by
  let T := K.canonicalTopologicalData
  let ρ : Fin (n + 1) → T.CuspidalDatum.{u, u} := fun k => rankOneCuspidalDatum K (μ k)
  let A := fun k => rankOneSupercuspidalObject.{u, u} K (μ k)
  have h : ∑ k, (ρ k).rank = n + 1 := by simp [ρ, rankOneCuspidalDatum]
  let d : T.SegmentProductDatum.{u, u} (n + 1) :=
    PadicField.TopologicalData.SegmentProductDatum.ofCuspidals T ρ h A
  have hhead (i : Fin (n + 1)) : T.IsSegmentHead (d.segments i) (d.blocks i) :=
    Unramified.singletonSegment_isSegmentHead K T (ρ i) (A i) rfl
  have hsq (i : Fin (n + 1)) : T.IsSquareIntegrable (d.blocks i).representation :=
    Unramified.isSquareIntegrable_castRank K T _ _
      (rankOneSupercuspidal_isSquareIntegrable K (μ i) (hμ i))
  have hunl : d.multisegment.IsUnlinked := by
    intro Δ hΔ Δ' hΔ'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hΔ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hΔ'
    exact Classification.squareIntegrableSegmentNonlinkage.{u, 0} T _ _
      (d.blocks i) (d.blocks j) (hhead i) (hhead j) (hsq i) (hsq j)
  have hEq : T.cuspidalProductInduced ρ h A = characterBlock K μ := rfl
  have e := (PadicField.TopologicalData.SegmentProductDatum.ofCuspidalsInducedIso T ρ h A).symm
  rw [hEq] at e
  exact (Classification.genericSegmentProductExhaustion.{u, u} (F := K) T ψ n
    (characterBlock K μ)).mpr ⟨d, hhead, hunl, ⟨e⟩⟩

/-- The character block is the normalized principal series, up to the `ULift` of the
one-dimensional factors. -/
def characterBlockEquiv {r : ℕ} (μ : Fin (r + 1) → QuasiCharacter K) :
    (characterBlock K μ).representation.Equiv (principalSeries K r μ) := by
  let T := K.canonicalTopologicalData
  have hU : (characterBlock K μ).representation =
      T.normalizedProductInduced (BlockShape.singletons (r + 1))
        (fun k => (rankOneSupercuspidalObject.{u, u} K (μ k)).obj.representation) :=
    T.normalizedProductInductionFunctor_obj _ _
  rw [hU]
  unfold principalSeries
  exact T.normalizedProductInducedEquiv (BlockShape.singletons (r + 1)) (fun i =>
    Representation.Equiv.mk ULift.moduleEquiv (fun g => by ext v; rfl))

/-- Every quasi-character is a norm-one quasi-character times an `(r+1)`-st power of an
unramified quasi-character. -/
theorem exists_unitary_mul_pow (ω : QuasiCharacter K) (r : ℕ) :
    ∃ ωu ν : QuasiCharacter K, (∀ a, ‖((ωu a : ℂˣ) : ℂ)‖ = 1) ∧ ω = ωu * ν ^ (r + 1) := by
  let T := K.canonicalTopologicalData
  set c : ℝ := ‖((ω T.uniformizerUnit : ℂˣ) : ℂ)‖ with hc
  have hc0 : 0 < c := norm_pos_iff.mpr (Units.ne_zero _)
  set x : ℝ := c ^ ((1 : ℝ) / (r + 1)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hxr : x ^ (r + 1) = c := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    have : (1 : ℝ) / (r + 1) * ((r + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  let w : ℂˣ := Units.mk0 (x : ℂ) (by exact_mod_cast hx0.ne')
  let ν : QuasiCharacter K := Unramified.character K w
  refine ⟨ω * (ν ^ (r + 1))⁻¹, ν, fun a => ?_, by rw [inv_mul_cancel_right]⟩
  have hω := T.norm_eq_zpow_ord_of_isOpen_ker (ω : K.Carrierˣ →* ℂˣ)
    (RankinSelberg.quasicharacter_isOpen_ker T ω) a
  have hν : ((ν a : ℂˣ) : ℂ) = (x : ℂ) ^ T.ord (a : K.Carrier) := by
    change ((w ^ T.ord (a : K.Carrier) : ℂˣ) : ℂ) = _
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hinv : ((ν ^ (r + 1))⁻¹ : QuasiCharacter K) a = ((ν ^ (r + 1)) a)⁻¹ := rfl
  rw [ContinuousMonoidHom.mul_apply, hinv, ContinuousMonoidHom.pow_apply]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hν, norm_mul,
    norm_inv, norm_pow, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  change ‖((ω a : ℂˣ) : ℂ)‖ * _ = 1
  rw [show ‖((ω a : ℂˣ) : ℂ)‖ = c ^ T.ord (a : K.Carrier) from hω]
  rw [← zpow_natCast (x ^ T.ord (a : K.Carrier)) (r + 1), ← zpow_mul,
    mul_comm (T.ord (a : K.Carrier)) _, zpow_mul, zpow_natCast, hxr]
  exact mul_inv_cancel₀ (zpow_ne_zero _ hc0.ne')

/-- **Generic principal-series model.** For every quasi-character `ω` there are
quasi-characters `μ_1, …, μ_(r+1)` with product `ω` and a generic irreducible admissible
object that is a subquotient of `i(μ)` with central character `ω`. -/
theorem exists_generic_principalSeries_object (ψ : NontrivialAdditiveCharacter K) (r : ℕ)
    (ω : QuasiCharacter K) :
    ∃ (μ : Fin (r + 1) → QuasiCharacter K) (A : AutomorphicObject.{u, u} K r.succPNat),
      ∏ i, μ i = ω ∧ Whittaker.IsGeneric ψ r A.obj.representation ∧
        IsSubquotientOf (principalSeries K r μ) A.obj.representation ∧
        Classification.HasGLCentralCharacter K.Carrier (r + 1) A.obj.representation
          ω.toMonoidHom := by
  classical
  obtain ⟨ωu, ν, hu, hω⟩ := exists_unitary_mul_pow K ω r
  let μu : Fin (r + 1) → QuasiCharacter K := fun i => if i = 0 then ωu else 1
  have hμu : ∀ k a, ‖((μu k a : ℂˣ) : ℂ)‖ = 1 := by
    intro k a
    by_cases hk : k = 0
    · simp only [μu, hk, ite_true]
      exact hu a
    · simp only [μu, hk, ite_false]
      simp
  let μ : Fin (r + 1) → QuasiCharacter K := fun i => μu i * ν
  have hprod : ∏ i, μ i = ω := by
    simp only [μ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, μu, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact hω.symm
  have h1 : Whittaker.IsGeneric ψ r (principalSeries K r μu) :=
    (Whittaker.isGeneric_iff_of_equiv ψ r (characterBlockEquiv K μu)).mp
      (characterBlock_isGeneric K ψ μu hμu)
  have h2 : Whittaker.IsGeneric ψ r (principalSeries K r μ) :=
    (Whittaker.isGeneric_iff_of_equiv ψ r (principalSeriesTwistEquiv K μu ν)).mp
      (RankinSelberg.isGeneric_quasicharacter_twist K.canonicalTopologicalData ψ ν h1)
  have h3 : Whittaker.IsGeneric ψ r (characterBlock K μ).representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r (characterBlockEquiv K μ).symm).mp h2
  let A : AutomorphicObject.{u, u} K r.succPNat := ⟨characterBlock K μ, h3.1, h3.2.1⟩
  refine ⟨μ, A, hprod, h3, ?_, ?_⟩
  · exact (Unramified.isSubquotientOf_iff_of_equiv (characterBlockEquiv K μ).symm).mp
      (isSubquotientOf_self _)
  · have h4 := RankinSelberg.HighlyRamified.hasScalarCharacter_of_equiv
      (characterBlockEquiv K μ).symm (principalSeries_hasGLCentralCharacter K μ)
    have h5 : (∏ i, (μ i).toMonoidHom) = ω.toMonoidHom := by
      have key : ∀ (s : Finset (Fin (r + 1))) (a : K.Carrierˣ),
          (∏ i ∈ s, μ i) a = ∏ i ∈ s, μ i a := by
        intro s a
        induction s using Finset.induction_on with
        | empty => rfl
        | insert j s hj ih =>
          rw [Finset.prod_insert hj, Finset.prod_insert hj, ContinuousMonoidHom.mul_apply, ih]
      rw [← hprod]
      ext a
      rw [MonoidHom.finsetProd_apply]
      exact congrArg Units.val (key Finset.univ a).symm
    rw [h5] at h4
    exact h4

end PrincipalSeries

end Langlands.Automorphic.StableTwist
