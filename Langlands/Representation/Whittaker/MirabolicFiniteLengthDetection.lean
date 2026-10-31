import Langlands.Representation.Whittaker.MirabolicFiniteLengthCharacters
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Derivative.MirabolicCharacter
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Detection of nonzero mirabolic representations by twisted coinvariants

A smooth representation of the actual mirabolic group is zero as soon as its
coinvariants vanish for all the characters `θ_S` of the upper-unipotent group,
`θ_S(u) = ψ(∑_{i ∈ S} u_{i,i+1})`, `S` a set of simple roots. The radical step
uses a nonzero vector, a maximal ideal of the group algebra of the radical and
the classification of its locally constant characters.
-/

noncomputable section

open Multiplicative

namespace Langlands.Whittaker.MirabolicFiniteLength

open Jacquet.Localization

universe uA uE uG uF

section Relations

variable {G : Type uG} [Group G]
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- Every character is invariant under the trivial subgroup. -/
theorem isInvariant_bot (U : Subgroup G) (θ : U →* ℂˣ) :
    IsInvariant U ⊥ bot_le θ := by
  intro m u
  congr 1
  apply Subtype.ext
  have hm : (m : G) = 1 := Subgroup.mem_bot.mp m.property
  simp [conjugate, hm]

/-- Relations are unchanged when the acting group is reparametrized surjectively. -/
theorem relations_eq_of_surjective {H : Type*} [Group H] (σ : Representation ℂ G E)
    (U : Subgroup G) (θ : U →* ℂˣ) (τ : Representation ℂ H E) (U' : Subgroup H)
    (θ' : U' →* ℂˣ) (φ : U' → U) (hφ : Function.Surjective φ)
    (hτ : ∀ u : U', τ u = σ (φ u)) (hθ : ∀ u, θ' u = θ (φ u)) :
    relations τ U' θ' = relations σ U θ := by
  unfold relations
  congr 1
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨⟨φ u, v⟩, by simp [hτ, hθ]⟩
  · rintro ⟨⟨u, v⟩, rfl⟩
    obtain ⟨u', rfl⟩ := hφ u
    exact ⟨⟨u', v⟩, by simp [hτ, hθ]⟩

/-- An element normalizing `U` carries the relations of `θ` to those of the
conjugate character. -/
theorem apply_mem_relations (σ : Representation ℂ G E) (U : Subgroup G)
    (θ θ' : U →* ℂˣ) (h : G) (hU : ∀ u : U, h * u * h⁻¹ ∈ U)
    (hθ : ∀ u : U, θ' ⟨h * u * h⁻¹, hU u⟩ = θ u) {v : E}
    (hv : v ∈ relations σ U θ) : σ h v ∈ relations σ U θ' := by
  have hle : relations σ U θ ≤ (relations σ U θ').comap (σ h) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    change σ h (σ u w - (θ u : ℂ) • w) ∈ relations σ U θ'
    have hgen := sub_mem_relations σ U θ' ⟨h * u * h⁻¹, hU u⟩ (σ h w)
    rw [hθ u] at hgen
    have heq : σ h (σ u w - (θ u : ℂ) • w) =
        σ (h * u * h⁻¹) (σ h w) - (θ u : ℂ) • σ h w := by
      rw [map_sub, map_smul]
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel_right]
    rw [heq]
    exact hgen
  exact hle hv

/-- If the acting subgroup is trivial, so are the relations. -/
theorem relations_eq_bot_of_subsingleton (σ : Representation ℂ G E) (U : Subgroup G)
    [Subsingleton U] (θ : U →* ℂˣ) : relations σ U θ = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  have hu : u = 1 := Subsingleton.elim _ _
  subst hu
  simp

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Injectivity of character localization along an injective map into a smooth
representation, phrased with relations. -/
theorem mem_relations_of_injective (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G W} {σ : Representation ℂ G E}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) {w : W}
    (hw : i w ∈ relations σ U θ) : w ∈ relations ρ U θ := by
  have hinj := map_injective_of_smooth U hU θ hθ ⊥ bot_le (isInvariant_bot U θ) i hi hσ
  rw [← mk_eq_zero]
  apply hinj
  rw [map_zero, map_mk, mk_eq_zero]
  exact hw

end Relations

section Abelian

variable {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- A group whose compact subsets lie in compact subgroups satisfies the
exhaustion condition for its top subgroup. -/
theorem isLimitOfCompactSubgroups_top {B : Type*} [Group B] [TopologicalSpace B]
    (h : ∀ C : Set B, IsCompact C → ∃ K : Subgroup B, IsCompact (K : Set B) ∧ C ⊆ K) :
    IsLimitOfCompactSubgroups (⊤ : Subgroup B) := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ := h _ (hC.image continuous_subtype_val)
  refine ⟨K.comap (⊤ : Subgroup B).subtype, ?_, ?_⟩
  · rw [Subtype.isCompact_iff]
    convert hK using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
  · intro c hc
    exact hCK ⟨c, hc, rfl⟩

/-- Each element has a positive power in a given open subgroup. -/
theorem exists_pow_mem_of_isOpen (hA : IsLimitOfCompactSubgroups (⊤ : Subgroup A))
    (H : Subgroup A) (hH : IsOpen (H : Set A)) (a : A) :
    ∃ N : ℕ, 0 < N ∧ a ^ N ∈ H := by
  obtain ⟨K, hK, haK⟩ := hA {⟨a, Subgroup.mem_top a⟩} isCompact_singleton
  let C : Subgroup A := K.map (⊤ : Subgroup A).subtype
  have hC : IsCompact (C : Set A) := by
    rw [Subgroup.coe_map]
    exact hK.image continuous_subtype_val
  have haC : a ∈ C := ⟨⟨a, Subgroup.mem_top a⟩, haK rfl, rfl⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hopen : IsOpen (H.subgroupOf C : Set C) := hH.preimage continuous_subtype_val
  have : Finite (C ⧸ H.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hopen
  exact ⟨H.relIndex C, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite,
    H.pow_relIndex_mem haC⟩

/-- A nonzero vector of a smooth representation of a commutative group exhausted
by compact subgroups survives in the coinvariants of some locally constant
character. -/
theorem exists_character_not_mem_relations
    (hA : IsLimitOfCompactSubgroups (⊤ : Subgroup A))
    (σ : Representation ℂ A E) (hσ : IsSmooth σ) {e : E} (he : e ≠ 0) :
    ∃ χ : A →* ℂˣ, IsLocallyConstant (fun a => (χ a : ℂ)) ∧
      e ∉ relations σ ⊤ (χ.comp (⊤ : Subgroup A).subtype) := by
  classical
  let e' : σ.asModule := σ.asModuleEquiv.symm e
  let ev : MonoidAlgebra ℂ A →ₗ[MonoidAlgebra ℂ A] σ.asModule :=
    LinearMap.toSpanSingleton _ _ e'
  have hev : ∀ x, ev x = x • e' := fun x => rfl
  let I : Ideal (MonoidAlgebra ℂ A) := LinearMap.ker ev
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MonoidAlgebra ℂ A) ∈ I := h ▸ Submodule.mem_top
    have h2 : (1 : MonoidAlgebra ℂ A) • e' = 0 := h1
    rw [one_smul] at h2
    exact he (σ.asModuleEquiv.symm.map_eq_zero_iff.mp h2)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  -- the stabilizer of `e`
  obtain ⟨H, hH⟩ := hσ e
  have hHfix : ∀ s ∈ H.toSubgroup, MonoidAlgebra.of ℂ A s • e' = e' := by
    intro s hs
    have hs' : σ s e = e := hH ⟨s, hs⟩
    rw [← Representation.asModuleEquiv_symm_map_rho, hs']
  have hHI : ∀ s ∈ H.toSubgroup, MonoidAlgebra.of ℂ A s - 1 ∈ m := by
    intro s hs
    apply hIm
    change ev _ = 0
    rw [hev, sub_smul, one_smul, hHfix s hs, sub_self]
  -- the residue field is `ℂ`
  have := hm
  let : Field (MonoidAlgebra ℂ A ⧸ m) := Ideal.Quotient.field m
  have hpow : ∀ a : A, ∃ N : ℕ, 0 < N ∧ MonoidAlgebra.of ℂ A a ^ N - 1 ∈ m := by
    intro a
    obtain ⟨N, hN, haN⟩ := exists_pow_mem_of_isOpen hA H.toSubgroup H.isOpen a
    refine ⟨N, hN, ?_⟩
    rw [← map_pow]
    exact hHI _ haN
  have hint : Algebra.IsIntegral ℂ (MonoidAlgebra ℂ A ⧸ m) := by
    constructor
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ m x
    induction f using MonoidAlgebra.induction_on with
    | of a =>
      obtain ⟨N, hN, hmem⟩ := hpow a
      refine IsIntegral.of_pow hN ?_
      have h1 : Ideal.Quotient.mkₐ ℂ m (MonoidAlgebra.of ℂ A a) ^ N = 1 := by
        rw [← map_pow, ← map_one (Ideal.Quotient.mkₐ ℂ m)]
        exact Ideal.Quotient.eq.mpr hmem
      rw [h1]
      exact isIntegral_one
    | add f g hf hg =>
      rw [map_add]
      exact hf.add hg
    | smul r f hf =>
      rw [map_smul]
      exact hf.smul r
  have hbij : Function.Bijective (algebraMap ℂ (MonoidAlgebra ℂ A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eqv : ℂ ≃ₐ[ℂ] (MonoidAlgebra ℂ A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hbij
  let φ : MonoidAlgebra ℂ A →ₐ[ℂ] ℂ :=
    (eqv.symm : (MonoidAlgebra ℂ A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have hφm : ∀ x ∈ m, φ x = 0 := by
    intro x hx
    have h0 : Ideal.Quotient.mkₐ ℂ m x = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    change eqv.symm (Ideal.Quotient.mkₐ ℂ m x) = 0
    rw [h0, map_zero]
  have hφker : ∀ x, φ x = 0 → x ∈ m := by
    intro x hx
    have h0 : Ideal.Quotient.mkₐ ℂ m x = 0 := by
      have h1 : eqv (φ x) = Ideal.Quotient.mkₐ ℂ m x := eqv.apply_symm_apply _
      rw [← h1, hx, map_zero]
    rw [Ideal.Quotient.mkₐ_eq_mk] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  -- the character
  let χ : A →* ℂˣ :=
    (φ.toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ A)).toHomUnits
  have hχ : ∀ a, (χ a : ℂ) = φ (MonoidAlgebra.of ℂ A a) := fun a => rfl
  have hχm : ∀ a, MonoidAlgebra.of ℂ A a - algebraMap ℂ _ (χ a : ℂ) ∈ m := by
    intro a
    apply hφker
    rw [map_sub, AlgHom.commutes, hχ, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hχH : ∀ s ∈ H.toSubgroup, χ s = 1 := by
    intro s hs
    apply Units.ext
    rw [hχ, Units.val_one]
    have h0 := hφm _ (hHI s hs)
    rwa [map_sub, map_one, sub_eq_zero] at h0
  have hloc : IsLocallyConstant (fun a => (χ a : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro a
    refine ⟨(fun b => a⁻¹ * b) ⁻¹' (H : Set A),
      H.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · change a⁻¹ * a ∈ H
      rw [inv_mul_cancel]
      exact H.one_mem
    · intro b hb
      have h1 : χ (a⁻¹ * b) = 1 := hχH _ hb
      have h2 : b = a * (a⁻¹ * b) := by group
      rw [h2, map_mul, h1, mul_one]
  refine ⟨χ, hloc, fun hrel => ?_⟩
  -- the cyclic subrepresentation generated by `e`
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' (LinearMap.range ev)
  have heW : e ∈ W.toSubmodule := ⟨1, one_smul _ _⟩
  let incl : W.toRepresentation.IntertwiningMap σ :=
    ⟨W.toSubmodule.subtype, fun _ => rfl⟩
  have hθloc : IsLocallyConstant
      (fun u : (⊤ : Subgroup A) => ((χ.comp (⊤ : Subgroup A).subtype) u : ℂ)) :=
    hloc.comp_continuous continuous_subtype_val
  have hrelW : (⟨e, heW⟩ : W.toSubmodule) ∈
      relations W.toRepresentation ⊤ (χ.comp (⊤ : Subgroup A).subtype) :=
    mem_relations_of_injective ⊤ hA _ hθloc incl Subtype.val_injective hσ hrel
  -- every relation of `W` lies in `m • e`
  let S : Submodule ℂ W.toSubmodule :=
    { carrier := {w | ∃ x ∈ m, x • e' = σ.asModuleEquiv.symm w.val}
      add_mem' := by
        rintro w w' ⟨x, hx, hxw⟩ ⟨x', hx', hxw'⟩
        refine ⟨x + x', m.add_mem hx hx', ?_⟩
        rw [add_smul, hxw, hxw']
        rfl
      zero_mem' := ⟨0, m.zero_mem, by rw [zero_smul]; rfl⟩
      smul_mem' := by
        rintro c w ⟨x, hx, hxw⟩
        refine ⟨algebraMap ℂ _ c * x, m.mul_mem_left _ hx, ?_⟩
        rw [mul_smul, hxw, ← Representation.asModuleEquiv_symm_map_smul]
        rfl }
  have hle : relations W.toRepresentation ⊤ (χ.comp (⊤ : Subgroup A).subtype) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨f, hf⟩ := w.property
    refine ⟨(MonoidAlgebra.of ℂ A u - algebraMap ℂ _ (χ u : ℂ)) * f,
      m.mul_mem_right _ (hχm u), ?_⟩
    change ev f = σ.asModuleEquiv.symm w.val at hf
    rw [hev] at hf
    rw [mul_smul, hf, sub_smul]
    change _ = σ.asModuleEquiv.symm (σ u w.val - (χ u : ℂ) • w.val)
    rw [map_sub, Representation.asModuleEquiv_symm_map_rho,
      Representation.asModuleEquiv_symm_map_smul]
  obtain ⟨x, hx, hxe⟩ := hle hrelW
  have h1 : (1 - x) ∈ I := by
    change ev (1 - x) = 0
    rw [hev, sub_smul, one_smul, hxe, sub_self]
  have h2 : (1 : MonoidAlgebra ℂ A) ∈ m := by
    have := m.add_mem (hIm h1) hx
    rwa [sub_add_cancel] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h2)

end Abelian

section Characters

open GeneralLinear.Mirabolic

variable {F : Type uF} [CommRing F] {n : ℕ}

/-- The sum of the adjacent upper entries `u_(i,i+1)` with `S i = true`. -/
def selectedSum (S : Fin n → Bool) :
    GeneralLinear.upperUnipotent (n + 1) F →* Multiplicative F where
  toFun u := ofAdd (∑ i : Fin n, if S i then u.val i.castSucc i.succ else 0)
  map_one' := by
    change (∑ i : Fin n, if S i then
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.castSucc i.succ else 0) = 0
    apply Finset.sum_eq_zero
    intro i _
    simp [ne_of_lt i.castSucc_lt_succ]
  map_mul' g h := by
    change (∑ i : Fin n, if S i then (g * h).val i.castSucc i.succ else 0) =
      (∑ i : Fin n, if S i then g.val i.castSucc i.succ else 0) +
        (∑ i : Fin n, if S i then h.val i.castSucc i.succ else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [GeneralLinear.UpperUnipotent.mul_adjacent_entry]
    split_ifs <;> simp

/-- The character `θ_S(u) = ψ(∑_{S i} u_(i,i+1))` of the actual upper-unipotent
subgroup of the mirabolic group `P_(n+1)`. -/
def simpleCharacter (ψ : Multiplicative F →* ℂˣ) (S : Fin n → Bool) :
    GeneralLinear.Mirabolic.upperUnipotent n F →* ℂˣ :=
  (ψ.comp (selectedSum S)).comp upperUnipotentEquiv.toMonoidHom

theorem simpleCharacter_apply (ψ : Multiplicative F →* ℂˣ) (S : Fin n → Bool)
    (u : GeneralLinear.Mirabolic.upperUnipotent n F) :
    simpleCharacter ψ S u =
      ψ (ofAdd (∑ i : Fin n, if S i then u.val.val.val i.castSucc i.succ else 0)) := rfl

/-- The character of the radical `V_(n+2)`: trivial for `b = false` and
`u(v) ↦ ψ(v_last)` for `b = true`. -/
def radicalCharacter (ψ : Multiplicative F →* ℂˣ) (n : ℕ) (b : Bool) :
    radical (n + 1) F →* ℂˣ :=
  ψ.comp (cond b (Derivative.Mirabolic.lastCoordinate n) 1)

theorem radicalCharacter_apply (ψ : Multiplicative F →* ℂˣ) (n : ℕ) (b : Bool)
    (u : radical (n + 1) F) :
    radicalCharacter ψ n b u =
      ψ (ofAdd (if b then radicalCoordinates u (Fin.last n) else 0)) := by
  cases b
  · simp [radicalCharacter]
  · rfl

/-- The radical characters are invariant under the smaller mirabolic group. -/
theorem radicalCharacter_isInvariant (ψ : Multiplicative F →* ℂˣ) (n : ℕ) (b : Bool) :
    IsInvariant (radical (n + 1) F) (successorSubgroup n F) successorSubgroup_le_normalizer
      (radicalCharacter ψ n b) := by
  intro m u
  obtain ⟨m, rfl⟩ := successorEquiv.surjective m
  obtain ⟨v, rfl⟩ := radicalEquiv.symm.surjective u
  have he : conjugate (radical (n + 1) F) (successorSubgroup n F)
      successorSubgroup_le_normalizer (successorEquiv m) (radicalEquiv.symm v) =
      radicalElement (m.val.val.mulVec v.toAdd) := by
    apply Subtype.ext
    change levi m.val * (radicalElement v.toAdd).val * (levi m.val)⁻¹ = _
    exact levi_conjugate_radicalElement m.val v.toAdd
  rw [he]
  simp only [radicalCharacter_apply, radicalEquiv_symm_apply, radicalCoordinates_element,
    Derivative.Mirabolic.mulVec_last]

/-- The upper-left block of an upper-unipotent element of `P_(n+2)`. -/
def topLeftMatrix (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.of fun i j => u.val.val.val i.castSucc j.castSucc

theorem topLeftMatrix_isUpperTriangular
    (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    (topLeftMatrix u).IsUpperTriangular := by
  intro i j hij
  exact GeneralLinear.UpperUnipotent.entry_eq_zero ⟨u.val.val, u.property⟩
    (Fin.castSucc_lt_castSucc_iff.mpr hij)

theorem topLeftMatrix_diag (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F)
    (i : Fin (n + 1)) : topLeftMatrix u i i = 1 :=
  GeneralLinear.UpperUnipotent.entry_diag ⟨u.val.val, u.property⟩ i.castSucc

theorem det_topLeftMatrix (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    (topLeftMatrix u).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (topLeftMatrix_isUpperTriangular u)]
  simp [topLeftMatrix_diag]

/-- The upper-left block as an invertible matrix. -/
def topLeftGL (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    Langlands.GeneralLinear (n + 1) F :=
  Matrix.nonsingInvUnit (topLeftMatrix u) (by rw [det_topLeftMatrix]; exact isUnit_one)

theorem topLeftGL_mem_upperUnipotent (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    topLeftGL u ∈ GeneralLinear.upperUnipotent (n + 1) F :=
  ⟨topLeftMatrix_isUpperTriangular u, topLeftMatrix_diag u⟩

/-- The upper-left block of `u ∈ U_(n+2)`, as an element of `U_(n+1) ⊆ P_(n+1)`. -/
def topLeft (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    GeneralLinear.Mirabolic.upperUnipotent n F :=
  ⟨⟨topLeftGL u, GeneralLinear.upperUnipotent_le_mirabolic (topLeftGL_mem_upperUnipotent u)⟩,
    topLeftGL_mem_upperUnipotent u⟩

@[simp] theorem topLeft_apply (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F)
    (i j : Fin (n + 1)) :
    (topLeft u).val.val.val i j = u.val.val.val i.castSucc j.castSucc := rfl

theorem successor_bottom (g : GeneralLinear.mirabolic n F) (j : Fin (n + 1 + 1)) :
    (successor g).val.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0 :=
  (successor g).property j

/-- The last column of `u ∈ U_(n+2)` above the corner entry. -/
def lastColumn (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) : Fin (n + 1) → F :=
  fun i => u.val.val.val i.castSucc (Fin.last (n + 1))

/-- Every `u ∈ U_(n+2)` is a radical element times the successor of its block. -/
theorem eq_radicalElement_mul_successor
    (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    (u : GeneralLinear.mirabolic (n + 1) F) =
      (radicalElement (lastColumn u)).val * successor (topLeft u).val := by
  have hbot : ∀ j, u.val.val.val (Fin.last (n + 1)) j =
      if j = Fin.last (n + 1) then 1 else 0 := u.val.property
  apply Subtype.ext
  apply Units.ext
  ext i j
  change u.val.val.val i j = ((radicalElement (lastColumn u)).val.val.val *
    (successor (topLeft u).val).val.val) i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, hbot, successor_bottom,
      radicalElement_first, radicalElement_last, radicalElement_bottom, lastColumn,
      Fin.castSucc_ne_last]

/-- The simple character of `S'` extended by `b` splits along the decomposition. -/
theorem simpleCharacter_snoc (ψ : Multiplicative F →* ℂˣ) (S' : Fin n → Bool) (b : Bool)
    (u : GeneralLinear.Mirabolic.upperUnipotent (n + 1) F) :
    simpleCharacter ψ (Fin.snoc S' b : Fin (n + 1) → Bool) u =
      radicalCharacter ψ n b (radicalElement (lastColumn u)) *
        simpleCharacter ψ S' (topLeft u) := by
  rw [simpleCharacter_apply, simpleCharacter_apply, radicalCharacter_apply,
    radicalCoordinates_element, ← map_mul, ← ofAdd_add, Fin.sum_univ_castSucc, add_comm]
  congr 3
  · simp only [Fin.snoc_last, Fin.succ_last, lastColumn]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.snoc_castSucc, topLeft_apply, Fin.succ_castSucc]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The action of `P_(n+1)` on the radical coinvariants of a representation of `P_(n+2)`. -/
def radicalQuotient (σ : Representation ℂ (GeneralLinear.mirabolic (n + 1) F) E)
    (ψ : Multiplicative F →* ℂˣ) (b : Bool) :
    Representation ℂ (GeneralLinear.mirabolic n F)
      (Coinvariants σ (radical (n + 1) F) (radicalCharacter ψ n b)) :=
  (action σ (radical (n + 1) F) (radicalCharacter ψ n b) (successorSubgroup n F)
    successorSubgroup_le_normalizer (radicalCharacter_isInvariant ψ n b)).comp
      successorEquiv.toMonoidHom

theorem radicalQuotient_mk (σ : Representation ℂ (GeneralLinear.mirabolic (n + 1) F) E)
    (ψ : Multiplicative F →* ℂˣ) (b : Bool) (m : GeneralLinear.mirabolic n F) (x : E) :
    radicalQuotient σ ψ b m (mk σ (radical (n + 1) F) (radicalCharacter ψ n b) x) =
      mk σ (radical (n + 1) F) (radicalCharacter ψ n b) (σ (successor m) x) := rfl

/-- The radical quotient map carries the relations of `θ_(S',b)` into those of `θ_S'`. -/
theorem mk_mem_relations (σ : Representation ℂ (GeneralLinear.mirabolic (n + 1) F) E)
    (ψ : Multiplicative F →* ℂˣ) (S' : Fin n → Bool) (b : Bool) {x : E}
    (hx : x ∈ relations σ (GeneralLinear.Mirabolic.upperUnipotent (n + 1) F)
      (simpleCharacter ψ (Fin.snoc S' b : Fin (n + 1) → Bool))) :
    mk σ (radical (n + 1) F) (radicalCharacter ψ n b) x ∈
      (relations (radicalQuotient σ ψ b) (GeneralLinear.Mirabolic.upperUnipotent n F)
        (simpleCharacter ψ S') :
          Submodule ℂ (Coinvariants σ (radical (n + 1) F) (radicalCharacter ψ n b))) := by
  have hle : relations σ (GeneralLinear.Mirabolic.upperUnipotent (n + 1) F)
      (simpleCharacter ψ (Fin.snoc S' b : Fin (n + 1) → Bool)) ≤
      (relations (radicalQuotient σ ψ b) (GeneralLinear.Mirabolic.upperUnipotent n F)
        (simpleCharacter ψ S')).comap (mk σ (radical (n + 1) F) (radicalCharacter ψ n b)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, y⟩, rfl⟩
    have hσu : σ u y = σ (radicalElement (lastColumn u)).val
        (σ (successor (topLeft u).val) y) := by
      rw [eq_radicalElement_mul_successor u, map_mul, Module.End.mul_apply]
    rw [SetLike.mem_coe, Submodule.mem_comap]
    dsimp only
    rw [map_sub, map_smul, hσu, mk_apply_subgroup, simpleCharacter_snoc, Units.val_mul,
      mul_smul, ← radicalQuotient_mk, ← smul_sub]
    exact Submodule.smul_mem _ _ (sub_mem_relations _ _ _ (topLeft u) _)
  exact hle hx

end Characters

section Padic

open GeneralLinear.Mirabolic Matrix

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The vector group `F^m` is exhausted by the compact open lattices `L_k^m`. -/
theorem isLimitOfCompactSubgroups_pi (m : ℕ) :
    letI := T.topology
    IsLimitOfCompactSubgroups (⊤ : Subgroup (Multiplicative (Fin m → F.Carrier))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply isLimitOfCompactSubgroups_top
  intro C hC
  let Λ : ℤ → Subgroup (Multiplicative (Fin m → F.Carrier)) := fun k =>
    { carrier := {v | ∀ i, toAdd v i ∈ T.additiveLattice k}
      mul_mem' := fun ha hb i => (T.additiveLattice k).add_mem (ha i) (hb i)
      one_mem' := fun _ => (T.additiveLattice k).zero_mem
      inv_mem' := fun ha i => (T.additiveLattice k).neg_mem (ha i) }
  have hmem : ∀ k v, v ∈ Λ k ↔ ∀ i, toAdd v i ∈ T.additiveLattice k := fun _ _ => Iff.rfl
  have hcompact : ∀ k, IsCompact (Λ k : Set (Multiplicative (Fin m → F.Carrier))) := by
    intro k
    have hc := (isCompact_univ_pi fun _ : Fin m => T.isCompact_additiveLattice k).image
      (continuous_ofAdd (X := Fin m → F.Carrier))
    convert hc using 1
    ext v
    constructor
    · intro hv
      exact ⟨toAdd v, fun i _ => hv i, rfl⟩
    · rintro ⟨w, hw, rfl⟩ i
      exact hw i (Set.mem_univ i)
  have hopen : ∀ k, IsOpen (Λ k : Set (Multiplicative (Fin m → F.Carrier))) := by
    intro k
    have ho := (isOpen_set_pi Set.finite_univ fun (i : Fin m) _ =>
      T.isOpen_additiveLattice k).preimage (continuous_toAdd (X := Fin m → F.Carrier))
    convert ho using 1
    ext v
    simp only [SetLike.mem_coe, hmem, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have hcover : C ⊆ ⋃ k, (Λ k : Set (Multiplicative (Fin m → F.Carrier))) := by
    intro v _
    have hk : ∀ i, ∃ k : ℤ, toAdd v i ∈ T.additiveLattice k :=
      fun i => exists_mem_additiveLattice T (toAdd v i)
    choose k hk using hk
    obtain ⟨M, hM⟩ := Finite.exists_le k
    exact Set.mem_iUnion.mpr ⟨M, fun i => T.additiveLattice_mono (hM i) (hk i)⟩
  have hmono : Monotone fun k => (Λ k : Set (Multiplicative (Fin m → F.Carrier))) :=
    fun j k hjk v hv i => T.additiveLattice_mono hjk (hv i)
  obtain ⟨k, hk⟩ := hC.elim_directed_cover _ hopen hcover hmono.directed_le
  exact ⟨Λ k, hcompact k, hk⟩

/-- A nonzero smooth representation of the actual mirabolic group `P_(n+1)` has
nonzero coinvariants for some simple character `θ_S` of its upper-unipotent
subgroup. Here `ψ` generates the locally constant characters of `F`. -/
theorem exists_relations_ne_top (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hgen : ∀ χ : Multiplicative F.Carrier →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) →
      ∃ a : F.Carrier, ∀ x : F.Carrier, χ (ofAdd x) = ψ (ofAdd (a * x)))
    (n : ℕ) :
    ∀ {E : Type uE} [AddCommGroup E] [Module ℂ E]
      (σ : Representation ℂ (GeneralLinear.mirabolic n F.Carrier) E),
      (letI := T.topology; IsSmooth σ) → ∀ {e : E}, e ≠ 0 →
      ∃ S : Fin n → Bool,
        relations σ (GeneralLinear.Mirabolic.upperUnipotent n F.Carrier)
          (simpleCharacter ψ S) ≠ ⊤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  induction n with
  | zero =>
    intro E _ _ σ _ e he
    refine ⟨fun i => i.elim0, fun h => he ?_⟩
    have hmem : e ∈ relations σ (GeneralLinear.Mirabolic.upperUnipotent 0 F.Carrier)
        (simpleCharacter ψ fun i => i.elim0) := h ▸ Submodule.mem_top
    rw [relations_eq_bot_of_subsingleton] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  | succ n ih =>
    intro E _ _ σ hσ e he
    let R := radical (n + 1) F.Carrier
    -- the radical as the vector group `F^(n+1)`
    let φ : Multiplicative (Fin (n + 1) → F.Carrier) →* GeneralLinear.mirabolic (n + 1) F.Carrier :=
      R.subtype.comp radicalEquiv.symm.toMonoidHom
    have hφ : Continuous φ :=
      continuous_subtype_val.comp (radicalContinuousEquiv (n := n + 1) (F := F.Carrier)).symm.continuous
    have hσR : IsSmooth (σ.comp φ) := isSmooth_comp φ hφ hσ
    obtain ⟨χ, hχloc, hχe⟩ := exists_character_not_mem_relations
      (isLimitOfCompactSubgroups_pi T (n + 1)) (σ.comp φ) hσR he
    obtain ⟨a, ha⟩ := exists_dotProduct_eq T ψ hgen χ (hχloc.comp_continuous continuous_ofAdd)
    -- move `χ` to a radical character by the Levi action
    obtain ⟨g, b, hgb⟩ : ∃ (g : Langlands.GeneralLinear (n + 1) F.Carrier) (b : Bool),
        ∀ v : Fin (n + 1) → F.Carrier,
          χ (ofAdd (g.val *ᵥ v)) = ψ (ofAdd (if b then v (Fin.last n) else 0)) := by
      by_cases ha0 : a = 0
      · refine ⟨1, false, fun v => ?_⟩
        rw [ha, ha0, zero_dotProduct]
        rfl
      · obtain ⟨g, hg⟩ := exists_dotProduct_mulVec_eq_last a ha0
        exact ⟨g, true, fun v => by rw [ha, hg]; rfl⟩
    let θR : R →* ℂˣ := χ.comp radicalEquiv.toMonoidHom
    have hθR : ∀ w : Fin (n + 1) → F.Carrier, θR (radicalElement w) = χ (ofAdd w) := by
      intro w
      change χ (radicalEquiv (radicalEquiv.symm (ofAdd w))) = χ (ofAdd w)
      rw [MulEquiv.apply_symm_apply]
    have hrelR : relations (σ.comp φ) ⊤ (χ.comp (⊤ : Subgroup _).subtype) =
        relations σ R θR := by
      refine relations_eq_of_surjective σ R θR (σ.comp φ) ⊤ _
        (fun u => radicalEquiv.symm u.val) ?_ (fun _ => rfl) ?_
      · intro u
        exact ⟨⟨radicalEquiv u, Subgroup.mem_top _⟩, radicalEquiv.symm_apply_apply u⟩
      · intro u
        change χ u.val = χ (radicalEquiv (radicalEquiv.symm u.val))
        rw [MulEquiv.apply_symm_apply]
    rw [hrelR] at hχe
    have hU : ∀ u : R, levi g * u * (levi g)⁻¹ ∈ R := fun u =>
      (Subgroup.mem_normalizer_iff.mp (leviSubgroup_le_normalizer ⟨g, rfl⟩) u).mp u.property
    have hθ : ∀ u : R, θR ⟨levi g * u * (levi g)⁻¹, hU u⟩ = radicalCharacter ψ n b u := by
      intro u
      obtain ⟨v, rfl⟩ := radicalEquiv.symm.surjective u
      have hconj : (⟨levi g * (radicalEquiv.symm v).val * (levi g)⁻¹, hU _⟩ : R) =
          radicalElement (g.val *ᵥ v.toAdd) :=
        Subtype.ext (levi_conjugate_radicalElement g v.toAdd)
      rw [hconj, hθR, hgb, radicalCharacter_apply, radicalEquiv_symm_apply,
        radicalCoordinates_element]
    let θb := radicalCharacter ψ n b
    have he' : σ (levi g)⁻¹ e ∉ relations σ R θb := by
      intro hrel
      apply hχe
      have h := apply_mem_relations σ R θb θR (levi g) hU hθ hrel
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at h
    -- pass to the radical quotient, a smooth representation of `P_(n+1)`
    have hτ : IsSmooth (radicalQuotient σ ψ b) :=
      isSmooth_comp successorEquiv.toMonoidHom
        (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous
        (isSmooth_action σ R θb (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
          (radicalCharacter_isInvariant ψ n b) hσ)
    have hne : mk σ R θb (σ (levi g)⁻¹ e) ≠ 0 := by
      rw [Ne, mk_eq_zero]
      exact he'
    obtain ⟨S', hS'⟩ := ih (radicalQuotient σ ψ b) hτ hne
    refine ⟨Fin.snoc S' b, fun htop => hS' ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := mk_surjective σ R θb q
    exact mk_mem_relations σ ψ S' b (htop ▸ Submodule.mem_top)

end Padic

end Langlands.Whittaker.MirabolicFiniteLength
