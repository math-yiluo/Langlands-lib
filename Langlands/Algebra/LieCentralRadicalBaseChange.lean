import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Central radicals under restriction and extension of scalars -/

noncomputable section

open LieAlgebra TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.LieCentralRadical

section Map

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

/-- The derived series of an ideal is carried onto the derived series of its image by a
surjective Lie algebra homomorphism. -/
theorem map_derivedSeriesOfIdeal (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f)
    (I : LieIdeal R L) (k : ℕ) :
    (derivedSeriesOfIdeal R L k I).map f = derivedSeriesOfIdeal R L' k (I.map f) := by
  induction k with
  | zero => simp only [derivedSeriesOfIdeal_zero]
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, LieIdeal.map_bracket_eq f hf, ih]

/-- If a surjective Lie algebra homomorphism onto a Lie algebra with trivial radical has central
kernel, the radical of the source is central. -/
theorem radical_le_center_of_surjective [IsNoetherian R L] (π : L →ₗ⁅R⁆ L')
    (hπ : Function.Surjective π) [HasTrivialRadical R L'] (hker : π.ker ≤ center R L) :
    radical R L ≤ center R L := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R (radical R L)
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  have hJ : IsSolvable ((radical R L).map π) := by
    apply IsSolvable.mk (R := R) (k := k)
    rw [LieIdeal.derivedSeries_eq_bot_iff, ← map_derivedSeriesOfIdeal π hπ, hk, LieIdeal.map_eq_bot_iff]
    exact bot_le
  have h0 : (radical R L).map π = ⊥ := HasTrivialRadical.eq_bot_of_isSolvable _
  exact (LieIdeal.map_eq_bot_iff.1 h0).trans hker

/-- Having central radical is invariant under isomorphisms of Lie algebras. -/
theorem hasCentralRadical_of_lieEquiv [IsNoetherian R L] [IsNoetherian R L'] [HasCentralRadical R L]
    (e : L ≃ₗ⁅R⁆ L') : HasCentralRadical R L' := by
  apply hasCentralRadical_of_radical_le
  let f : L' →ₗ⁅R⁆ L := e.symm.toLieHom
  have hf : Function.Surjective f := e.symm.surjective
  obtain ⟨k, hk⟩ := IsSolvable.solvable R (radical R L')
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  have hJ : IsSolvable ((radical R L').map f) := by
    apply IsSolvable.mk (R := R) (k := k)
    rw [LieIdeal.derivedSeries_eq_bot_iff, ← map_derivedSeriesOfIdeal f hf, hk,
      LieIdeal.map_eq_bot_iff]
    exact bot_le
  have hle : (radical R L').map f ≤ radical R L := (LieIdeal.solvable_iff_le_radical R L _).mp hJ
  intro x hx
  have hfx : f x ∈ center R L := by
    rw [← HasCentralRadical.radical_eq_center]
    exact hle (LieIdeal.mem_map hx)
  rw [LieModule.mem_maxTrivSubmodule] at hfx
  show x ∈ LieModule.maxTrivSubmodule R L' L'
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  have h1 : f ⁅y, x⁆ = 0 := by
    rw [LieHom.map_lie]
    exact hfx (f y)
  have h2 : ⁅y, x⁆ = e (f ⁅y, x⁆) := (e.apply_symm_apply _).symm
  rw [h2, h1, map_zero]

end Map

section Quotient

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The quotient map of a Lie algebra by an ideal, as a Lie algebra homomorphism. -/
def quotientHom (I : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ I :=
  { (LieSubmodule.Quotient.mk' I : L →ₗ[R] L ⧸ I) with
    map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket I x y }

@[simp] theorem quotientHom_apply (I : LieIdeal R L) (x : L) :
    quotientHom I x = LieSubmodule.Quotient.mk x := rfl

theorem quotientHom_surjective (I : LieIdeal R L) : Function.Surjective (quotientHom I) :=
  LieSubmodule.Quotient.surjective_mk' I

theorem quotientHom_ker (I : LieIdeal R L) : (quotientHom I).ker = I := by
  ext x
  rw [LieHom.mem_ker]
  exact LieSubmodule.Quotient.mk_eq_zero' (N := I)

/-- A Lie algebra whose radical is its centre has a quotient by the centre with trivial
radical. -/
theorem hasTrivialRadical_quotient_center [IsNoetherian R L] [HasCentralRadical R L] :
    HasTrivialRadical R (L ⧸ center R L) := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  intro J hJ
  let π := quotientHom (center R L)
  have hπ : Function.Surjective π := quotientHom_surjective _
  obtain ⟨k, hk⟩ := IsSolvable.solvable R J
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  let J' := J.comap π
  have hJ'map : J'.map π = J := by
    rw [LieIdeal.map_comap_eq (π.isIdealMorphism_of_surjective hπ),
      π.idealRange_eq_top_of_surjective hπ, top_inf_eq]
  have hle : derivedSeriesOfIdeal R L k J' ≤ center R L := by
    rw [← quotientHom_ker (center R L), ← LieIdeal.map_eq_bot_iff, map_derivedSeriesOfIdeal π hπ,
      hJ'map, hk]
  have hsolv : IsSolvable J' := by
    apply IsSolvable.mk (R := R) (k := k + 1)
    rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeriesOfIdeal_succ, eq_bot_iff]
    refine (LieSubmodule.mono_lie hle hle).trans ?_
    rw [LieSubmodule.lie_le_iff]
    intro x hx y _
    rw [LieSubmodule.mem_bot, ← lie_skew, hx y, neg_zero]
  have hJ' : J' ≤ center R L := by
    rw [← HasCentralRadical.radical_eq_center (R := R) (L := L)]
    exact (LieIdeal.solvable_iff_le_radical R L J').mp hsolv
  rw [← hJ'map, LieIdeal.map_eq_bot_iff, quotientHom_ker]
  exact hJ'

end Quotient

section RestrictScalars

variable {k F S : Type*} [Field k] [Field F] [Algebra k F] [LieRing S] [LieAlgebra F S]

/-- Trivial radical is inherited by restriction of scalars: the scalar span of an abelian ideal
over the smaller field is an abelian ideal over the larger one. -/
theorem hasTrivialRadical_restrictScalars [HasTrivialRadical F S] :
    HasTrivialRadical k (RestrictScalars k F S) := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  let e := RestrictScalars.addEquiv k F S
  let J : LieIdeal F S :=
    { Submodule.span F (e '' (I : Set (RestrictScalars k F S))) with
      lie_mem := by
        intro x m hm
        change m ∈ Submodule.span F _ at hm
        change ⁅x, m⁆ ∈ Submodule.span F _
        induction hm using Submodule.span_induction with
        | mem m hm =>
          obtain ⟨m, hm, rfl⟩ := hm
          exact Submodule.subset_span ⟨⁅e.symm x, m⁆, I.lie_mem hm, rfl⟩
        | zero => simp
        | add a b _ _ ha hb => rw [lie_add]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [lie_smul]; exact Submodule.smul_mem _ c ha }
  have hcomm : ∀ a ∈ (I : Set (RestrictScalars k F S)), ∀ b ∈ (I : Set (RestrictScalars k F S)),
      ⁅e a, e b⁆ = 0 := by
    intro a ha b hb
    have h := (hI.trivial ⟨a, ha⟩ ⟨b, hb⟩)
    exact congrArg (fun z : I => e (z : RestrictScalars k F S)) h
  have hJab : IsLieAbelian J := by
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    change ⁅x, y⁆ = 0
    change x ∈ Submodule.span F _ at hx
    change y ∈ Submodule.span F _ at hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact hcomm a ha b hb
      | zero => simp
      | add a b _ _ ha hb => rw [lie_add, ha, hb, add_zero]
      | smul c a _ ha => rw [lie_smul, ha, smul_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [add_lie, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_lie, ha, smul_zero]
  have hJ0 : J = ⊥ := (hasTrivialRadical_iff_no_abelian_ideals F S).mp inferInstance J hJab
  rw [eq_bot_iff]
  intro a ha
  have haJ : e a ∈ J := Submodule.subset_span ⟨a, ha, rfl⟩
  rw [hJ0, LieSubmodule.mem_bot] at haJ
  rw [LieSubmodule.mem_bot]
  exact e.injective (haJ.trans e.map_zero.symm)

end RestrictScalars

section BaseChange

variable {k K S : Type*} [Field k] [CharZero k] [Field K] [Algebra k K] [LieRing S]
  [LieAlgebra k S] [FiniteDimensional k S]

omit [CharZero k] [FiniteDimensional k S] in
/-- The Gram matrix of a base-changed bilinear form in the base-changed basis is the image of
the original Gram matrix. -/
theorem toMatrix_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k S)
    (B : LinearMap.BilinForm k S) :
    LinearMap.BilinForm.toMatrix (Algebra.TensorProduct.basis K b) (B.baseChange K) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap k K) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply,
    Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul, mul_one,
    Algebra.smul_def]

omit [CharZero k] in
/-- A nondegenerate Killing form stays nondegenerate after extension of scalars. -/
theorem isKilling_baseChange [IsKilling k S] : IsKilling K (K ⊗[k] S) := by
  let b := Module.finBasis k S
  have hdet : (LinearMap.BilinForm.toMatrix b (killingForm k S)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (IsKilling.killingForm_nondegenerate k S)
  have hK : (killingForm K (K ⊗[k] S)).Nondegenerate := by
    rw [killingForm, LieModule.traceForm_baseChange,
      LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Algebra.TensorProduct.basis K b),
      toMatrix_baseChange, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (algebraMap k K).injective).mpr hdet
  refine ⟨?_⟩
  rw [eq_bot_iff]
  intro x hx
  rw [LieIdeal.mem_killingCompl] at hx
  rw [LieSubmodule.mem_bot]
  apply hK.1 x
  intro y
  rw [LieModule.traceForm_comm]
  exact hx y (LieSubmodule.mem_top y)

/-- Trivial radical is preserved by extension of scalars in characteristic zero. -/
theorem hasTrivialRadical_baseChange [HasTrivialRadical k S] :
    HasTrivialRadical K (K ⊗[k] S) := by
  have : IsKilling K (K ⊗[k] S) := isKilling_baseChange
  infer_instance

end BaseChange

section Hom

variable {k K : Type*} [CommRing k] [CommRing K] [Algebra k K]

/-- The extension of scalars of a Lie algebra homomorphism. -/
def baseChangeHom {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra k L₁] [LieRing L₂] [LieAlgebra k L₂]
    (f : L₁ →ₗ⁅k⁆ L₂) : K ⊗[k] L₁ →ₗ⁅K⁆ K ⊗[k] L₂ :=
  { (f : L₁ →ₗ[k] L₂).baseChange K with
    map_lie' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [add_lie, map_add, hx, hx']
      | tmul a l =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => simp only [lie_add, map_add, hy, hy']
        | tmul c m =>
          simp only [ExtendScalars.bracket_tmul, LinearMap.baseChange_tmul, LieHom.coe_toLinearMap,
            LieHom.map_lie] }

@[simp] theorem baseChangeHom_tmul {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra k L₁] [LieRing L₂]
    [LieAlgebra k L₂] (f : L₁ →ₗ⁅k⁆ L₂) (a : K) (x : L₁) :
    baseChangeHom (K := K) f (a ⊗ₜ x) = a ⊗ₜ f x := rfl

end Hom

section Assembly

variable {k F K L : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [FiniteDimensional k F]
  [Field K] [Algebra k K] [LieRing L] [LieAlgebra F L] [FiniteDimensional F L]

/-- The quotient by the centre, as a homomorphism of Lie algebras over the smaller field. -/
def restrictedQuotientHom :
    RestrictScalars k F L →ₗ⁅k⁆ RestrictScalars k F (L ⧸ center F L) where
  toFun x := quotientHom (center F L) x
  map_add' x y := (quotientHom (center F L)).map_add x y
  map_smul' c x := (quotientHom (center F L)).map_smul (algebraMap k F c) x
  map_lie' := fun {x y} => (quotientHom (center F L)).map_lie x y

/-- The inclusion of the centre, over the smaller field. -/
def restrictedCenterInclusion :
    RestrictScalars k F (center F L) →ₗ[k] RestrictScalars k F L where
  toFun z := ((RestrictScalars.addEquiv k F (center F L) z : center F L) : L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Reductivity under restriction and extension of scalars.** If a finite-dimensional Lie
algebra over a finite extension `F` of a field `k` of characteristic zero has central radical,
then so has its scalar extension to any field extension `K` of `k`, after restricting scalars to
`k`. -/
theorem hasCentralRadical_baseChange_restrictScalars [HasCentralRadical F L] :
    HasCentralRadical K (K ⊗[k] RestrictScalars k F L) := by
  let S := L ⧸ center F L
  have hS : HasTrivialRadical F S := hasTrivialRadical_quotient_center
  have hSk : HasTrivialRadical k (RestrictScalars k F S) := hasTrivialRadical_restrictScalars
  have : FiniteDimensional k (RestrictScalars k F S) := by
    let := RestrictScalars.moduleOrig k F S
    have : Module.Finite F (RestrictScalars k F S) := inferInstanceAs (Module.Finite F S)
    exact Module.Finite.trans F _
  have : FiniteDimensional k (RestrictScalars k F L) := by
    let := RestrictScalars.moduleOrig k F L
    have : Module.Finite F (RestrictScalars k F L) := inferInstanceAs (Module.Finite F L)
    exact Module.Finite.trans F _
  have hSK : HasTrivialRadical K (K ⊗[k] RestrictScalars k F S) :=
    hasTrivialRadical_baseChange
  let π₀ : RestrictScalars k F L →ₗ⁅k⁆ RestrictScalars k F S := restrictedQuotientHom
  let π : K ⊗[k] RestrictScalars k F L →ₗ⁅K⁆ K ⊗[k] RestrictScalars k F S := baseChangeHom π₀
  have hπ₀ : Function.Surjective π₀ := quotientHom_surjective (center F L)
  have hπ : Function.Surjective π :=
    LinearMap.lTensor_surjective K hπ₀
  let ι : RestrictScalars k F (center F L) →ₗ[k] RestrictScalars k F L :=
    restrictedCenterInclusion
  have hexact : Function.Exact ι (π₀ : RestrictScalars k F L →ₗ[k] RestrictScalars k F S) := by
    intro y
    constructor
    · intro hy
      have hy' : quotientHom (center F L) y = 0 := hy
      rw [← LieHom.mem_ker, quotientHom_ker] at hy'
      exact ⟨⟨y, hy'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      change quotientHom (center F L)
        ((RestrictScalars.addEquiv k F (center F L) z : center F L) : L) = 0
      rw [← LieHom.mem_ker, quotientHom_ker]
      exact (RestrictScalars.addEquiv k F (center F L) z).2
  have hexactK := lTensor_exact K hexact hπ₀
  apply hasCentralRadical_of_radical_le
  refine radical_le_center_of_surjective π hπ ?_
  intro x hx
  rw [LieHom.mem_ker] at hx
  obtain ⟨w, rfl⟩ := (hexactK x).mp hx
  clear hx
  intro y
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => rw [map_add, lie_add, hw, hw', add_zero]
  | tmul a z =>
    rw [LinearMap.lTensor_tmul]
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [add_lie, hy, hy', add_zero]
    | tmul c l =>
      rw [ExtendScalars.bracket_tmul]
      have hz : ⁅l, ι z⁆ = 0 :=
        (RestrictScalars.addEquiv k F (center F L) z).2 (RestrictScalars.addEquiv k F L l)
      rw [hz, TensorProduct.tmul_zero]

end Assembly

end Langlands.Algebra.LieCentralRadical
