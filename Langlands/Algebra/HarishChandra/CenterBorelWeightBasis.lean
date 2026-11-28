import Langlands.Algebra.HarishChandra.CenterBorelInjectivityStatement
import Langlands.Algebra.CartanCenterProjectionInjectivity
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Joint weight bases for the center projection at a split Cartan -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule Finsupp MvPolynomial UniversalEnveloping

attribute [local instance] Classical.decEq

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {H : LieSubalgebra ℂ L}

/-- Bracketing weight vectors adds their weights. -/
theorem bracket_mem_weightSpace_add {χ ψ : H → ℂ} {x y : L}
    (hx : x ∈ weightSpace L χ) (hy : y ∈ weightSpace L ψ) :
    ⁅x, y⁆ ∈ weightSpace L (χ + ψ) := by
  rw [mem_weightSpace] at hx hy ⊢
  intro h
  change ⁅(h : L), ⁅x, y⁆⁆ = (χ h + ψ h) • ⁅x, y⁆
  rw [leibniz_lie, show ⁅(h : L), x⁆ = χ h • x from hx h,
    show ⁅(h : L), y⁆ = ψ h • y from hy h, smul_lie, lie_smul, add_smul]

/-- A basis of joint weight vectors sorted by decreasing real value of the weight at `X`.
The basis contains at most one vector of each nonzero weight. -/
theorem IsSplitCartan.exists_ordered_weight_basis [FiniteDimensional ℂ L]
    (hCartan : IsSplitCartan H) (X : H) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) ℂ L) (χ : Fin r → H → ℂ),
      (∀ i, b i ∈ weightSpace L (χ i)) ∧
      (∀ i j, χ i ≠ 0 → χ i = χ j → i = j) ∧
      Antitone (fun i => (χ i X).re) := by
  classical
  let _ : IsLieAbelian H := hCartan.isLieAbelian
  let W (ψ : H → ℂ) : Submodule ℂ L := weightSpace L ψ
  have hIndep : iSupIndep W :=
    (LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace ℂ H L)).mono
      (fun ψ => weightSpace_le_genWeightSpace L ψ)
  have hSum : (⨆ ψ, W ψ) = ⊤ := by
    rw [← LieSubmodule.iSup_toSubmodule, hCartan.iSup_weightSpace_eq_top]
    rfl
  have hInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hIndep hSum
  let B (ψ : H → ℂ) := Module.finBasis ℂ (W ψ)
  let c := hInternal.collectedBasis B
  let I := Σ ψ : H → ℂ, Fin (Module.finrank ℂ (W ψ))
  let _ : Finite I := Module.Finite.finite_basis c
  let _ : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let val (i : Fin (Fintype.card I)) := -((e i).1 X).re
  let f : Fin (Fintype.card I) ≃ I := (Tuple.sort val).trans e
  let b := c.reindex f.symm
  let χ (i : Fin (Fintype.card I)) := (f i).1
  have hb (i : Fin (Fintype.card I)) : b i = c (f i) := by simp [b]
  have hm (i : Fin (Fintype.card I)) : b i ∈ weightSpace L (χ i) := by
    rw [hb]
    exact hInternal.collectedBasis_mem B (f i)
  refine ⟨Fintype.card I, b, χ, hm, ?_, ?_⟩
  · intro i j hχ hEq
    have hNonzero : weightSpace L (χ i) ≠ ⊥ := by
      intro h
      exact b.ne_zero i (by simpa [h] using hm i)
    have hDim := hCartan.finrank_weightSpace (χ i) hχ hNonzero
    apply f.injective
    change (f i).1 = (f j).1 at hEq
    change Module.finrank ℂ (W (f i).1) = 1 at hDim
    generalize hi : f i = a at hEq hDim ⊢
    generalize hj : f j = d at hEq ⊢
    rcases a with ⟨α, a⟩
    rcases d with ⟨β, d⟩
    change α = β at hEq
    subst β
    congr 1
    change Module.finrank ℂ (W α) = 1 at hDim
    exact Fin.ext (by omega)
  · intro i j hij
    exact neg_le_neg_iff.mp (Tuple.monotone_sort val hij)

section Basis

variable {r : ℕ} (b : Module.Basis (Fin r) ℂ L) (χ : Fin r → H → ℂ)
  (hb : ∀ i, b i ∈ weightSpace L (χ i))

include hb in
/-- Nonzero coordinates of a weight vector have the same weight. -/
theorem weight_eq_of_basis_repr_ne_zero {ψ : H → ℂ} {u : L} (hu : u ∈ weightSpace L ψ)
    {i : Fin r} (hi : b.repr u i ≠ 0) : χ i = ψ := by
  funext Y
  let adY : L →ₗ[ℂ] L := LieAlgebra.ad ℂ L (Y : L)
  have hCoord : (b.coord i).comp adY = (χ i Y) • b.coord i := by
    apply b.ext
    intro j
    change b.coord i ⁅(Y : L), b j⁆ = (χ i Y) • b.coord i (b j)
    rw [show ⁅(Y : L), b j⁆ = χ j Y • b j from (mem_weightSpace _ _).mp (hb j) Y,
      map_smul]
    by_cases h : i = j
    · subst j
      rfl
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, h]
  have h := LinearMap.congr_fun hCoord u
  change b.repr (⁅(Y : L), u⁆) i = χ i Y * b.repr u i at h
  rw [show ⁅(Y : L), u⁆ = ψ Y • u from (mem_weightSpace _ _).mp hu Y,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ hi h).symm

include hb in
theorem positiveRootSubmodule_eq_span (X : H) :
    positiveRootSubmodule H X = Submodule.span ℂ (b '' {i | 0 < (χ i X).re}) := by
  apply le_antisymm
  · unfold positiveRootSubmodule
    refine iSup_le fun ψ => iSup_le fun hψ u hu => ?_
    rw [← b.linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    have h := weight_eq_of_basis_repr_ne_zero b χ hb hu (Finsupp.mem_support_iff.mp hi)
    exact Submodule.subset_span ⟨i, by change 0 < (χ i X).re; rwa [h], rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.mem_iSup_of_mem (χ i) (Submodule.mem_iSup_of_mem hi (hb i))

private theorem linearPolynomial_injective : Function.Injective (pbwLinearPolynomial b) := by
  classical
  intro x y heq
  apply b.repr.injective
  ext i
  have hCoeff : (lcoeff ℂ (single i 1)).comp (pbwLinearPolynomial b) = b.coord i := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, lcoeff_apply, pbwLinearPolynomial_basis, Module.Basis.coord_apply,
      Module.Basis.repr_self, coeff_X]
    by_cases h : i = j
    · subst j
      simp
    · rw [ite_eq_right (by simpa [single_eq_single_iff] using Ne.symm h)]
      simp [h]
  have hxy := congrArg (fun p : MvPolynomial (Fin r) ℂ => p.coeff (single i 1)) heq
  exact (LinearMap.congr_fun hCoeff x).symm.trans
    (hxy.trans (LinearMap.congr_fun hCoeff y))

include hb in
private theorem restrict_linearPolynomial_weight {ψ : H → ℂ} {u : L}
    (hu : u ∈ weightSpace L ψ) :
    weightedHomogeneousComponent (fun i => if χ i = 0 then 0 else 1) 0
        (pbwLinearPolynomial b u) =
      if ψ = 0 then pbwLinearPolynomial b u else 0 := by
  classical
  let w (i : Fin r) : ℕ := if χ i = 0 then 0 else 1
  change weightedHomogeneousComponent w 0 (pbwLinearPolynomial b u) =
    if ψ = 0 then pbwLinearPolynomial b u else 0
  simp only [pbwLinearPolynomial, Module.Basis.constr_apply_fintype, map_sum, map_smul]
  by_cases hψ : ψ = 0
  · rw [ite_eq_left hψ]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : b.repr u i = 0
    · simp [h]
    · have hw : w i = 0 := by simp [w, weight_eq_of_basis_repr_ne_zero b χ hb hu h, hψ]
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same
        (hw ▸ isWeightedHomogeneous_X (R := ℂ) w i)]
  · rw [ite_eq_right hψ]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : b.repr u i = 0
    · simp [h]
    · have hw : w i = 1 := by simp [w, weight_eq_of_basis_repr_ne_zero b χ hb hu h, hψ]
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne _
        (hw ▸ isWeightedHomogeneous_X (R := ℂ) w i) zero_ne_one, smul_zero]

include hb in
/-- The restriction of the root derivations to the Cartan coordinates is diagonal, with
nonzero entries given by the brackets of opposite root directions. -/
theorem exists_transverse_weight_bracket (hCartan : IsSplitCartan H)
    (hLine : ∀ i j, χ i ≠ 0 → χ i = χ j → i = j) (i : Fin r) (hi : χ i ≠ 0) :
    ∃ x : L,
      weightedHomogeneousComponent (fun j => if χ j = 0 then 0 else 1) 0
        (pbwLinearPolynomial b ⁅x, b i⁆) ≠ 0 ∧
      ∀ j, χ j ≠ 0 → j ≠ i →
        weightedHomogeneousComponent (fun j => if χ j = 0 then 0 else 1) 0
          (pbwLinearPolynomial b ⁅x, b j⁆) = 0 := by
  classical
  have hSpace : weightSpace L (χ i) ≠ ⊥ := by
    intro h
    exact b.ne_zero i (by simpa [h] using hb i)
  obtain ⟨e, he, f, hf, h, hBracket, hValue⟩ := hCartan.exists_sl2 (χ i) hi hSpace
  have hAtZero : χ i 0 = 0 := by
    have hEquation : ⁅(0 : L), b i⁆ = χ i 0 • b i :=
      (mem_weightSpace _ _).mp (hb i) 0
    exact (smul_eq_zero.mp (by simpa using hEquation.symm)).resolve_right (b.ne_zero i)
  have hNonzero : (h : L) ≠ 0 := by
    intro hzero
    have hzero' : h = 0 := Subtype.ext hzero
    rw [hzero', hAtZero] at hValue
    exact two_ne_zero hValue.symm
  have he0 : e ≠ 0 := by
    intro hzero
    exact hNonzero (by simpa [hzero] using hBracket.symm)
  let e' : weightSpace L (χ i) := ⟨e, he⟩
  have he' : e' ≠ 0 := fun heq => he0 (congrArg Subtype.val heq)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (hCartan.finrank_weightSpace (χ i) hi hSpace) he' ⟨b i, hb i⟩
  have hc' : c • e = b i := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    intro hz
    exact b.ne_zero i (by simpa [hz] using hc'.symm)
  refine ⟨f, ?_, ?_⟩
  · have hfBracket : ⁅f, b i⁆ ≠ 0 := by
      rw [← hc', lie_smul, ← lie_skew f e, hBracket]
      exact smul_ne_zero hc0 (neg_ne_zero.mpr hNonzero)
    have hZero : ⁅f, b i⁆ ∈ weightSpace L (0 : H → ℂ) := by
      simpa using bracket_mem_weightSpace_add hf (hb i)
    rw [restrict_linearPolynomial_weight b χ hb hZero, ite_eq_left rfl]
    intro hZeroPolynomial
    apply hfBracket (linearPolynomial_injective b (hZeroPolynomial.trans (map_zero _).symm))
  · intro j _ hj
    have hNe : -χ i + χ j ≠ 0 := by
      intro hzero
      have hEq : χ i = χ j := by
        rw [neg_add_eq_sub, sub_eq_zero] at hzero
        exact hzero.symm
      exact hj (hLine i j hi hEq).symm
    rw [restrict_linearPolynomial_weight b χ hb (bracket_mem_weightSpace_add hf (hb j)),
      ite_eq_right hNe]

end Basis

end Langlands.Algebra.HarishChandra
