import Langlands.Algebra.ParabolicCenterProjectionCoordinates
import Langlands.Algebra.LieGelfandCentralElements
import Langlands.Algebra.MvPolynomialLeadingFinite
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Leading forms of the Harish-Chandra map -/

noncomputable section

universe v w

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection.GradingData

open LieAlgebra MvPolynomial Langlands.Algebra.LieWeightProjection Langlands.Archimedean.Kostant
  Langlands.Archimedean.VermaPBW Langlands.Algebra.LieEnvelopingSymbol
  Langlands.Algebra.MvPolynomialLeadingFinite

attribute [local instance 100] LieRing.ofAssociativeRing

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] {H : g} (D : GradingData g H)

/-- Restriction of polynomials in all the basis letters to the letters of grading zero: the
other variables are sent to zero. -/
def zeroRestrict : MvPolynomial D.ι ℂ →ₐ[ℂ] MvPolynomial D.zeroIndex ℂ :=
  killCompl (Subtype.val_injective : Function.Injective (Subtype.val : D.zeroIndex → D.ι))

theorem coeff_zeroRestrict (s : MvPolynomial D.ι ℂ) (α : D.zeroIndex →₀ ℕ) :
    (D.zeroRestrict s).coeff α =
      s.coeff (α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0)) := by
  classical
  let e := Function.Embedding.subtype fun c : D.ι => D.φ c = 0
  induction s using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial β r =>
    by_cases hβ : ∀ i ∈ β.support, D.φ i = 0
    · let β' : D.zeroIndex →₀ ℕ := β.comapDomain Subtype.val Subtype.val_injective.injOn
      have hβ' : β'.embDomain e = β := by
        ext i
        by_cases hi : D.φ i = 0
        · exact Finsupp.embDomain_apply_self e β' ⟨i, hi⟩
        · rw [Finsupp.embDomain_of_notMem_range _ _ _ (by rintro ⟨a, rfl⟩; exact hi a.2)]
          by_contra hne
          exact hi (hβ i (Finsupp.mem_support_iff.mpr (Ne.symm hne)))
      have hmd : Finsupp.mapDomain Subtype.val β' = β := by
        rw [← hβ', Finsupp.embDomain_eq_mapDomain]
        rfl
      have hmon : monomial β r = rename Subtype.val (monomial β' r) := by
        rw [rename_monomial, hmd]
      have hlhs : D.zeroRestrict (monomial β r) = monomial β' r := by
        rw [hmon, zeroRestrict, killCompl_rename_app]
      rw [hlhs, coeff_monomial, coeff_monomial, ← hβ']
      by_cases h : β' = α
      · rw [ite_eq_left h, ite_eq_left (by rw [h])]
      · rw [ite_eq_right h, ite_eq_right ((Finsupp.embDomain_injective e).ne h)]
    · push Not at hβ
      obtain ⟨i, hi, hφ⟩ := hβ
      have h0 : D.zeroRestrict (monomial β r) = 0 := by
        rw [zeroRestrict, killCompl, aeval_monomial, Finsupp.prod]
        rw [Finset.prod_eq_zero hi]
        · rw [mul_zero]
        · rw [dite_eq_right (by rintro ⟨a, rfl⟩; exact hφ a.2),
            zero_pow (Finsupp.mem_support_iff.mp hi)]
      rw [h0, coeff_monomial, ite_eq_right]
      · simp
      rintro rfl
      apply hφ
      have hi' := Finsupp.support_embDomain e α ▸ hi
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hi'
      exact a.2

theorem degree_embDomain (α : D.zeroIndex →₀ ℕ) :
    (α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0)).degree = α.degree := by
  change ∑ i ∈ (α.embDomain _).support, (α.embDomain _) i = ∑ i ∈ α.support, α i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  exact Finset.sum_congr rfl fun a _ => Finsupp.embDomain_apply_self _ _ _

theorem zeroRestrict_X_val (a : D.zeroIndex) : D.zeroRestrict (X a.1) = X a := by
  have h : (X a.1 : MvPolynomial D.ι ℂ) = rename Subtype.val (X a) := (rename_X _ _).symm
  rw [h, zeroRestrict, killCompl_rename_app]

theorem zeroRestrict_X_of_ne {i : D.ι} (hi : D.φ i ≠ 0) : D.zeroRestrict (X i) = 0 := by
  ext α
  rw [coeff_zeroRestrict, coeff_X, ite_eq_right]
  · simp
  intro h
  apply hi
  have hmem : i ∈ (α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0)).support := by
    rw [← h]; simp
  rw [Finsupp.support_embDomain] at hmem
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hmem
  exact a.2

/-- The restriction of the linear symbol of `v` keeps its coordinates of grading zero. -/
theorem zeroRestrict_ξ (v : g) :
    D.zeroRestrict (ξ D.basis v) = ∑ a : D.zeroIndex, D.basis.repr v a • X a := by
  classical
  rw [ξ_apply, map_sum]
  simp only [map_smul]
  rw [← sum_subtype_eq_sum_of_zero (fun c => D.φ c = 0) _ (fun c hc => by
    rw [D.zeroRestrict_X_of_ne hc, smul_zero])]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [D.zeroRestrict_X_val]

/-- The linear forms `ℓ q`, restrictions of the linear symbols of `T(wt q)`. -/
def ell (q : D.ι) : MvPolynomial D.zeroIndex ℂ := D.zeroRestrict (ξ D.basis (D.dualOf (D.wt q)))

theorem zeroRestrict_ξ_dual_of_ne {i : D.ι} (hi : D.φ i ≠ 0) :
    D.zeroRestrict (ξ D.basis (D.dual i)) = 0 := by
  rw [zeroRestrict_ξ]
  refine Finset.sum_eq_zero fun a _ => ?_
  have h : D.basis.repr (D.dual i) a = 0 := by
    by_contra hne
    have := D.φ_eq_neg_of_repr_dual_ne_zero hne
    rw [a.2] at this
    exact hi (by linarith)
  rw [h, zero_smul]

theorem adCoeff_of_φ_eq_zero {i : D.ι} (hi : D.φ i = 0) (p q : D.ι) :
    LieGelfandCentral.adCoeff D.basis (D.basis i) p q =
      if p = q then D.wt q ⟨D.basis i, D.mem_cartan_of_φ_eq_zero hi⟩ else 0 := by
  unfold LieGelfandCentral.adCoeff
  have h : ⁅D.basis i, D.basis q⁆ =
      D.wt q ⟨D.basis i, D.mem_cartan_of_φ_eq_zero hi⟩ • D.basis q :=
    D.lie_basis q ⟨D.basis i, D.mem_cartan_of_φ_eq_zero hi⟩
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [ite_eq_right (Ne.symm hpq), ite_eq_right hpq, mul_zero]

/-- On the letters of grading zero, the symbol matrix of the Gelfand matrix is diagonal with
entries `ℓ q`. -/
theorem zeroRestrict_symbolMatrix :
    (LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis).map D.zeroRestrict =
      Matrix.diagonal D.ell := by
  classical
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.map_apply, LieGelfandCentral.symbolMatrix, Matrix.of_apply, map_sum,
    map_smul, Matrix.diagonal_apply]
  change ∑ x, LieGelfandCentral.adCoeff D.basis (D.basis x) p q •
      D.zeroRestrict (ξ D.basis (D.dual x)) = _
  rw [← sum_subtype_eq_sum_of_zero (fun i => D.φ i = 0)
    (fun i => LieGelfandCentral.adCoeff D.basis (D.basis i) p q •
      D.zeroRestrict (ξ D.basis (D.dual i))) (fun i hi => by
    rw [D.zeroRestrict_ξ_dual_of_ne hi, smul_zero])]
  by_cases hpq : p = q
  · subst hpq
    rw [ite_eq_left rfl, ell, dualOf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [D.adCoeff_of_φ_eq_zero c.2, ite_eq_left rfl, map_smul, map_smul]
  · rw [ite_eq_right hpq]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [D.adCoeff_of_φ_eq_zero c.2, ite_eq_right hpq, zero_smul]

/-- The leading form of the Gelfand element `C_n`: the power sum `∑ ℓ q ^ n`. -/
theorem zeroRestrict_symbol_gelfand {bs : List D.ι} (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs)
    (n : ℕ) :
    D.zeroRestrict (symbol D.basis hbs hall n
      (LieGelfandCentral.gelfand D.form D.nondegenerate D.basis n)) = ∑ q, D.ell q ^ n := by
  rw [LieGelfandCentral.symbol_gelfand, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := congrArg (fun M => M q q)
    (Matrix.map_pow (LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis)
      D.zeroRestrict.toRingHom n)
  simp only [Matrix.map_apply] at h
  change D.zeroRestrict ((LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis ^ n) q q) = _
  rw [show D.zeroRestrict ((LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis ^ n) q q)
    = D.zeroRestrict.toRingHom ((LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis ^ n)
      q q) from rfl, h]
  change ((LieGelfandCentral.symbolMatrix D.form D.nondegenerate D.basis).map D.zeroRestrict ^ n)
    q q = _
  rw [D.zeroRestrict_symbolMatrix, Matrix.diagonal_pow, Matrix.diagonal_apply_eq]
  rfl

/-- The leading form of a central Lie element: its linear symbol restricted to grading zero. -/
theorem zeroRestrict_symbol_ι {bs : List D.ι} (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (c : g) :
    D.zeroRestrict (symbol D.basis hbs hall 1 (UniversalEnvelopingAlgebra.ι ℂ c)) =
      D.zeroRestrict (ξ D.basis c) := by
  have h := symbol_word_of_length_eq D.basis hbs hall [c]
  simp only [UniversalEnveloping.word, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, List.length_cons, List.length_nil] at h
  rw [h]

variable {m : Type w} [LieRing m] [LieAlgebra ℂ m] {j : m →ₗ⁅ℂ⁆ g}
  (hj : Function.Injective j) (hrange : ∀ X : g, X ∈ Set.range j ↔ ⁅H, X⁆ = 0)

local notation "Ug" => UniversalEnvelopingAlgebra ℂ g
local notation "Um" => UniversalEnvelopingAlgebra ℂ m

theorem hcMap_degLE (P : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um)
    (hP : ∀ z : Subalgebra.center ℂ Ug, (z : Ug) -
      UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j) (P z : Um) ∈
        positiveRightIdeal H)
    (z : Subalgebra.center ℂ Ug) {n : ℕ} (hz : z.val ∈ UniversalEnveloping.degreeFiltration ℂ g n) :
    DegLE n (D.hcMap hj hrange P z) := by
  intro α hα
  rw [MvPolynomial.mem_support_iff, D.coeff_hcMap hj hrange P hP] at hα
  by_contra hlt
  push Not at hlt
  apply hα
  have h := coeff_pbwPoly D.basis (weightOrderedIndices_nodup D.φ) (mem_weightOrderedIndices D.φ)
    z.val (α.embDomain (Function.Embedding.subtype fun c => D.φ c = 0))
  change _ = (weightOrderedPBWBasis D.basis D.φ).repr _ _ at h
  rw [← h]
  exact coeff_pbwPoly_eq_zero_of_mem D.basis (weightOrderedIndices_nodup D.φ)
    (mem_weightOrderedIndices D.φ) hz (by rw [degree_embDomain]; exact hlt)

theorem homogeneousComponent_hcMap (P : Subalgebra.center ℂ Ug →ₐ[ℂ] Subalgebra.center ℂ Um)
    (hP : ∀ z : Subalgebra.center ℂ Ug, (z : Ug) -
      UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j) (P z : Um) ∈
        positiveRightIdeal H)
    (z : Subalgebra.center ℂ Ug) (n : ℕ) :
    homogeneousComponent n (D.hcMap hj hrange P z) = D.zeroRestrict
      (symbol D.basis (weightOrderedIndices_nodup D.φ) (mem_weightOrderedIndices D.φ) n z.val) := by
  ext α
  rw [coeff_homogeneousComponent, coeff_zeroRestrict, coeff_symbol, D.coeff_hcMap hj hrange P hP,
    degree_embDomain]
  rfl

theorem degLT_sub_homogeneousComponent {x : MvPolynomial D.zeroIndex ℂ} {n : ℕ}
    (hx : DegLE n x) : DegLT n (x - homogeneousComponent n x) := by
  intro α hα
  rw [MvPolynomial.mem_support_iff] at hα
  simp only [MvPolynomial.coeff_sub, coeff_homogeneousComponent] at hα
  by_cases h : α.degree = n
  · rw [ite_eq_left h, sub_self] at hα
    exact absurd rfl hα
  · rw [ite_eq_right h, sub_zero] at hα
    exact lt_of_le_of_ne (hx α (MvPolynomial.mem_support_iff.mpr hα)) h

end Langlands.Algebra.ParabolicCenterProjection.GradingData
