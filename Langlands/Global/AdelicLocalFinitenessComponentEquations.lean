import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicStandardSlabEstimate
import Langlands.Global.AdelicHarishChandraDecomposition

/-! # Difference equations for constant terms and Harish-Chandra components

A difference equation `∑_k D_k φ(b^k g) = 0` for left translation by the image `b` of a point of
the positive split component of `P`, satisfied by the constant term `C_P f` of a continuous
`G(F)`-invariant function, is satisfied by every constant term `C_Q f` with `Q ≤ P`, and hence
by the Harish-Chandra components of `f` whose index lies below `P`. The equations of a monic
polynomial are residual equations, and with a nonzero constant coefficient also for `b⁻¹`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.StandardConstantTerm

open AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The lower coefficients `D_0, …, D_{m-1}` of a polynomial `D` of degree `m`. -/
def lowerCoefficients (D : Polynomial ℂ) : Fin D.natDegree → ℂ := fun q => D.coeff q

/-- The lower coefficients `D_m / D_0, …, D_1 / D_0` of the normalized reversed polynomial
`D_0⁻¹ x^m D(x⁻¹)` of a polynomial `D` of degree `m`. -/
def reversedLowerCoefficients (D : Polynomial ℂ) : Fin D.natDegree → ℂ :=
  fun q => D.coeff (D.natDegree - q) / D.coeff 0

/-- A solution of the difference equation of a monic polynomial has zero residual. -/
theorem residualFun_eq_zero_of_monic {b : AdelicGroupPoints F G} {D : Polynomial ℂ}
    (hD : D.Monic) {φ : AdelicGroupPoints F G → ℂ} (h : IsTranslationPolynomialSolution b D φ) :
    residualFun F G b (lowerCoefficients D) φ = 0 := by
  funext g
  have hg := h g
  rw [Finset.sum_range_succ, hD.coeff_natDegree, one_mul] at hg
  rw [residualFun, Pi.zero_apply, ← hg, add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun k => D.coeff k * φ (b ^ k * g)) D.natDegree)

/-- A solution of the difference equation of a polynomial `D` with nonzero constant coefficient
has zero residual for `b⁻¹` and the reversed normalized polynomial, of degree `m = natDegree D`
with lower coefficients `D_{m-q} / D_0`. -/
theorem residualFun_inv_eq_zero {b : AdelicGroupPoints F G} {D : Polynomial ℂ}
    (h0 : D.coeff 0 ≠ 0) {φ : AdelicGroupPoints F G → ℂ}
    (h : IsTranslationPolynomialSolution b D φ) :
    residualFun F G b⁻¹ (reversedLowerCoefficients D) φ = 0 := by
  funext g
  set m := D.natDegree
  have hg := h (b⁻¹ ^ m * g)
  have hpow : ∀ k ∈ Finset.range (m + 1), b ^ k * (b⁻¹ ^ m * g) = b⁻¹ ^ (m - k) * g := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [← mul_assoc]
    congr 1
    conv_lhs => rw [show m = k + (m - k) by omega, pow_add, ← mul_assoc, inv_pow, mul_inv_cancel,
      one_mul]
  rw [Finset.sum_congr rfl fun k hk => by rw [hpow k hk]] at hg
  rw [← Finset.sum_range_reflect] at hg
  have hrefl : ∀ q ∈ Finset.range (m + 1), m + 1 - 1 - q = m - q := fun q _ => by omega
  have hsub : ∀ q ∈ Finset.range (m + 1), m - (m - q) = q := fun q hq => by
    have := Finset.mem_range.mp hq; omega
  rw [Finset.sum_congr rfl fun q hq => by rw [hrefl q hq, hsub q hq]] at hg
  rw [Finset.sum_range_succ, Nat.sub_self] at hg
  rw [residualFun, Pi.zero_apply]
  simp only [reversedLowerCoefficients]
  have hsum : ∑ k : Fin m, D.coeff (m - k) / D.coeff 0 * φ (b⁻¹ ^ (k : ℕ) * g) =
      (D.coeff 0)⁻¹ * ∑ q ∈ Finset.range m, D.coeff (m - q) * φ (b⁻¹ ^ q * g) := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun q => (D.coeff 0)⁻¹ *
      (D.coeff (m - q) * φ (b⁻¹ ^ q * g))) m]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_inv_mul]
    ring
  rw [hsum]
  have hsum' : ∑ q ∈ Finset.range m, D.coeff (m - q) * φ (b⁻¹ ^ q * g) =
      -(D.coeff 0 * φ (b⁻¹ ^ m * g)) := by linear_combination hg
  rw [hsum']
  field_simp
  ring

end Langlands.Global.StandardConstantTerm

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open Langlands.Global.HarishChandraDecomposition
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

/-- **Difference equations descend to smaller constant terms.** Let `a` be a point of the
positive split component of `P` with image `b ∈ G(𝔸)` and `Q ≤ P`. If the constant term
`C_P f` of a continuous `G(F)`-invariant `f` satisfies `∑_k D_k C_P f(b^k g) = 0` for all `g`,
then so does `C_Q f`. -/
theorem isTranslationPolynomialSolution_constantTerm_of_le {Q P : Idx} (hQP : Q ≤ P)
    (a : 𝓕.positiveSplitComponent P) (D : Polynomial ℂ) (f : ContinuousRationalFunctions F G)
    (h : IsTranslationPolynomialSolution (map F (𝓕.P P) G (𝓕.p P) a) D
      (𝓕.constantTerm P (evaluate F G f))) :
    IsTranslationPolynomialSolution (map F (𝓕.P P) G (𝓕.p P) a) D
      (𝓕.constantTerm Q (evaluate F G f)) := by
  intro g
  rw [← 𝓕.constantTerm_constantTerm_of_le hQP f]
  set φ := 𝓕.constantTerm P (evaluate F G f) with hφdef
  set b := map F (𝓕.P P) G (𝓕.p P) a with hbdef
  have hφ : 𝓕.IsRadicalInvariant P φ := 𝓕.isRadicalInvariant_constantTerm P f
  have hi : 𝓕.HasIntegrableConstantTerm Q φ := 𝓕.hasIntegrableConstantTerm_constantTerm_of_le hQP f
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G rad(Q) : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G rad(Q)
  let Fg (x : AdelicGroupPoints F G) (q : AdelicSubgroupPoints.RationalQuotient F G rad(Q)) :=
    φ (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) : AdelicGroupPoints F G) * x)
  have hF : ∀ x, Integrable (Fg x) m := hi
  have hmap : ∀ k : ℕ, map F (𝓕.P P) G (𝓕.p P) ((a ^ k : 𝓕.positiveSplitComponent P) :
      AdelicGroupPoints F (𝓕.P P)) = b ^ k := fun k => by
    rw [Subgroup.coe_pow, map_pow]
  have hswap : ∀ (k : ℕ) (q : AdelicSubgroupPoints.RationalQuotient F G rad(Q)),
      φ (b ^ k * (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
        AdelicGroupPoints F G) * g)) = Fg (b ^ k * g) q := by
    intro k q
    have := IsRadicalInvariant.unnormalizedAction_radical_mul 𝓕 hQP hφ (a ^ k) (Quotient.out q) g
    simp only [unnormalizedAction, hmap] at this
    exact this
  have hterm : ∀ k : ℕ, 𝓕.constantTerm Q φ (b ^ k * g) =
      ∫ q, φ (b ^ k * (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
        AdelicGroupPoints F G) * g)) ∂m := by
    intro k
    simp_rw [hswap k]
    rfl
  simp_rw [hterm]
  have hsum : ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k *
      ∫ q, φ (b ^ k * (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
        AdelicGroupPoints F G) * g)) ∂m =
      ∫ q, ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (b ^ k *
        (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
          AdelicGroupPoints F G) * g)) ∂m := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    · intro k _
      simp_rw [hswap k]
      exact (hF (b ^ k * g)).const_mul _
  have hzero : ∀ q : AdelicSubgroupPoints.RationalQuotient F G rad(Q),
      ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * φ (b ^ k *
        (((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G rad(Q)) :
          AdelicGroupPoints F G) * g)) = 0 := fun q => h _
  rw [hsum]
  simp_rw [hzero, integral_zero]

/-- The difference equations of `C_P f` hold for every Harish-Chandra component of `f` whose
index lies below `P`. -/
theorem isTranslationPolynomialSolution_hcComponent {P : Idx} (a : 𝓕.positiveSplitComponent P)
    (D : Polynomial ℂ) (f : ContinuousRationalFunctions F G)
    (h : IsTranslationPolynomialSolution (map F (𝓕.P P) G (𝓕.p P) a) D
      (𝓕.constantTerm P (evaluate F G f)))
    (S : Finset (characterLattice 𝓕.T)) (hS : 𝓕.finsetIndex S ≤ P) :
    IsTranslationPolynomialSolution (map F (𝓕.P P) G (𝓕.p P) a) D
      (𝓕.hcComponent S (evaluate F G f)) := by
  intro g
  set b := map F (𝓕.P P) G (𝓕.p P) a with hb
  have hT : ∀ S' ∈ S.powerset, ∑ k ∈ Finset.range (D.natDegree + 1),
      D.coeff k * 𝓕.constantTerm (𝓕.finsetIndex S') (evaluate F G f) (b ^ k * g) = 0 := by
    intro S' hS'
    have hsub : (𝓕.finsetIndex S').1 ⊆ (𝓕.finsetIndex S).1 := fun x hx =>
      ⟨Finset.mem_powerset.mp hS' hx.1, hx.2⟩
    have hle : 𝓕.finsetIndex S' ≤ P :=
      le_trans (show 𝓕.finsetIndex S' ≤ 𝓕.finsetIndex S from hsub) hS
    exact 𝓕.isTranslationPolynomialSolution_constantTerm_of_le hle a D f h g
  have hexp : ∀ k, 𝓕.hcComponent S (evaluate F G f) (b ^ k * g) =
      ∑ S' ∈ S.powerset, (-1 : ℂ) ^ (S \ S').card *
        𝓕.constantTerm (𝓕.finsetIndex S') (evaluate F G f) (b ^ k * g) := by
    intro k
    unfold hcComponent alternatingSum
    rw [Finset.sum_apply]
    rfl
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun S' hS' => ?_
  have hfac : ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * ((-1 : ℂ) ^ (S \ S').card *
      𝓕.constantTerm (𝓕.finsetIndex S') (evaluate F G f) (b ^ k * g)) =
      (-1 : ℂ) ^ (S \ S').card * ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k *
        𝓕.constantTerm (𝓕.finsetIndex S') (evaluate F G f) (b ^ k * g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  rw [hfac, hT S' hS', mul_zero]

end Langlands.Global.StandardParabolicFamily
