import Langlands.Global.AdelicGLCompactConjugateCounting
import Langlands.Global.AdelicSplitCenterSubgroupHaar
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # Polynomial positive-rational subgroup mass on compact adelic conjugates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

private abbrev GLG (F : Type u) [Field F] (n : ℕ) :=
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance glIsAffine (F : Type u) [Field F] (n : ℕ) : IsAffine (GLG F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance glSmooth (F : Type u) [Field F] (n : ℕ) : Smooth (GLG F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

private def principalEquiv (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] :
    RationalGroupPoints F G ≃ rationalNormOneSubgroup F G :=
  Equiv.ofBijective (fun q => ⟨rationalNormOne F G q, ⟨q, rfl⟩⟩) ⟨by
    intro a b h
    exact rationalNormOne_injective F G (congrArg Subtype.val h), by
    rintro ⟨_, q, rfl⟩
    exact ⟨q, rfl⟩⟩

private theorem principalEquiv_symm_rational (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (q : rationalNormOneSubgroup F G) :
    AdelicGroupPoints.rational F G ((principalEquiv F G).symm q) = q.val.val :=
  congrArg (fun p : rationalNormOneSubgroup F G => p.val.val)
    ((principalEquiv F G).apply_symm_apply q)

/-- The canonical positive-rational subgroup measure of a compact conjugate grows at most
polynomially in the archimedean Hilbert height, with the finite adelic coordinate fixed. -/
def AdelicGLPositiveRationalConjugateGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLG F n)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    (S : Set (AdelicGroupPoints F (GLG F n))), IsCompact S →
    ∀ b : FiniteAdelicGL F n, ∃ B : ℝ, 0 ≤ B ∧ ∀ a : InfiniteAdelicGL F n,
      let x := (GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.pair F n a b)
      (positiveRationalSubgroupHaarMeasure F (GLG F n) T i hi I e hc).real
        (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) ≤
          B * infiniteAdelicHilbertNorm F n a ^ (2 * Module.finrank ℝ (ArchimedeanMatrix F n))

set_option maxHeartbeats 800000 in
/-- Centrality keeps the positive coordinate in one fixed compact set. The norm-one
coordinate is controlled by the polynomial count of rational matrices. -/
theorem adelicGLPositiveRationalConjugateGrowth :
    AdelicGLPositiveRationalConjugateGrowthStatement.{u} := by
  classical
  intro F _ _ n T i hi _ I _ e hc S hS b
  let G := GLG F n
  let E := GeneralLinearGroupPoints.adelicHomeomorph F n
  let A := intrinsicSubgroup F T
  let Γ := rationalNormOneSubgroup F G
  let π₀ := positiveFactor F G T i hi I e
  let π₁ := normOneProjection F G T i hi I e hc
  let D := positiveRationalDecomposition F G T i hi I e hc
  let μ₀ := normalizedPositiveHaarMeasure F G T i hi I e hc
  let μ₁ : Measure Γ := Measure.count
  let μH := positiveRationalSubgroupHaarMeasure F G T i hi I e hc
  let C₀ : Set A := π₀ '' S
  have hC₀ : IsCompact C₀ := hS.image π₀.continuous
  let θ (s : AdelicGroupPoints F G) : AdelicGL F n := E (π₁ s).val
  have hθ : Continuous θ := E.continuous.comp (continuous_subtype_val.comp π₁.continuous)
  let C₁ := θ '' S
  have hC₁ : IsCompact C₁ := hS.image hθ
  have hpos (x s : AdelicGroupPoints F G) : π₀ (x * s * x⁻¹) = π₀ s := by
    simp only [map_mul, map_inv]
    rw [mul_comm (π₀ x) (π₀ s), mul_assoc, mul_inv_cancel, mul_one]
  have hθconj (x s : AdelicGroupPoints F G) : θ (x * s * x⁻¹) = E x * θ s * (E x)⁻¹ := by
    change E ((normOneFactor F G T i hi I e (x * s * x⁻¹)).val) =
      E x * E ((normOneFactor F G T i hi I e s).val) * (E x)⁻¹
    simp only [normOneFactor_val]
    change E ((positivePointMap F G T i (π₀ (x * s * x⁻¹)))⁻¹ * (x * s * x⁻¹)) =
      E x * E ((positivePointMap F G T i (π₀ s))⁻¹ * s) * (E x)⁻¹
    rw [hpos]
    let z := positivePointMap F G T i (π₀ s)
    have hz : Commute z x := positivePointMap_commute F G T i hc (π₀ s) x
    have he : z⁻¹ * (x * s * x⁻¹) = x * (z⁻¹ * s) * x⁻¹ := by
      calc
        _ = (z⁻¹ * x) * s * x⁻¹ := by simp only [mul_assoc]
        _ = (x * z⁻¹) * s * x⁻¹ := by rw [hz.inv_left.eq]
        _ = _ := by simp only [mul_assoc]
    calc
      _ = E (x * (z⁻¹ * s) * x⁻¹) := congrArg (fun t : AdelicGroupPoints F G => E t) he
      _ = _ := by simp only [map_mul, map_inv, z]
  let j : Γ ≃ RationalGL F n := (principalEquiv F G).symm.trans
    (GeneralLinearGroupPoints.rationalEquiv F n).toEquiv
  have hj (q : Γ) : E q.val.val = AdelicGL.rational F n (j q) := by
    change E q.val.val = AdelicGL.rational F n
      (GeneralLinearGroupPoints.rationalEquiv F n ((principalEquiv F G).symm q))
    rw [← GeneralLinearGroupPoints.adelicHomeomorph_rational, principalEquiv_symm_rational]
  obtain ⟨M, hM, hcount⟩ := AdelicGL.adelicGLCompactConjugateCounting F n C₁ hC₁ b
  let : μ₀.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  have hμ₀ : μ₀ C₀ ≠ ∞ := hC₀.measure_lt_top.ne
  refine ⟨(μ₀ C₀).toReal * M, mul_nonneg ENNReal.toReal_nonneg hM, ?_⟩
  intro a
  let y := AdelicGL.pair F n a b
  let x := E.symm y
  have hEx : E x = y := E.apply_symm_apply y
  let P := (AdelicGL.rational F n) ⁻¹' ((fun s => y * s * y⁻¹) '' C₁)
  let Q : Set Γ := j ⁻¹' P
  obtain ⟨hP, hPb⟩ := hcount a
  change P.Finite at hP
  have hQ : Q.Finite := hP.preimage j.injective.injOn
  have hQP : Q.ncard ≤ P.ncard := Set.ncard_le_ncard_of_injOn j
    (fun _ hq => hq) j.injective.injOn hP
  let U : Set (positiveRationalSubgroup F G T i) :=
    Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)
  have hsub : D ⁻¹' U ⊆ C₀ ×ˢ Q := by
    intro p hp
    obtain ⟨s, hs, hp⟩ := hp
    have hpD : (D p).val = positivePointMap F G T i p.1 * p.2.val.val := rfl
    have hp₀ : π₀ (D p).val = p.1 := positiveFactor_mul_normOne F G T i hi I e p.1 p.2.val
    have hp₁ : π₁ (D p).val = p.2.val := by
      rw [hpD, map_mul, normOneProjection_positivePointMap, normOneProjection_normOne, one_mul]
    refine ⟨⟨s, hs, ?_⟩, ⟨θ s, ⟨s, hs, rfl⟩, ?_⟩⟩
    · exact (hpos x s).symm.trans ((congrArg π₀ hp).trans hp₀)
    · calc
        y * θ s * y⁻¹ = θ (x * s * x⁻¹) := by rw [hθconj, hEx]
        _ = θ (D p).val := congrArg θ hp
        _ = E p.2.val.val := congrArg (fun q : normOneSubgroup F G => E q.val) hp₁
        _ = _ := hj p.2
  have hpres : MeasurePreserving D.toHomeomorph.toMeasurableEquiv (μ₀.prod μ₁) μH :=
    measurePreserving_positiveRationalDecomposition F G T i hi I e hc
  have hm : μH U = (μ₀.prod μ₁) (D ⁻¹' U) := (hpres.measure_preimage_equiv U).symm
  have hcnt : μ₁ Q = Q.ncard := by
    rw [Set.ncard_eq_toFinset_card Q hQ]
    exact Measure.count_apply_finite Q hQ
  have hmul : μ₀ C₀ * μ₁ Q ≠ ∞ :=
    ENNReal.mul_ne_top hμ₀ (by rw [hcnt]; exact ENNReal.natCast_ne_top _)
  have hle : μH U ≤ μ₀ C₀ * μ₁ Q := by
    rw [hm, ← Measure.prod_prod]
    exact measure_mono hsub
  change (μH U).toReal ≤ _
  calc
    _ ≤ (μ₀ C₀ * μ₁ Q).toReal := ENNReal.toReal_mono hmul hle
    _ = (μ₀ C₀).toReal * (Q.ncard : ℝ) := by rw [ENNReal.toReal_mul, hcnt, ENNReal.toReal_natCast]
    _ ≤ (μ₀ C₀).toReal * (P.ncard : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hQP) ENNReal.toReal_nonneg
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hPb ENNReal.toReal_nonneg

end Langlands.Global.PositiveRealTorus
