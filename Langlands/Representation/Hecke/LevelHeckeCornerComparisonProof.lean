import Langlands.Representation.Hecke.LevelHeckeCornerComparisonStatement
import Langlands.Representation.Hecke.LevelHeckeCornerLinear
import Langlands.Representation.Hecke.ActionProjection

/-! # Comparison of the level Hecke algebra and the Haar-measure corner -/

noncomputable section

open MeasureTheory Langlands.Shimura.LevelHecke

namespace Langlands.Hecke

universe u v

namespace LevelCorner

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- A normalized coset indicator convolves a left-invariant test by translation. -/
theorem cosetTest_mul (q : G ⧸ K.toSubgroup) (f : HeckeAlgebra μ)
    (hf : ∀ k : K, ∀ x, f ((k : G) * x) = f x) :
    cosetTest μ K hK q * f =
      (HeckeAlgebra.toTestFunction μ).symm
        (TestFunction.leftTranslate q.out (HeckeAlgebra.toTestFunction μ f)) := by
  change TestFunction.convolution μ
    (TestFunction.leftTranslate q.out
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK)))
    (HeckeAlgebra.toTestFunction μ f) =
      TestFunction.leftTranslate q.out (HeckeAlgebra.toTestFunction μ f)
  rw [TestFunction.convolution_leftTranslate]
  change TestFunction.leftTranslate q.out
    (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK * f)) = _
  rw [HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant μ K hK f hf]

/-- The normalized linear map preserves coset convolution. -/
theorem toCorner_mul (a b : LevelHeckeAlgebra ℂ K.toSubgroup) :
    toCorner μ K hK (a * b) = toCorner μ K hK a * toCorner μ K hK b := by
  classical
  apply HeckeAlgebra.Corner.toHeckeAlgebra_injective μ K hK
  change expansion μ K hK (a * b).1 = expansion μ K hK a.1 * expansion μ K hK b.1
  have hb : ∀ k : K, ∀ x,
      expansion μ K hK b.1 ((k : G) * x) = expansion μ K hK b.1 x :=
    (toCorner μ K hK b).property.1
  apply HeckeAlgebra.ext
  intro x
  rw [expansion_apply]
  change (μ.real (K : Set G) : ℂ)⁻¹ * (a * b).1 (x : G ⧸ K.toSubgroup) =
    evaluation μ x (expansion μ K hK a.1 * expansion μ K hK b.1)
  rw [expansion, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul, map_sum]
  simp_rw [smul_mul_assoc, map_smul]
  change (μ.real (K : Set G) : ℂ)⁻¹ * (a * b).1 (x : G ⧸ K.toSubgroup) =
    ∑ q ∈ a.1.support, a.1 q * (cosetTest μ K hK q * expansion μ K hK b.1) x
  simp_rw [cosetTest_mul μ K hK _ _ hb]
  change (μ.real (K : Set G) : ℂ)⁻¹ *
      (heckeMul ℂ K.toSubgroup K.toSubgroup K.toSubgroup a b).1
        (x : G ⧸ K.toSubgroup) =
    ∑ q ∈ a.1.support, a.1 q * expansion μ K hK b.1 (q.out⁻¹ * x)
  simp_rw [expansion_apply]
  rw [heckeMul_apply K.toSubgroup K.toSubgroup K.toSubgroup a b
    (x : G ⧸ K.toSubgroup), Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  ring

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- A normalized coset indicator acts on a fixed vector by its representative. -/
theorem cosetTest_action (q : G ⧸ K.toSubgroup) (w : fixedVectors ρ K.toSubgroup) :
    heckeAction μ ρ hρ (cosetTest μ K hK q) w = ρ q.out w := by
  change integratedAction μ ρ hρ
    (TestFunction.leftTranslate q.out
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK))) w = _
  rw [integratedAction_leftTranslate]
  change ρ q.out (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) w) = _
  rw [heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK w.property]

/-- The finite expansion has exactly the usual coset action on fixed vectors. -/
theorem expansion_action (a : G ⧸ K.toSubgroup →₀ ℂ) (w : fixedVectors ρ K.toSubgroup) :
    heckeAction μ ρ hρ (expansion μ K hK a) w =
      a.sum fun q r => r • ρ q.out w := by
  rw [expansion, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, LinearMap.smul_apply, cosetTest_action]

/-- The normalized linear map identifies the two actions on fixed vectors. -/
theorem toCorner_action (a : LevelHeckeAlgebra ℂ K.toSubgroup)
    (w : fixedVectors ρ K.toSubgroup) :
    ((a • w : fixedVectors ρ K.toSubgroup) : V) =
      heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
        (toCorner μ K hK a)) w := by
  change (heckeAct ρ K.toSubgroup K.toSubgroup a w : V) =
    heckeAction μ ρ hρ (expansion μ K hK a.1) w
  exact (heckeAct_apply ρ K.toSubgroup K.toSubgroup a w).trans
    (expansion_action μ K hK ρ hρ a.1 w).symm

end LevelCorner

/-- The exact normalized algebra and action comparison, with independent universes. -/
theorem levelHeckeCornerComparison : LevelHeckeCornerComparisonStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ K hK
  refine ⟨LevelCorner.linearEquiv μ K hK, ?_, ?_, ?_⟩
  · intro a b
    exact LevelCorner.toCorner_mul μ K hK a b
  · intro a x
    exact LevelCorner.linearEquiv_apply μ K hK a x
  · intro V _ _ ρ hρ a w
    exact LevelCorner.toCorner_action μ K hK ρ hρ a w

end Langlands.Hecke
