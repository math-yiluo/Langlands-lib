import Langlands.Analysis.Local.CompactOpenFactorNormalization
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Local product geometry and choice-independent factor measures -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG uX

section Geometry

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) {X : Type uX} [TopologicalSpace X]
  (s : X → G) (m : H × X ≃ₜ G)
  (hm : ∀ p : H × X, m p = p.1.val * s p.2)

/-- A nonempty local Cartesian product in ordered coordinates gives the
corresponding image on the actual left quotient. The second coordinate
space need not be a group. -/
theorem factorQuotientHomeomorph_image_of_localProduct
    (A : Set H) (B : Set X) (T : Set G) (hA : A.Nonempty)
    (hprod : m '' (A ×ˢ B) = T) :
    factorQuotientHomeomorph H s m hm '' B = leftQuotientMap H '' T := by
  let c := factorQuotientHomeomorph H s m hm
  have hq (h : H) (x : X) : leftQuotientMap H (m (h, x)) = c x := by
    rw [hm, leftQuotientMap_subgroup_mul]
    rfl
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h, hh⟩ := hA
    refine ⟨m (h, x), ?_, hq h x⟩
    rw [← hprod]
    exact ⟨(h, x), ⟨hh, hx⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rw [← hprod] at hg
    obtain ⟨⟨h, x⟩, ⟨hh, hx⟩, rfl⟩ := hg
    exact ⟨x, hx, (hq h x).symm⟩

end Geometry

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H K : Subgroup G)
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace K] [BorelSpace K]
  (μG : Measure G) (μH : Measure H) (μK : Measure K)
  (S : OpenSubgroup G) (B : OpenSubgroup K)

/-- The explicit normalized ordered product measure, constructed from
ambient, intersection and complementary compact-open volumes. -/
def compactOpenFactorProductMeasure : Measure (H × K) :=
  μH.prod (compactOpenFactorMeasure H K μG μH μK S B)

/-- Regularity of the seed product passes to the constructed product by
finite nonnegative real scaling. -/
instance compactOpenFactorProductMeasure_regular
    [SFinite μK] [(μH.prod μK).Regular] :
    (compactOpenFactorProductMeasure H K μG μH μK S B).Regular := by
  unfold compactOpenFactorProductMeasure compactOpenFactorMeasure
  rw [Measure.prod_smul_right]
  infer_instance

section Comparison

variable [T2Space G] [LocallyCompactSpace G]
  [IsHaarMeasure μG] [μG.Regular]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  (m : H × K ≃ₜ G) (hm : ∀ p : H × K, m p = p.1.val * p.2.val)
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  {ν : Measure (LeftQuotient H)}

/-- Actual local product geometry supplies the orbit identity used by
the explicit complement Haar normalization. -/
theorem IsCompatible.measurePreserving_compactOpenFactorMeasure_of_localProduct
    (hν : IsCompatible H μG μH ν)
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K))
    (hprod : m '' ({h : H | (h : G) ∈ S} ×ˢ (B : Set K)) = (S : Set G)) :
    MeasurePreserving (factorQuotientHomeomorph H Subtype.val m hm)
      (compactOpenFactorMeasure H K μG μH μK S B) ν :=
  hν.measurePreserving_compactOpenFactorMeasure H K μG μH μK S B m hm hH hS hB
    (factorQuotientHomeomorph_image_of_localProduct H Subtype.val m hm
      _ _ _ ⟨1, S.one_mem⟩ hprod)

include hm in
/-- With a common compatible Weil measure, the explicitly constructed
complement measure is independent of both compact-open choices and the
regular two-sided seed Haar measure. -/
theorem IsCompatible.compactOpenFactorMeasure_eq_of_localProducts
    (hν : IsCompatible H μG μH ν)
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K))
    (hprod : m '' ({h : H | (h : G) ∈ S} ×ˢ (B : Set K)) = (S : Set G))
    (μK' : Measure K) [IsHaarMeasure μK'] [μK'.Regular] [IsMulRightInvariant μK']
    (T : OpenSubgroup G) (C : OpenSubgroup K)
    (hT : IsCompact (T : Set G)) (hC : IsCompact (C : Set K))
    (hprod' : m '' ({h : H | (h : G) ∈ T} ×ˢ (C : Set K)) = (T : Set G)) :
    compactOpenFactorMeasure H K μG μH μK S B =
      compactOpenFactorMeasure H K μG μH μK' T C := by
  have horbit := factorQuotientHomeomorph_image_of_localProduct H Subtype.val m hm
    _ _ _ ⟨1, S.one_mem⟩ hprod
  have horbit' := factorQuotientHomeomorph_image_of_localProduct H Subtype.val m hm
    _ _ _ ⟨1, T.one_mem⟩ hprod'
  exact (hν.map_symm_eq_compactOpenFactorMeasure H K μG μH μK S B m hm
    hH hS hB horbit).symm.trans
      (hν.map_symm_eq_compactOpenFactorMeasure H K μG μH μK' T C m hm
        hH hT hC horbit')

section Product

variable [BorelSpace (H × K)] [SFinite μH] [SFinite μK]
  [(μH.prod μK).Regular]

include hm in
/-- The full ambient product identity follows from the explicit local
volume construction and actual local product geometry. -/
theorem IsCompatible.measurePreserving_compactOpenFactorProductMeasure
    (hν : IsCompatible H μG μH ν)
    (hH : IsClosed (H : Set G))
    (hS : IsCompact (S : Set G)) (hB : IsCompact (B : Set K))
    (hprod : m '' ({h : H | (h : G) ∈ S} ×ˢ (B : Set K)) = (S : Set G)) :
    MeasurePreserving m (compactOpenFactorProductMeasure H K μG μH μK S B) μG := by
  let : IsHaarMeasure (compactOpenFactorMeasure H K μG μH μK S B) :=
    compactOpenFactorMeasure_isHaarMeasure H K μG μH μK S B hH hS hB
  let : (μH.prod (compactOpenFactorMeasure H K μG μH μK S B)).Regular :=
    compactOpenFactorProductMeasure_regular H K μG μH μK S B
  exact hν.measurePreserving_factorProduct H K m hm
    (compactOpenFactorMeasure H K μG μH μK S B)
    (hν.measurePreserving_compactOpenFactorMeasure_of_localProduct H K μG μH μK S B
      m hm hH hS hB hprod)

end Product

end Comparison

end Langlands.QuotientIntegration
