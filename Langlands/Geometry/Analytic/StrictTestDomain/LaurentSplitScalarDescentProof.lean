import Langlands.Geometry.Analytic.StrictTestDomain.LaurentSplitScalarDescentStatement
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentGluingProof

/-! # Degree-zero scalar Laurent diagram chase -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

private theorem lift_eq_on_smaller (d e t : RationalData K P) (inc : t ⟶ e)
    (a : e.algebra) (s : d.algebra)
    (h : (d.pullback e.baseMap).baseMap a = d.comparison e.baseMap s) :
    (d.pullback t.baseMap).baseMap (inc.restriction a) =
      d.comparison t.baseMap s := by
  let m := d.pullbackTriangleMap e.baseMap t.baseMap inc.restriction
    inc.restriction_comp_baseMap
  have hm := congrArg m h
  change (m.comp (d.pullback e.baseMap).baseMap) a =
    (m.comp (d.comparison e.baseMap)) s at hm
  rw [pullbackTriangleMap_comp_baseMap, pullbackTriangleMap_comp_comparison] at hm
  exact hm

/-- The actual upper and lower base maps jointly separate scalar elements. -/
theorem eq_of_binaryLaurent_images (f : P) {a b : P}
    (hU : (laurentUpper f).baseMap a = (laurentUpper f).baseMap b)
    (hL : (laurentLower f).baseMap a = (laurentLower f).baseMap b) : a = b := by
  have hc :
      (interLeft (laurentUpper f) (laurentLower f)).restriction
          ((laurentUpper f).baseMap b) =
        (interRight (laurentUpper f) (laurentLower f)).restriction
          ((laurentLower f).baseMap b) :=
    (congrArg (fun g => g b)
      (interLeft (laurentUpper f) (laurentLower f)).restriction_comp_baseMap).trans
      (congrArg (fun g => g b)
        (interRight (laurentUpper f) (laurentLower f)).restriction_comp_baseMap).symm
  obtain ⟨c, _, hu⟩ := binaryLaurentGluing K P f
    ((laurentUpper f).baseMap b) ((laurentLower f).baseMap b) hc
  exact (hu a ⟨hU, hL⟩).trans (hu b ⟨rfl, rfl⟩).symm

private theorem eq_of_laurent_pullback_images (d : RationalData K P) (f : P)
    {a b : d.algebra}
    (hU : ((laurentUpper f).pullback d.baseMap).baseMap a =
      ((laurentUpper f).pullback d.baseMap).baseMap b)
    (hL : ((laurentLower f).pullback d.baseMap).baseMap a =
      ((laurentLower f).pullback d.baseMap).baseMap b) : a = b := by
  apply eq_of_binaryLaurent_images (d.baseMap f)
  · exact Eq.mp (congrArg
      (fun e : RationalData K d.algebra => e.baseMap a = e.baseMap b)
      (pullback_laurentUpper f d.baseMap)) hU
  · exact Eq.mp (congrArg
      (fun e : RationalData K d.algebra => e.baseMap a = e.baseMap b)
      (pullback_laurentLower f d.baseMap)) hL

/-- The degree-zero Laurent split chase on actual rational quotients. -/
theorem laurentSplitScalarDescent : LaurentSplitScalarDescentStatement.{u,v} := by
  intro K _ _ _ P I D f hU hL hO s hs
  let U := laurentUpper f
  let L := laurentLower f
  let O := U.inter L
  obtain ⟨aU, haU, huU⟩ := hU (fun i => (D i).comparison U.baseMap (s i))
    (hs.comparison U.baseMap)
  obtain ⟨aL, haL, huL⟩ := hL (fun i => (D i).comparison L.baseMap (s i))
    (hs.comparison L.baseMap)
  have hcompat : (interLeft U L).restriction aU =
      (interRight U L).restriction aL := by
    apply hO
    intro i
    exact (lift_eq_on_smaller (D i) U O (interLeft U L) aU (s i) (haU i)).trans
      (lift_eq_on_smaller (D i) L O (interRight U L) aL (s i) (haL i)).symm
  obtain ⟨a, ha, hu⟩ := binaryLaurentGluing K P f aU aL hcompat
  refine ⟨a, ?_, ?_⟩
  · intro i
    apply eq_of_laurent_pullback_images (D i) f
    · exact (D i).pullback_base_images_eq U a (s i) (by
        rw [show U.baseMap a = aU from ha.1]
        exact haU i)
    · exact (D i).pullback_base_images_eq L a (s i) (by
        rw [show L.baseMap a = aL from ha.2]
        exact haL i)
  · intro b hb
    apply hu b
    constructor
    · apply huU
      intro i
      exact (congrArg (fun g => g b) ((D i).comparison_comp_baseMap U.baseMap)).symm.trans
        (congrArg ((D i).comparison U.baseMap) (hb i))
    · apply huL
      intro i
      exact (congrArg (fun g => g b) ((D i).comparison_comp_baseMap L.baseMap)).symm.trans
        (congrArg ((D i).comparison L.baseMap) (hb i))

end Langlands.Analytic.StrictTestDomain
