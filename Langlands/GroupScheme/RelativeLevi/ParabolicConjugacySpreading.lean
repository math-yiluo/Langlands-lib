import Langlands.GroupScheme.RelativeLevi.ParabolicFieldPointEquality
import Langlands.GroupScheme.RelativeLevi.ParabolicTransport
import Langlands.GroupScheme.LocalSubgroupConjugacy
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Spreading parabolic conjugacy from a field point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G B B' : GroupScheme S}

/-- Conjugacy by the identity at an arbitrary test scheme means equality of
the two actual base-changed ranges. -/
theorem isConjugatingPoint_one_iff_baseChange_range
    (i : B ⟶ G) (j : B' ⟶ G) (U : Over S) :
    IsConjugatingPoint (range i) (range j) (1 : U ⟶ G.X) ↔
      range ((GroupScheme.baseChange U.hom).map i) =
        range ((GroupScheme.baseChange U.hom).map j) := by
  rw [isConjugatingPoint_iff_baseChange_range]
  simp only [map_one, innerIso_one_hom, Category.comp_id]

/-- A left correction by a point of the target subgroup preserves conjugacy. -/
theorem IsConjugatingPoint.of_mul_inv_mem_target
    {F F' : SubgroupFunctor G} {U : Over S} {g h : U ⟶ G.X}
    (hg : IsConjugatingPoint F F' g)
    (hh : h * g⁻¹ ∈ F'.carrier U) : IsConjugatingPoint F F' h := by
  have hn := (le_normalizer F') U hh
  have hc := hg.trans (isConjugatingPoint_self_iff.mpr hn)
  simpa only [inv_mul_cancel_right] using hc

end SubgroupFunctor

open SubgroupFunctor

section LocalSpreading

variable {S : Scheme.{u}} {G P Q : GroupScheme S}
  (i : P ⟶ G) (j : Q ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- A supplied global normalizer section that conjugates the two parabolics
at a field point continues to conjugate them on a neighbourhood of its image. -/
theorem relativeParabolic_exists_open_conjugatingPoint_of_fieldPoint
    (hLie : RelativeParabolicLieContainmentStatement.{u}) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j)
    (n : Over.mk (𝟙 S) ⟶ G.X)
    (hn : n ∈ (range t).normalizer.carrier (Over.mk (𝟙 S)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (hc : IsConjugatingPoint (range i) (range j)
      (Over.homMk (U := Over.mk x) (V := Over.mk (𝟙 S)) x (by simp) ≫ n)) :
    ∃ V : S.Opens, x (IsLocalRing.closedPoint k) ∈ V ∧
      IsConjugatingPoint (range i) (range j)
        (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 S)) V.ι (by simp) ≫ n) := by
  let iN := i ≫ (G.innerIso n).hom
  have hiN : IsRelativeParabolicSubgroup iN := hi.comp_iso (G.innerIso n)
  have htN : range t ≤ range iN := by
    have hnT := (isConjugatingPoint_iff_range_innerIso t t n).mp
      (isConjugatingPoint_self_iff.mpr hn)
    have h := range_comp_mono hti (G.innerIso n).hom
    rwa [hnT] at h
  have hiC : IsConjugatingPoint (range i) (range iN) n :=
    (isConjugatingPoint_iff_range_innerIso i iN n).mpr rfl
  have hfield : range ((baseChange x).map iN) = range ((baseChange x).map j) := by
    apply (isConjugatingPoint_one_iff_baseChange_range iN j (Over.mk x)).mp
    have h := (hiC.restrict (Over.homMk (U := Over.mk x) (V := Over.mk (𝟙 S)) x (by simp))).inv.trans hc
    simpa only [mul_inv_cancel] using h
  let V := relativeParabolicLocalEqualityOfFieldPoint iN j T t hLie hG hiN hj
    hT ht hmax htN htj x hfield
  refine ⟨V.val, V.property.1, ?_⟩
  have he : IsConjugatingPoint (range iN) (range j)
      (1 : Over.mk V.val.ι ⟶ G.X) :=
    (isConjugatingPoint_one_iff_baseChange_range iN j (Over.mk V.val.ι)).mpr
      V.property.2
  simpa only [one_mul] using
    (hiC.restrict (Over.homMk (U := Over.mk V.val.ι) (V := Over.mk (𝟙 S)) V.val.ι (by simp))).trans he

/-- Choose a neighbourhood on which the supplied normalizer section conjugates
both parabolics, retaining the point and the all-test conjugacy relation. -/
def relativeParabolicLocalConjugacyOfFieldPoint
    (hLie : RelativeParabolicLieContainmentStatement.{u}) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j)
    (n : Over.mk (𝟙 S) ⟶ G.X)
    (hn : n ∈ (range t).normalizer.carrier (Over.mk (𝟙 S)))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (hc : IsConjugatingPoint (range i) (range j)
      (Over.homMk (U := Over.mk x) (V := Over.mk (𝟙 S)) x (by simp) ≫ n)) :
    {V : S.Opens // x (IsLocalRing.closedPoint k) ∈ V ∧
      IsConjugatingPoint (range i) (range j)
        (Over.homMk (U := Over.mk V.ι) (V := Over.mk (𝟙 S)) V.ι (by simp) ≫ n)} :=
  let h := relativeParabolic_exists_open_conjugatingPoint_of_fieldPoint
    i j T t hLie hG hi hj hT ht hmax hti htj n hn x hc
  ⟨h.choose, h.choose_spec⟩

end LocalSpreading

end Langlands.GroupScheme
