import Langlands.GroupScheme.RelativeLevi.ParabolicConjugacySpreading
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport

/-! # Parabolic conjugacy from a normalizer section on an open -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

open SubgroupFunctor

section LocalSection

variable {S : Scheme.{u}} {G P Q : GroupScheme S}
    (i : P ⟶ G) (j : Q ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- A normalizer section on a neighbourhood, conjugating at a specified field
point, yields a smaller neighbourhood on which it conjugates both parabolics. -/
theorem relativeParabolic_exists_open_conjugatingPoint_of_local_fieldPoint
    (hLie : RelativeParabolicLieContainmentStatement.{u}) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (V : S.Opens) (a : Over.mk x ⟶ Over.mk V.ι)
    (nV : Over.mk V.ι ⟶ G.X)
    (hnV : nV ∈ (range t).normalizer.carrier (Over.mk V.ι))
    (hc : IsConjugatingPoint (range i) (range j) (a ≫ nV)) :
    ∃ U : S.Opens, x (IsLocalRing.closedPoint k) ∈ U ∧
      ∃ nU : Over.mk U.ι ⟶ G.X,
        nU ∈ (range t).normalizer.carrier (Over.mk U.ι) ∧
          IsConjugatingPoint (range i) (range j) nU := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let iV := (baseChange V.ι).map i
  let jV := (baseChange V.ι).map j
  let TV := (CommGroupScheme.baseChange V.ι).obj T
  let tV := (baseChange V.ι).map t
  let n := (baseChangeBasePointsEquiv V.ι G).symm nV
  have hnleft : n.left ≫ CategoryTheory.Limits.pullback.fst G.X.hom V.ι = nV.left := by
    rw [← baseChangeBasePointsEquiv_left]
    exact congrArg (fun f => f.left)
      (MulEquiv.apply_symm_apply (baseChangeBasePointsEquiv V.ι G) nV)
  have hn : n ∈ (range tV).normalizer.carrier (Over.mk (𝟙 V.toScheme)) := by
    apply isConjugatingPoint_self_iff.mp
    change IsConjugatingPoint (range ((baseChange V.ι).map t))
      (range ((baseChange V.ι).map t)) n
    rw [range_baseChangeHom]
    apply (isConjugatingPoint_baseChangeBasePointsEquiv_iff V.ι n).mpr
    simpa only [n, MulEquiv.apply_symm_apply] using isConjugatingPoint_self_iff.mpr hnV
  let y : Spec (CommRingCat.of k) ⟶ V.toScheme := a.left
  let q : Over.mk y ⟶ Over.mk (𝟙 V.toScheme) := Over.homMk y (by simp)
  let e : (Over.map V.ι).obj (Over.mk y) ⟶ Over.mk x :=
    Over.homMk (𝟙 _) (by
      change (𝟙 _) ≫ x = a.left ≫ V.ι
      simpa only [Category.id_comp] using (show a.left ≫ V.ι = x from a.w).symm)
  have hpoint : baseChangePointsEquiv V.ι G (Over.mk y) (q ≫ n) = e ≫ (a ≫ nV) := by
    apply Over.OverMorphism.ext
    change (a.left ≫ n.left) ≫ CategoryTheory.Limits.pullback.fst G.X.hom V.ι =
      (𝟙 _) ≫ (a.left ≫ nV.left)
    rw [Category.assoc, hnleft, Category.id_comp]
  have hcV : IsConjugatingPoint (range iV) (range jV) (q ≫ n) := by
    simpa only [iV, jV, range_baseChangeHom] using hc.baseChange V.ι e (q ≫ n) hpoint
  have htiV : range tV ≤ range iV := by
    simpa only [tV, iV, range_baseChangeHom] using baseChange_mono V.ι hti
  have htjV : range tV ≤ range jV := by
    simpa only [tV, jV, range_baseChangeHom] using baseChange_mono V.ι htj
  obtain ⟨W, hw, hcW⟩ := relativeParabolic_exists_open_conjugatingPoint_of_fieldPoint
    iV jV TV tV hLie (hG.baseChange V.ι) (hi.baseChange hG V.ι)
    (hj.baseChange hG V.ι) (hT.baseChange V.ι) (ht.baseChange V.ι)
    (hmax.baseChange V.ι) htiV htjV n hn y hcV
  let qW : W.toScheme ⟶ S := W.ι ≫ V.ι
  let cW : Over.mk qW ⟶ Over.mk V.ι := Over.homMk W.ι rfl
  have hcW' : IsConjugatingPoint (range i) (range j) (cW ≫ nV) := by
    have hcWb : IsConjugatingPoint ((range i).baseChange V.ι)
        ((range j).baseChange V.ι)
        (Over.homMk (U := Over.mk W.ι) (V := Over.mk (𝟙 V.toScheme)) W.ι (by simp) ≫ n) := by
      simpa only [iV, jV, range_baseChangeHom] using hcW
    have h := hcWb.of_baseChange V.ι
    have he : baseChangePointsEquiv V.ι G (Over.mk W.ι)
        (Over.homMk (U := Over.mk W.ι) (V := Over.mk (𝟙 V.toScheme)) W.ι (by simp) ≫ n) =
        cW ≫ nV := by
      apply Over.OverMorphism.ext
      change (W.ι ≫ n.left) ≫ CategoryTheory.Limits.pullback.fst G.X.hom V.ι = W.ι ≫ nV.left
      rw [Category.assoc, hnleft]
    rwa [he] at h
  let U : S.Opens := qW.opensRange
  have hrange : Set.range qW = Set.range U.ι := by simp [U]
  let eU : W.toScheme ≅ U.toScheme := IsOpenImmersion.isoOfRangeEq qW U.ι hrange
  let b : Over.mk U.ι ⟶ Over.mk qW :=
    Over.homMk eU.inv (IsOpenImmersion.isoOfRangeEq_inv_fac qW U.ι hrange)
  refine ⟨U, ?_, b ≫ cW ≫ nV,
    (range t).normalizer.comp_mem (b ≫ cW) hnV, hcW'.restrict b⟩
  apply Scheme.Hom.mem_opensRange.mpr
  refine ⟨⟨y (IsLocalRing.closedPoint k), hw⟩, ?_⟩
  change (a.left ≫ V.ι) (IsLocalRing.closedPoint k) = x (IsLocalRing.closedPoint k)
  exact congrArg (fun f : Spec (CommRingCat.of k) ⟶ S =>
    f (IsLocalRing.closedPoint k)) (show a.left ≫ V.ι = x from a.w)

/-- Choose an open and an actual normalizer conjugator by shrinking a supplied
local section that conjugates the parabolics at a field-valued point. -/
def relativeParabolicLocalNormalizerConjugacyOfLocalFieldPoint
    (hLie : RelativeParabolicLieContainmentStatement.{u}) (hG : IsReductive G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (V : S.Opens) (a : Over.mk x ⟶ Over.mk V.ι)
    (nV : Over.mk V.ι ⟶ G.X)
    (hnV : nV ∈ (range t).normalizer.carrier (Over.mk V.ι))
    (hc : IsConjugatingPoint (range i) (range j) (a ≫ nV)) :
    Σ U : S.Opens, {nU : Over.mk U.ι ⟶ G.X //
      x (IsLocalRing.closedPoint k) ∈ U ∧
        nU ∈ (range t).normalizer.carrier (Over.mk U.ι) ∧
          IsConjugatingPoint (range i) (range j) nU} :=
  let h := relativeParabolic_exists_open_conjugatingPoint_of_local_fieldPoint
    i j T t hLie hG hi hj hT ht hmax hti htj x V a nV hnV hc
  ⟨h.choose, h.choose_spec.2.choose, h.choose_spec.1, h.choose_spec.2.choose_spec⟩

end LocalSection

end Langlands.GroupScheme
