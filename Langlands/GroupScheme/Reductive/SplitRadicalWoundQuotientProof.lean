import Langlands.GroupScheme.Reductive.SplitKernelAction
import Langlands.GroupScheme.Reductive.SplitRadicalWoundReduction
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalInclusion
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.CommutativePTorsionVectorFactorProof
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionFromVectorFactor
import Langlands.GroupScheme.Rational.WoundSeparableFromCriterion
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity

/-! # Woundness of the ordinary radical modulo the split radical -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Every supplied fppf quotient of the ordinary unipotent radical by the
ambient split unipotent radical has only constant affine-line maps. -/
theorem splitRadicalWoundQuotient : SplitRadicalWoundQuotientStatement.{u} := by
  have hC : UnipotentWoundCriterionStatement.{u} :=
    UnipotentWoundCriterionReduction.criterion_of_vectorFactor
      RelativeRoot.commutativePTorsionVectorFactor
  have hS : UnipotentWoundSeparableExtensionStatement.{u} :=
    woundSeparableFromCriterion hC
  intro k _ G _ _ _ U V j n hj hn m hm Q _ _ _ q hq
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Smooth U.X.hom := hj.smooth
  let : IsAffineHom U.X.hom := hj.isClosedSubgroup.isAffineHom
  let : ConnectedSpace U.X.left := hj.connectedSpace
  obtain ⟨W, w, hw⟩ :=
    SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence k U
  let : Smooth W.X.hom := hw.smooth
  let : IsAffineHom W.X.hom := hw.isClosedSubgroup.isAffineHom
  obtain ⟨R, r, hRsm, hRa, hr⟩ :=
    normalSubgroupQuotient k U W w hw.isClosedSubgroup hw.isNormal
  let : Smooth R.X.hom := hRsm
  let : IsAffineHom R.X.hom := hRa
  let : ConnectedSpace R.X.left := hr.connectedSpace
  have hR : HasConstantAffineLineMaps R :=
    hw.hasConstantAffineLineMaps_quotient_of_criterion hr hC hj.isUnipotent
  let K := SeparableClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let GK := (GroupScheme.baseChange b).obj G
  let WK := (GroupScheme.baseChange b).obj W
  let : Smooth GK.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  let : Smooth WK.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd W.X.hom b)
    infer_instance
  let : Smooth (GK.X ⊗ WK.X).hom := smooth_tensor GK.X WK.X inferInstance inferInstance
  have hRK : HasConstantAffineLineMaps ((GroupScheme.baseChange b).obj R) :=
    (hS k K R (hr.isUnipotent hj.isUnipotent)).mp hR
  have hD : HasDenseRationalPoints K (GK.X ⊗ WK.X) :=
    hasDenseRationalPoints_of_smooth_of_isSepClosed K (GK.X ⊗ WK.X)
  let a : AutomorphicAction G U := AutomorphicAction.ofNormalizedConjugation j (𝟙 G)
    (fun T g x _ hx => hj.isNormal T g x (Subgroup.mem_top _) hx)
  let aW : AutomorphicAction G W :=
    a.onSplitKernelOfWoundBaseChange K w hw.isClosedSubgroup r hr
      hw.isSplitUnipotent hRK hD
  have hWnormal : (SubgroupFunctor.range (w ≫ j)).IsNormal := by
    intro T g x _ hx
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨aW.act g v, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc]
    rw [a.onSplitKernelOfWoundBaseChange_act_comp]
    simpa only [a, Grp.id_hom_hom, Category.comp_id, Grp.comp_hom_hom,
      Category.assoc] using
      (AutomorphicAction.ofNormalizedConjugation_act_comp j (𝟙 G)
        (fun T g x _ hx => hj.isNormal T g x (Subgroup.mem_top _) hx)
        g (v ≫ w.hom.hom))
  have hWambient : SubgroupFunctor.range (w ≫ j) ≤ SubgroupFunctor.range n :=
    hn.greatest W (w ≫ j) (hw.isClosedSubgroup.comp hj.isClosedSubgroup)
      hw.smooth hw.connectedSpace hw.isUnipotent hw.isSplitUnipotent hWnormal
  have hWle : SubgroupFunctor.range w ≤ SubgroupFunctor.range m := by
    intro T x hx
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hxj : (v ≫ w.hom.hom) ≫ j.hom.hom ∈
        (SubgroupFunctor.range (w ≫ j)).carrier T := by
      exact SubgroupFunctor.mem_range.mpr ⟨v, by
        simp only [Grp.comp_hom_hom, Category.assoc]⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hWambient T hxj)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y, ?_⟩
    apply (cancel_mono j.hom.hom).mp
    rw [← hm] at hy
    simpa only [Grp.comp_hom_hom, ← Category.assoc] using hy
  have hmr : IsSplitUnipotentRadical m := {
    isClosedSubgroup := IsClosedSubgroup.of_comp hj.isClosedSubgroup
      (by rw [hm]; exact hn.isClosedSubgroup)
    smooth := hn.smooth
    connectedSpace := hn.connectedSpace
    isUnipotent := hn.isUnipotent
    isSplitUnipotent := hn.isSplitUnipotent
    isNormal := by
      rw [← range_comp_comap_of_mono m j, hm]
      exact hn.isNormal.comap j
    greatest := fun N i hi hs hc hu hsplit hnormal =>
      (hw.greatest N i hi hs hc hu hsplit hnormal).trans hWle }
  exact hmr.hasConstantAffineLineMaps_quotient_of_criterion hq hC hj.isUnipotent

end Langlands.GroupScheme
