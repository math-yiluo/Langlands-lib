import Langlands.GroupScheme.Unipotent.SeparableSplitDescentStatement
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Reductive.SplitRadicalWoundReduction
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionProof
import Langlands.GroupScheme.Rational.UnipotentWoundSeparableExtensionProof

/-! # Split unipotence descends along separable field extensions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Split unipotence descends along any separable algebraic field extension (Milne 14.65). -/
theorem separableSplitUnipotentDescent : SeparableSplitUnipotentDescentStatement.{u} := by
  intro k _ G _ _ hG K _ _ hSep hSplit
  let : Algebra.IsSeparable k K := hSep
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let GK := B.obj G
  obtain ⟨hbSurj, hbFlat, hbQc⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbSurj
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQc
  let : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  change RelativeRoot.IsSplitUnipotent GK at hSplit
  obtain ⟨n, hSeries⟩ := hSplit
  obtain ⟨e⟩ := splitUnipotentAffineSpaceStatement K n GK inferInstance hSeries
  have hSmoothK : Smooth GK.X.hom := by
    let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    rw [← Over.w e.hom]
    change Smooth (e.hom.left ≫
      (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)))
    infer_instance
  have hConnectedK : ConnectedSpace GK.X.left := by
    apply (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.mpr
    change ConnectedSpace 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of K))
    infer_instance
  let : Smooth G.X.hom := smooth_of_baseChange b G hSmoothK
  let : ConnectedSpace G.X.left := connectedSpace_of_baseChange b G hConnectedK

  obtain ⟨N, i, hi⟩ := SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence k G
  obtain ⟨Q, q, hSmoothQ, hAffineQ, hq⟩ :=
    normalSubgroupQuotient k G N i hi.isClosedSubgroup hi.isNormal
  let : Smooth Q.X.hom := hSmoothQ
  let : IsAffineHom Q.X.hom := hAffineQ
  let : ConnectedSpace Q.X.left := hq.connectedSpace
  have hWound := hi.hasConstantAffineLineMaps_quotient_of_criterion hq unipotentWoundCriterion hG
  have hWoundK : HasConstantAffineLineMaps (B.obj Q) :=
    (unipotentWoundSeparableExtension k K Q (hq.isUnipotent hG)).mp hWound
  have hZero : q = 0 := by
    apply B.map_injective
    rw [Functor.map_zero]
    exact hWoundK.hom_eq_zero_of_isSplitUnipotent ⟨n, hSeries⟩ (B.map q)

  have hRange : SubgroupFunctor.range i = SubgroupFunctor.range (𝟙 G) := by
    rw [← hq.2.2.2, SubgroupFunctor.range_id]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      rw [mem_range_kernelι_iff, hZero]
      exact MonObj.comp_one _
  have hId : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  exact RelativeRoot.IsSplitUnipotent.of_iso
    (hi.isClosedSubgroup.sourceIsoOfRangeEq hId hRange) hi.isSplitUnipotent

end Langlands.GroupScheme
