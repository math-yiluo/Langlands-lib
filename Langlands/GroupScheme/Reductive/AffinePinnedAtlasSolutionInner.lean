import Langlands.GroupScheme.Reductive.AffinePinnedAtlasDatum
import Langlands.GroupScheme.Reductive.AffinePinnedAtlasTransitionInner

/-! # Inner discrepancy of actual pinned atlas solutions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

/-- The canonical overlap restricts to the two direct-pullback comparisons. -/
theorem pullIso_canonicalOverlap_comparisons {S U T : Scheme.{u}}
    (p : U ⟶ S) (C : GroupScheme S) (q : T ⟶ Overlap p)
    (a b : T ⟶ U) (ha : q ≫ fst p = a) (hb : q ≫ snd p = b)
    (k : T ⟶ S) (hka : a ≫ p = k) (hkb : b ≫ p = k) :
    pullIso q ha hb (canonicalOverlap p C) =
      pullbackComparison p a k hka C ≪≫
        (pullbackComparison p b k hkb C).symm := by
  apply Iso.ext
  apply (cancel_mono (pullbackComparison p b k hkb C).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      pullbackComparison_hom_fst]
    exact pullHom_canonicalOverlap_fst p C q a b ha hb
  · exact (Over.w ((pullIso q ha hb (canonicalOverlap p C)).hom ≫
      (pullbackComparison p b k hkb C).hom).hom.hom).trans
        (Over.w (pullbackComparison p a k hka C).hom.hom.hom).symm

end Descent

namespace AffinePinnedAtlas

open Descent

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (s : Solution (A.datum P))

/-- The direct-pullback local identifications respect the corrected transitions. -/
theorem solution_pullIso_transition {T : Scheme.{u}}
    (a b : T ⟶ A.space) (k : T ⟶ S)
    (ha : a ≫ A.projection = k) (hb : b ≫ A.projection = k) :
    pullIso a ha ha s.iso ≪≫ A.transition P a b k ha hb =
      pullIso b hb hb s.iso := by
  let q : T ⟶ Overlap A.projection := pullback.lift a b (ha.trans hb.symm)
  have hqa : q ≫ fst A.projection = a := pullback.lift_fst _ _ _
  have hqb : q ≫ snd A.projection = b := pullback.lift_snd _ _ _
  have hc := congrArg (pullHom q hqa hqb) s.compatible
  change pullHom q hqa hqb
      ((baseChange (fst A.projection)).map s.iso.hom ≫ (A.overlap P).hom) =
    pullHom q hqa hqb
      ((canonicalOverlap A.projection s.obj).hom ≫
        (baseChange (snd A.projection)).map s.iso.hom) at hc
  rw [pullHom_comp q hqa hqa hqb, pullHom_map,
    pullHom_comp q hqa hqb hqb, pullHom_map,
    ← pullIso_hom, ← pullIso_hom,
    A.overlap_pull P q a b hqa hqb k ha,
    pullIso_canonicalOverlap_comparisons A.projection s.obj q a b hqa hqb k ha hb] at hc
  apply Iso.ext
  apply (cancel_epi (pullbackComparison A.projection a k ha s.obj).hom).mp
  apply (cancel_mono (pullbackComparison A.projection b k hb G).inv).mp
  simpa only [pullIso, actualTransition, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using hc

/-- The actual solution is locally identified with the original group over the atlas. -/
def solutionLocalIso : LocalGroupIso G s.obj (Over.mk A.projection) :=
  LocalGroupIso.ofBaseChangeIso s.iso.symm

/-- Its discrepancy is exactly the inverse corrected atlas transition. -/
theorem solutionLocalIso_discrepancyIso {T : Over S}
    (b c : T ⟶ Over.mk A.projection) :
    (A.solutionLocalIso P s).discrepancyIso b c =
      (A.transition P b.left c.left T.hom (Over.w b) (Over.w c)).symm := by
  rw [LocalGroupIso.discrepancyIso_eq_composite]
  have hb := LocalGroupIso.ofBaseChangeIso_pullIso s.iso.symm b
  have hc := LocalGroupIso.ofBaseChangeIso_pullIso s.iso.symm c
  change ((LocalGroupIso.ofBaseChangeIso s.iso.symm).refine c).toBaseChangeIso ≪≫
      ((LocalGroupIso.ofBaseChangeIso s.iso.symm).refine b).toBaseChangeIso.symm = _
  rw [← hb, ← hc, LocalGroupIso.toBaseChangeIso_ofBaseChangeIso,
    LocalGroupIso.toBaseChangeIso_ofBaseChangeIso, pullIso_symm, pullIso_symm]
  have h := A.solution_pullIso_transition P s b.left c.left T.hom (Over.w b) (Over.w c)
  apply Iso.ext
  apply (cancel_epi (pullIso c.left (Over.w c) (Over.w c) s.iso).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Iso.hom_inv_id_assoc]
  have hh := congrArg Iso.hom h
  change (pullIso b.left (Over.w b) (Over.w b) s.iso).hom ≫
    (A.transition P b.left c.left T.hom (Over.w b) (Over.w c)).hom =
      (pullIso c.left (Over.w c) (Over.w c) s.iso).hom at hh
  rw [← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The quotient action induces every discrepancy of the actual solution. -/
theorem solutionLocalIso_hasInnerDiscrepancy {Q : GroupScheme S}
    (p : G ⟶ Q) (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction Q G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G)) :
    (A.solutionLocalIso P s).HasInnerDiscrepancy c := by
  apply (LocalGroupIso.hasInnerDiscrepancy_iff_discrepancyIso _ c).mpr
  intro T b d
  refine ⟨A.transitionInnerPoint P p hp c hc b.left d.left T.hom (Over.w b) (Over.w d), ?_⟩
  rw [A.solutionLocalIso_discrepancyIso P s]
  exact A.transitionInnerPoint_spec P p hp c hc b.left d.left T.hom (Over.w b) (Over.w d)

end AffinePinnedAtlas

end Langlands.GroupScheme
