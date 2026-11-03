import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.KernelCentralizerStructureProof
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Rational.RootProductTransport

/-! # Smooth closed representatives of the intrinsic character-orbit root functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- A smooth closed represented subgroup, without a chosen representative or
any connectedness requirement. -/
def IsSmoothClosed {B : Scheme.{u}} {G : GroupScheme B}
    (F : SubgroupFunctor G) : Prop :=
  ∃ (H : GroupScheme B) (j : H ⟶ G),
    F.IsRepresentedBy j ∧ IsClosedSubgroup j ∧ Smooth H.X.hom

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [hAff : IsAffineHom G.X.hom] [hG : Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (a : characterLattice S) (ha : a ≠ 0)

include hAff hG hS ha

/-- Every intrinsic root functor has a smooth closed representative. Dynamic
connectedness, if supplied, makes this same representative connected. -/
theorem subgroup_has_smooth_closed_representative :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G),
      (subgroup i a).IsRepresentedBy jU ∧ IsClosedSubgroup jU ∧
        Smooth U.X.hom ∧
          (DynamicConnectedStatement.{u} → ConnectedSpace U.X.left) := by
  obtain ⟨C, j, hj, hjc, hCs, _⟩ :=
    kernelCentralizerStructure k G inferInstance inferInstance S hS i a ha
  let : IsAffineHom C.X.hom := by
    let : IsClosedImmersion j.hom.hom.left := hjc
    rw [← j.hom.hom.w]
    infer_instance
  let : Smooth C.X.hom := hCs
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k S hS a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hsurj
  let b := quotientAction i a j hj
  refine ⟨AutomorphicAction.Affine.unipotentScheme b,
    AutomorphicAction.Affine.unipotentHom b ≫ j, ?_,
    (AutomorphicAction.Affine.isClosedSubgroup_unipotentHom b).comp hjc,
    AutomorphicAction.Affine.smooth_unipotentScheme b,
    AutomorphicAction.Affine.connected_unipotentScheme b⟩
  rw [quotientActionComparison _ _ _ _ i a j hj hjc]
  exact (AutomorphicAction.Affine.isRepresentedBy_unipotentHom b).comp hj

/-- Every nonzero intrinsic root functor is smooth and closed. -/
theorem subgroup_isSmoothClosed : IsSmoothClosed (subgroup i a) := by
  obtain ⟨U, jU, hjU, hjUc, hUs, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  exact ⟨U, jU, hjU, hjUc, hUs⟩

/-- Closed representability holds without any connectedness theorem. -/
theorem subgroup_isClosedRepresentable : (subgroup i a).IsClosedRepresentable := by
  obtain ⟨U, jU, hjU, hjUc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  exact ⟨U, jU, hjU, hjUc⟩

/-- Every representative of the intrinsic root functor is smooth. -/
theorem smooth_of_isRepresentedBy_subgroup
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hjU : (subgroup i a).IsRepresentedBy jU) : Smooth U.X.hom := by
  obtain ⟨V, jV, hjV, _, hVs, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso (hjU.isoOfIsRepresentedBy hjV)) hVs

/-- Dynamic connectedness implies connectedness of every root representative. -/
theorem connected_of_isRepresentedBy_subgroup (h : DynamicConnectedStatement.{u})
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hjU : (subgroup i a).IsRepresentedBy jU) : ConnectedSpace U.X.left := by
  obtain ⟨V, jV, hjV, _, _, hVc⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  exact connectedSpace_of_over_iso
    ((Grp.forget _).mapIso (hjU.isoOfIsRepresentedBy hjV)) (hVc h)

/-- The intrinsic root functor is smooth, connected and closed, conditional only
on dynamic connectedness. No reductivity or actual-root premise is needed. -/
theorem subgroup_isSmoothConnectedClosed (h : DynamicConnectedStatement.{u}) :
    IsSmoothConnectedClosed (subgroup i a) := by
  obtain ⟨U, jU, hjU, hjUc, hUs, hUc⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  exact ⟨U, jU, hjU, hjUc, hUs, hUc h⟩

end Langlands.GroupScheme.RelativeRoot
