import Langlands.GroupScheme.Absolute.SolvableUnipotentPart
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Greatest unipotent subgroups and changes of presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {U V B C : GroupScheme (Spec (CommRingCat.of k))}

/-- A smooth connected unipotent closed subgroup containing every unipotent
closed subgroup of its ambient group. -/
def IsUnipotentPart (i : U ⟶ B) : Prop :=
  IsClosedSubgroup i ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
    ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ B),
      IsClosedSubgroup j → IsUnipotent V →
        SubgroupFunctor.range j ≤ SubgroupFunctor.range i

namespace IsUnipotentPart

variable {i : U ⟶ B}

theorem isClosedSubgroup (hi : IsUnipotentPart i) : IsClosedSubgroup i := hi.1
theorem smooth (hi : IsUnipotentPart i) : Smooth U.X.hom := hi.2.1
theorem connectedSpace (hi : IsUnipotentPart i) : ConnectedSpace U.X.left := hi.2.2.1
theorem isUnipotent (hi : IsUnipotentPart i) : IsUnipotent U := hi.2.2.2.1
theorem greatest (hi : IsUnipotentPart i)
    (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ B) :
    IsClosedSubgroup j → IsUnipotent V →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range i := hi.2.2.2.2 V j

/-- Two unipotent parts have the same all-test subgroup functor. -/
theorem range_eq (hi : IsUnipotentPart i) {j : V ⟶ B} (hj : IsUnipotentPart j) :
    SubgroupFunctor.range i = SubgroupFunctor.range j :=
  le_antisymm (hj.greatest U i hi.isClosedSubgroup hi.isUnipotent)
    (hi.greatest V j hj.isClosedSubgroup hj.isUnipotent)

/-- The unique source isomorphism between two unipotent parts. -/
theorem exists_iso (hi : IsUnipotentPart i) {j : V ⟶ B} (hj : IsUnipotentPart j) :
    ∃ e : U ≅ V, e.hom ≫ j = i := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let hri : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hrj : (SubgroupFunctor.range i).IsRepresentedBy j := ⟨inferInstance, (hi.range_eq hj).symm⟩
  exact ⟨hri.isoOfIsRepresentedBy hrj, hri.isoOfIsRepresentedBy_hom_comp hrj⟩

/-- Change the source presentation of a unipotent part. -/
theorem iso_comp (hi : IsUnipotentPart i) (e : V ≅ U) :
    IsUnipotentPart (e.hom ≫ i) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : Smooth U.X.hom := hi.smooth
  refine ⟨?_, ?_, ?_, IsUnipotent.of_iso e hi.isUnipotent, ?_⟩
  · change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hi.connectedSpace
  · intro W j hj hu
    exact (hi.greatest W j hj hu).trans
      (SubgroupFunctor.range_le_of_factor e.inv (by simp))

/-- Change the ambient group of a unipotent part. -/
theorem comp_iso (hi : IsUnipotentPart i) (e : B ≅ C) :
    IsUnipotentPart (i ≫ e.hom) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  refine ⟨?_, hi.smooth, hi.connectedSpace, hi.isUnipotent, ?_⟩
  · change IsClosedImmersion (i.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · intro W j hj hu
    have : IsClosedImmersion j.hom.hom.left := hj
    have hjc : IsClosedSubgroup (j ≫ e.inv) := by
      change IsClosedImmersion (j.hom.hom.left ≫ e.inv.hom.hom.left)
      infer_instance
    have hle := hi.greatest W (j ≫ e.inv) hjc hu
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    have : IsClosedImmersion (j ≫ e.inv).hom.hom.left := hjc
    have : Mono (j ≫ e.inv).hom.hom := Over.mono_of_mono_left _
    let f := SubgroupFunctor.factorOfRangeLE hle
    have hf : f ≫ i = j ≫ e.inv := SubgroupFunctor.factorOfRangeLE_comp hle
    exact SubgroupFunctor.range_le_of_factor f (by
      rw [← Category.assoc, hf, Category.assoc, e.inv_hom_id, Category.comp_id])

end IsUnipotentPart

/-- The published solvable unipotent-part theorem gives the greatest-subgroup predicate. -/
theorem exists_isUnipotentPart [IsAlgClosed k] (B : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    (hB : IsSolvableGroupScheme B) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ B), IsUnipotentPart i := by
  obtain ⟨U, i, hc, hs, hconn, hu, _, hgreat⟩ := solvableUnipotentPart k B hB
  exact ⟨U, i, hc, hs, hconn, hu, hgreat⟩

end Langlands.GroupScheme
