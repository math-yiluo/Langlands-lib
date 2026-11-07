import Langlands.GroupScheme.Reductive.PinnedIsomorphismFunctoriality
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Subgroup.Defs

/-! # Actual lifts of based root-datum automorphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The full root-datum automorphisms preserving the chosen simple-root support. -/
def basedRootDatumAut (p : SplitPinning G) : Subgroup (RootPairing.Aut p.rootDatum) where
  carrier := {e | ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ p.base.support}
  one_mem' := by
    intro a
    rfl
  mul_mem' := by
    intro e d he hd a
    exact (hd a).trans (he (d.indexEquiv a))
  inv_mem' := by
    intro e he a
    change a ∈ p.base.support ↔ e.indexEquiv.symm a ∈ p.base.support
    simpa only [Equiv.apply_symm_apply] using (he (e.indexEquiv.symm a)).symm

/-- The complete actual pinned lift of a based full root-datum automorphism. -/
def isoOfBasedRootDatumAut (p : SplitPinning G) (e : p.basedRootDatumAut) :
    SplitPinning.Iso p p :=
  p.isoOfRootDatumEquiv p e.val e.property

/-- Based root-datum automorphisms act by actual automorphisms of the field group. -/
def basedRootDatumAutLift (p : SplitPinning G) :
    p.basedRootDatumAut →* CategoryTheory.Aut G where
  toFun e := (p.isoOfBasedRootDatumAut e).groupIso
  map_one' := congrArg (fun f : SplitPinning.Iso p p => f.groupIso)
    (p.isoOfRootDatumEquiv_id)
  map_mul' e d := congrArg (fun f : SplitPinning.Iso p p => f.groupIso)
    (isoOfRootDatumEquiv_comp d.val e.val d.property e.property)

/-- The same based root-datum automorphisms act on the actual pinned torus. -/
def basedRootDatumAutTorusLift (p : SplitPinning G) :
    p.basedRootDatumAut →* CategoryTheory.Aut p.torus where
  toFun e := (p.isoOfBasedRootDatumAut e).torusIso
  map_one' := congrArg (fun f : SplitPinning.Iso p p => f.torusIso)
    (p.isoOfRootDatumEquiv_id)
  map_mul' e d := congrArg (fun f : SplitPinning.Iso p p => f.torusIso)
    (isoOfRootDatumEquiv_comp d.val e.val d.property e.property)

/-- The two lifted actions intertwine the actual torus inclusion. -/
theorem basedRootDatumAutLift_square (p : SplitPinning G) (e : p.basedRootDatumAut) :
    p.inclusion ≫ (p.basedRootDatumAutLift e).hom =
      CommGroupScheme.groupHom (p.basedRootDatumAutTorusLift e).hom ≫ p.inclusion :=
  (p.isoOfBasedRootDatumAut e).square

/-- The forward full character action is the given integral weight equivalence. -/
theorem basedRootDatumAutTorusLift_character (p : SplitPinning G)
    (e : p.basedRootDatumAut) :
    (characterLattice.congr (p.basedRootDatumAutTorusLift e)).toIntLinearEquiv =
      e.val.weightEquiv :=
  p.isoOfRootDatumEquiv_character p e.val e.property

/-- The forward cocharacter action is the inverse contravariant coweight map. -/
theorem basedRootDatumAutTorusLift_cocharacter (p : SplitPinning G)
    (e : p.basedRootDatumAut) :
    (cocharacterLattice.congr (p.basedRootDatumAutTorusLift e)).toIntLinearEquiv =
      e.val.coweightEquiv.symm :=
  p.isoOfRootDatumEquiv_cocharacter p e.val e.property

/-- Actual differentials carry each chosen simple-root vector to its prescribed vector. -/
theorem basedRootDatumAutLift_rootVector (p : SplitPinning G)
    (e : p.basedRootDatumAut) (a : p.base.support) :
    Lie.targetMapLinear (p.basedRootDatumAutLift e).hom (CommRingCat.of k)
        (p.pinning.rootVector a) =
      p.pinning.rootVector ⟨e.val.indexEquiv a, (e.property a).mp a.property⟩ := by
  change Lie.targetMapLinear (p.isoOfRootDatumEquiv p e.val e.property).groupIso.hom
      (CommRingCat.of k) (p.pinning.rootVector a) = _
  have h := (p.isoOfBasedRootDatumAut e).rootVector_eq a
  simpa only [isoOfBasedRootDatumAut, isoOfRootDatumEquiv_indexEquiv] using h

/-- Scalar extension of these field automorphisms remains a group homomorphism. -/
def basedRootDatumAutLiftBaseChange (p : SplitPinning G) {S : Scheme.{u}}
    (b : S ⟶ Spec (CommRingCat.of k)) :
    p.basedRootDatumAut →* CategoryTheory.Aut ((GroupScheme.baseChange b).obj G) :=
  ((GroupScheme.baseChange b).mapAut G).comp p.basedRootDatumAutLift

@[simp]
theorem basedRootDatumAutLiftBaseChange_apply (p : SplitPinning G) {S : Scheme.{u}}
    (b : S ⟶ Spec (CommRingCat.of k)) (e : p.basedRootDatumAut) :
    p.basedRootDatumAutLiftBaseChange b e =
      (GroupScheme.baseChange b).mapIso (p.basedRootDatumAutLift e) := rfl

end Langlands.GroupScheme.SplitPinning
