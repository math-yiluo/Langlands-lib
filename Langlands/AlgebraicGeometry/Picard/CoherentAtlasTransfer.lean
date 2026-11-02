import Langlands.AlgebraicGeometry.Picard.CoherentAtlasRestriction
import Langlands.AlgebraicGeometry.Picard.CoherentFamilyComparison
import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement
import Langlands.AlgebraicGeometry.CoherentSheaves.FieldCoherentStackAtlasStatement
import Langlands.CategoryTheory.Sites.PseudofunctorHomLiftStrongTrans
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual transfer of coherent-family atlases to Picard atlases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open CoherentSheaves Langlands.CategoryTheory.PseudofunctorHomLift
open Langlands.CategoryTheory.PseudofunctorPointFiberTransport

namespace PicardGroupoid

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]

/-- The actual coherent-family inclusion through the explicit hom lift. -/
def toFamilyHomLiftStrongTrans :
    Pseudofunctor.StrongTrans (relativeHomLift f)
      (homLift.{u + 1} (FamilyGroupoid.pseudofunctor f)) :=
  homLiftStrongTrans.{u + 1} (toFamilyStrongTrans f)

/-- Every lifted component remains fully faithful. -/
def toFamilyHomLiftStrongTransFullyFaithful (T : Over S) :
    (component (toFamilyHomLiftStrongTrans f) T).FullyFaithful :=
  homLiftStrongTransFullyFaithful (toFamilyStrongTrans f)
    (toFamilyStrongTransFullyFaithful f) T

/-- The lifted inclusion retains precisely the original actual family. -/
lemma toFamilyHomLiftStrongTrans_obj (T : Over S)
    (η : (relativeHomLift f).obj (.mk (op T))) :
    (component (toFamilyHomLiftStrongTrans f) T).obj η =
      ULiftHom.objUp.{u + 1, u + 1}
        ((relativeToFamily f T).obj (ULiftHom.objDown.{u + 1, u + 1} η)) := rfl

/-- The rank-one open of any actual coherent-family atlas gives an actual
Picard atlas, using the constructed inclusion rather than supplied data. -/
lemma hasLocallyFiniteTypeSmoothSchemeAtlas_of_familyAtlas
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (h : Stacks.HasLocallyFiniteTypeSmoothSchemeAtlas
      (homLift.{u + 1} (FamilyGroupoid.pseudofunctor f))) :
    HasLocallyFiniteTypeSmoothSchemeAtlas f :=
  hasLocallyFiniteTypeSmoothSchemeAtlas_of_coherentAtlas f
    (toFamilyHomLiftStrongTrans f)
    (toFamilyHomLiftStrongTransFullyFaithful f)
    (toFamilyHomLiftStrongTrans_obj f) h

end PicardGroupoid

/-- Coherent-family atlas existence over every field implies the exact
Picard-atlas statement, with all auxiliary geometric properties derived. -/
lemma fieldPicardStackAtlas_of_coherentStackAtlas
    (h : CoherentSheaves.FieldCoherentStackAtlasStatement.{u}) :
    FieldPicardStackAtlasStatement.{u} := by
  intro k hk X hX
  let : IsProper X.hom := hX
  exact PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_familyAtlas
    X.hom (h k X hX)

end Langlands.AlgebraicGeometry.Picard
