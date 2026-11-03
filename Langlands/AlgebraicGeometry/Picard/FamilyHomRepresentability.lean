import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationRepresentable
import Langlands.AlgebraicGeometry.Picard.CoherentFamilyInclusion
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentabilityStatement

/-! # Hom representation for the coherent-family images of line bundles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open CoherentSheaves AlgebraicSpace

variable {S X : Scheme.{u}} (f : X ⟶ S) [Flat f] (T : Over S)
  (L M : PicardGroupoid ((relativeSpace f).obj T))

/-- The Hom presheaf between image families is the intrinsic Hom presheaf
of the original line-bundle modules, naturally on the whole slice. -/
def relativeFamilyHomIntrinsicIso :
    FamilyGroupoid.homPresheaf f
        ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M) ≅
      intrinsicModuleHomPresheaf ((relativeProjection f).app T)
        L.of.obj M.of.obj :=
  FamilyGroupoid.homPresheafIntrinsicIso f T
    ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M)

/-- Affine finite-presentation representation is equivalent for the two
entire presheaves, with the same geometric scope. -/
theorem relativeFamilyHomRepresentable_iff :
    IsAffineFinitePresentationRepresentable
        (FamilyGroupoid.homPresheaf f
          ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M)) ↔
      IsAffineFinitePresentationRepresentable
        (intrinsicModuleHomPresheaf ((relativeProjection f).app T)
          L.of.obj M.of.obj) :=
  ⟨fun h => h.of_iso (relativeFamilyHomIntrinsicIso f T L M),
    fun h => h.of_iso (relativeFamilyHomIntrinsicIso f T L M).symm⟩

/-- A focused proper line-bundle Hom theorem supplies every Hom pair needed
by the inverse-equation construction for the image families. -/
theorem relativeFamilyHomRepresentable_of_properLineBundleHomRepresentability
    (h : ProperLineBundleHomRepresentabilityStatement.{u})
    [IsProper f] [LocallyOfFinitePresentation f] :
    IsAffineFinitePresentationRepresentable
      (FamilyGroupoid.homPresheaf f
        ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M)) :=
  (relativeFamilyHomRepresentable_iff f T L M).mpr
    (h S X f inferInstance inferInstance inferInstance T L M)

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
