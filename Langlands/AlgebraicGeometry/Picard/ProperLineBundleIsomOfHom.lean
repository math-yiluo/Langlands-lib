import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationRepresentable
import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.CoherentSheaves.IsomHomEqualizer
import Langlands.AlgebraicGeometry.CoherentSheaves.IsomPresheaf
import Langlands.AlgebraicGeometry.Picard.CoherentFamilyComparison
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleHomRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomRepresentabilityStatement
import Langlands.CategoryTheory.Sites.PseudofunctorPresheafHomTransport

/-!
# Line-bundle Isom representability from line-bundle Hom representability

For a flat ambient morphism, the full-slice Isom presheaf of two actual
line-bundle families is naturally isomorphic to the Isom presheaf of the
corresponding coherent families. The latter is the equalizer of two maps between
binary products of Hom presheaves, and each of those Hom presheaves is the
ordinary module Hom presheaf of two line bundles.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace CoherentSheaves

namespace PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) [Flat f] {T : Over S}

/-- The presheaf of groupoid arrows between two line bundles in the relative
Picard pseudofunctor agrees with that of their coherent-family images. -/
def relativePresheafHomFamilyIso (L M : PicardGroupoid ((relativeSpace f).obj T)) :
    (relative f).presheafHom L M ≅
      (FamilyGroupoid.pseudofunctor f).presheafHom
        ((relativeToFamily f T).obj L) ((relativeToFamily f T).obj M) :=
  CategoryTheory.PseudofunctorPresheafHomTransport.presheafHomIso
    (toFamilyStrongTrans f) L M (toFamilyStrongTransFullyFaithful f)

/-- The actual line-bundle Isom presheaf agrees, on the entire test slice and
with all its restriction maps, with the actual Isom presheaf of the included
coherent families. -/
def relativeIsomPresheafFamilyIso (L M : PicardGroupoid ((relativeSpace f).obj T)) :
    relativeIsomPresheaf f L M ≅
      FamilyGroupoid.isomPresheaf f ((relativeToFamily f T).obj L)
        ((relativeToFamily f T).obj M) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft T.iteratedSliceBackward.op
        (CategoryTheory.PseudofunctorPresheafHomTransport.presheafHomIso
          (toFamilyStrongTrans f) L M (fun Z ↦ toFamilyStrongTransFullyFaithful f Z)))
      uliftFunctor.{u + 1} ≪≫
    (FamilyGroupoid.isomPresheafLiftIso f _ _).symm

end PicardGroupoid

/-- Line-bundle Hom representability implies line-bundle Isom representability. -/
theorem properLineBundleIsomRepresentability_of_hom
    (h : ProperLineBundleHomRepresentabilityStatement.{u}) :
    ProperLineBundleIsomRepresentabilityStatement.{u} := by
  intro S X f hP hF hL T L M
  have hHom : ∀ L₁ L₂ : PicardGroupoid ((relativeSpace f).obj T),
      IsAffineFinitePresentationRepresentable
        (FamilyGroupoid.homPresheaf f ((PicardGroupoid.relativeToFamily f T).obj L₁)
          ((PicardGroupoid.relativeToFamily f T).obj L₂)) := fun L₁ L₂ ↦
    IsAffineFinitePresentationRepresentable.of_iso (h S X f hP hF hL T L₁ L₂)
      (FamilyGroupoid.homPresheafIntrinsicIso f T
        ((PicardGroupoid.relativeToFamily f T).obj L₁)
        ((PicardGroupoid.relativeToFamily f T).obj L₂)).symm
  have hPair := IsAffineFinitePresentationRepresentable.of_isLimit_binaryFan
    (hHom L M) (hHom M L) (FunctorToTypes.binaryProductLimit _ _)
  have hEnd := IsAffineFinitePresentationRepresentable.of_isLimit_binaryFan
    (hHom L L) (hHom M M) (FunctorToTypes.binaryProductLimit _ _)
  exact IsAffineFinitePresentationRepresentable.of_iso
    (IsAffineFinitePresentationRepresentable.of_isLimit_fork hPair hEnd
      (FamilyGroupoid.isomPairForkIsLimit f _ _))
    (PicardGroupoid.relativeIsomPresheafFamilyIso f L M).symm

/-- Affine finitely presented representability of actual line-bundle Hom implies
that of actual line-bundle Isom, on the whole test slice. -/
theorem properLineBundleIsomRepresentability_of_properLineBundleHomRepresentability
    (h : ProperLineBundleHomRepresentabilityStatement.{u}) :
    ProperLineBundleIsomRepresentabilityStatement.{u} :=
  properLineBundleIsomRepresentability_of_hom h

end Langlands.AlgebraicGeometry.Picard
