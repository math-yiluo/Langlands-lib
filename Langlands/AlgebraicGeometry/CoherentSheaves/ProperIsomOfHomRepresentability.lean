import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineFinitePresentationRepresentable
import Langlands.AlgebraicGeometry.CoherentSheaves.IsomHomEqualizer
import Langlands.AlgebraicGeometry.CoherentSheaves.ProperHomRepresentabilityStatement
import Langlands.AlgebraicGeometry.CoherentSheaves.ProperIsomRepresentabilityStatement

/-!
# Isom representability from Hom representability

If every actual Hom presheaf of two coherent families is represented by an affine
scheme locally of finite presentation over the test base, then so is every actual
Isom presheaf: the Isom presheaf is the equalizer of two maps between binary
products of Hom presheaves.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.CoherentSheaves

open AlgebraicSpace

/-- Proper-Hom representability implies proper-Isom representability. -/
theorem properIsomRepresentability_of_properHomRepresentability
    (h : ProperHomRepresentabilityStatement.{u}) :
    ProperIsomRepresentabilityStatement.{u} := by
  intro S X f hP hL T M N
  have hHom : ∀ M' N' : FamilyGroupoid f T,
      IsAffineFinitePresentationRepresentable (FamilyGroupoid.homPresheaf f M' N') :=
    fun M' N' ↦ h S X f hP hL T M' N'
  have hPair := IsAffineFinitePresentationRepresentable.of_isLimit_binaryFan
    (hHom M N) (hHom N M) (FunctorToTypes.binaryProductLimit _ _)
  have hEnd := IsAffineFinitePresentationRepresentable.of_isLimit_binaryFan
    (hHom M M) (hHom N N) (FunctorToTypes.binaryProductLimit _ _)
  exact IsAffineFinitePresentationRepresentable.of_isLimit_fork hPair hEnd
    (FamilyGroupoid.isomPairForkIsLimit f M N)

end Langlands.AlgebraicGeometry.CoherentSheaves
