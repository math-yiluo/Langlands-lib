import Langlands.GroupScheme.Reductive.CharacteristicZeroInvariantIntegralStatement
import Langlands.GroupScheme.Reductive.CharacteristicZeroVectorExtensionStatement
import Langlands.GroupScheme.Rational.InvariantIntegralVectorExtension
import Langlands.GroupScheme.Rational.AffineVectorExtension
import Langlands.GroupScheme.Rational.VectorActionCharZero

/-! # Characteristic-zero vector extensions with invariant integration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace InvariantIntegralVectorExtension

variable {k : Type u} [Field k] [CharZero k]
    {E H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsAffineHom H.X.hom]
    (q : E ⟶ H) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    {d : ℕ} (hV : RelativeRoot.IsVectorGroupOfDimension (kernel q) d)
    (I : CoordinateIntegration.InvariantIntegral H)

include hV I

/-- In characteristic zero, a normalized invariant integral splits every affine
faithfully flat extension with a full finite-dimensional vector kernel. -/
theorem exists_extensionSection_of_charZero :
    ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  let : IsAffineHom (kernel q).X.hom := hV.isAffineHom
  obtain ⟨s, hs⟩ := hV.exists_quotientSection (kernelι q) q rfl
  obtain ⟨e, he⟩ := hV
  have hlin := RelativeRoot.isLinearVectorCoordinates_of_charZero
    (b := VectorExtensionDescent.action (kernelι q) q rfl) (e := e) he
  exact ⟨extensionSection (kernelι q) q rfl s hs e I hlin,
    extensionSection_comp (kernelι q) q rfl s hs e I hlin⟩

/-- The chosen original-field homomorphic section from invariant integration. -/
def vectorKernelSectionOfInvariantIntegral : H ⟶ E :=
  Classical.choose (exists_extensionSection_of_charZero q hV I)

/-- The chosen homomorphism splits the supplied quotient. -/
theorem vectorKernelSectionOfInvariantIntegral_comp :
    vectorKernelSectionOfInvariantIntegral q hV I ≫ q = 𝟙 H :=
  Classical.choose_spec (exists_extensionSection_of_charZero q hV I)

end InvariantIntegralVectorExtension

/-- The reductive invariant-integral existence proposition implies the unchanged
characteristic-zero vector-extension splitting proposition. -/
theorem characteristicZeroReductiveVectorExtension_of_invariantIntegral
    (hI : CharacteristicZeroReductiveInvariantIntegralStatement.{u}) :
    CharacteristicZeroReductiveVectorExtensionStatement.{u} := by
  intro k _ _ E H _ q _ _ hH d hV
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨I⟩ := hI k H hH
  exact InvariantIntegralVectorExtension.exists_extensionSection_of_charZero q hV I

end Langlands.GroupScheme
