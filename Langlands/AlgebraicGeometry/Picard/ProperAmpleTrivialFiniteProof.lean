import Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteStatement
import Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineProof

/-! # Finiteness of a proper field scheme with an ample trivial line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

private theorem finite_of_proper_of_quasiAffine {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsAffine Y] [X.IsQuasiAffine] : IsFinite f := by
  have : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  have : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map f.appTop)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion X.toSpecΓ X.toSpecΓ.isClosedMap.isClosed_range
  have : IsAffine X := isAffine_of_isAffineHom X.toSpecΓ
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-- A proper scheme over a field with an ample trivial line bundle is finite. -/
theorem properAmpleTrivialFinite : ProperAmpleTrivialFiniteStatement.{u} := by
  intro K _ X f L hf hL he
  have : IsProper f := hf
  have : X.IsQuasiAffine := ampleTrivialQuasiAffine X L hL he
  exact finite_of_proper_of_quasiAffine f

end Langlands.AlgebraicGeometry.Picard
