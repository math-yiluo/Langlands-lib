import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The structure map from an affine base to sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- The base ring action on the sections of an open of the actual scheme. -/
def baseSectionHom (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

end Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient
