import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Étale morphisms of schemes are locally quasi-finite -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Etale morphisms are locally quasi-finite. -/
lemma locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := HasRingHomProperty.appLE @Etale f inferInstance U V e
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.Etale Γ(Y, U) Γ(X, V) := h
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end Langlands.AlgebraicGeometry
