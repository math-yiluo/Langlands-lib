import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Quasi-affine morphisms of schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ S` is quasi-affine if the inverse image of every affine
open of `S` is a quasi-affine scheme (Stacks Project, Definition 29.13.1, Tag 01SK).
Quasi-affine schemes are Mathlib's `Scheme.IsQuasiAffine`: quasi-compact schemes whose
canonical map to the spectrum of global sections is an immersion. -/
def IsQuasiAffineOver {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ V : S.affineOpens, (f ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine

end Langlands.AlgebraicGeometry
