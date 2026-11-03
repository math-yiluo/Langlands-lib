import Langlands.GroupScheme.Products
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Geometric-integrality prerequisites for actual group schemes -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine group over any field is geometrically integral.
This is a proposition target, not an assumed instance. -/
def SmoothConnectedAffineGroupIntegralStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))),
    Smooth H.X.hom → IsAffineHom H.X.hom → ConnectedSpace H.X.left →
      GeometricallyIntegral H.X.hom

/-- The actual product of two smooth connected affine groups is an affine,
finite-type, geometrically integral source for the commutator morphism. -/
def SmoothConnectedAffineProductIntegralStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H₁ H₂ : GroupScheme (Spec (CommRingCat.of k))),
    Smooth H₁.X.hom → IsAffineHom H₁.X.hom → ConnectedSpace H₁.X.left →
    Smooth H₂.X.hom → IsAffineHom H₂.X.hom → ConnectedSpace H₂.X.left →
      IsAffineHom (H₁.X ⊗ H₂.X).hom ∧
      LocallyOfFiniteType (H₁.X ⊗ H₂.X).hom ∧
      QuasiCompact (H₁.X ⊗ H₂.X).hom ∧
      GeometricallyIntegral (H₁.X ⊗ H₂.X).hom

/-- The basic geometric-integrality obligations for the general
pointed-image and commutator constructions. -/
def SmoothConnectedAffineGeometryStatement : Prop :=
  SmoothConnectedAffineGroupIntegralStatement.{u} ∧
    SmoothConnectedAffineProductIntegralStatement.{u}

end Langlands.GroupScheme
