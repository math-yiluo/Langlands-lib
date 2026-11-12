import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentStatement
import Langlands.AlgebraicGeometry.SchemeFiberGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Descent of flatness and of fibral pure dimension for algebraic spaces

Conrad, printed p.13: Theorem 3.4 holds with finitely presented algebraic spaces in place of
finitely presented schemes. This file defines flat morphisms of algebraic spaces and morphisms
whose fibres are pure of dimension `d`, through étale scheme charts, and states part (2) of
Theorem 3.4 for flatness and for the property "fibres nonempty and geometrically connected of
pure dimension `d`".
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A morphism is flat when there is a commutative square from a flat scheme morphism
`φ : U ⟶ V`, with `h_U ⟶ X` étale and surjective and `h_V ⟶ Y` étale, following the étale
local definition of flatness in the Stacks Project chapter "Morphisms of Algebraic Spaces". -/
def IsFlatMorphism (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V),
    IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ Flat φ.left ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b

/-- The fibres of a morphism are pure of dimension `d` when there is a commutative square from
a scheme morphism `φ : U ⟶ V` locally of finite type, with `h_U ⟶ X` étale and surjective and
`h_V ⟶ Y` étale, whose residue-field fibres are all pure of dimension `d`. -/
def HasPureFibreDimension (d : ℕ) (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : U ⟶ V),
    IsEtale a ∧ IsSurjective a ∧ IsEtale b ∧ LocallyOfFiniteType φ.left ∧
      (∀ v : V.left, SchemeFiberGeometry.HasPureDimension (φ.left.fiber v) d) ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b

/-- Conrad's Theorem 3.4(2) for finitely presented algebraic spaces (printed p.13), for
flatness and for every `d` the property "fibres nonempty and geometrically connected of pure
dimension `d`". -/
def SpaceLimitFlatnessDimensionDescentStatement : Prop :=
  SpaceLimitPropertyDescends.{u} (fun f => IsFlatMorphism f) ∧
    ∀ d : ℕ, SpaceLimitPropertyDescends.{u}
      (fun f => HasGeometricallyConnectedFibres f ∧ HasPureFibreDimension d f)

end Langlands.AlgebraicGeometry.AlgebraicSpace
