import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Anisotropic absolutely almost-simple groups over local fields have inner type A

This module states, on actual Tits-index data, the two local arithmetic facts
behind Bruhat–Tits (1967), Proposition 6: over a nonarchimedean local field an
anisotropic absolutely almost-simple group has type `A_n`, and a simply connected
one of type `A_n` has trivial star action. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a nonarchimedean local field, the actual index of an affine anisotropic
absolutely almost-simple group has type `A_n` for some positive `n`: its actual
simple vertices admit a numbering by `Fin n` carrying the actual Cartan pairings
to the type-`A` Cartan matrix. No condition on the star action is asserted. -/
def LocalAnisotropicTypeAStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsAbsolutelyAlmostSimple G → IsAnisotropic G →
      ∃ n : ℕ, 0 < n ∧ ∃ e : d.Vertex ≃ Fin n,
        ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)

/-- Over a nonarchimedean local field, if the actual index of an affine anisotropic
simply connected absolutely almost-simple group has type `A_n`, then every element
of the absolute Galois group acts trivially on its simple vertices through the
actual star action. Equivalently, simply connected groups of outer type `A_n` over
such fields are isotropic. -/
def LocalAnisotropicTypeAInnerStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → IsAnisotropic G →
      (∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
        ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
          d.star σ a = a

/-- Both local statements. Together they say that the actual index of every affine
anisotropic simply connected absolutely almost-simple group over a nonarchimedean
local field is of inner type `A_n` for some positive `n`. -/
def LocalAnisotropicInnerTypeAStatement : Prop :=
  LocalAnisotropicTypeAStatement.{u} ∧ LocalAnisotropicTypeAInnerStatement.{u}

end Langlands.GroupScheme
