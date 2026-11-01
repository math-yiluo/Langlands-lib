import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Étale equivalence relations on schemes

Presentations of algebraic spaces by étale equivalence relations, in the absolute setting:
schemes over `Spec ℤ`, so that `U × U` is the categorical product of schemes. We follow the
Stacks Project conventions `j = (t, s) : R → U × U` (Tags 022P and 02WS), representable
quotients (Tags 03BD and 03C5) and cartesian morphisms (Tag 0APD).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- An étale equivalence relation on a scheme `U` (Stacks Tags 022P and 02WS, over
`Spec ℤ`): a morphism `j = (t, s) : R ⟶ U × U` that is a monomorphism, whose `T`-valued
points form an equivalence relation on the `T`-valued points of `U` for every scheme `T`,
and whose projections `t` and `s` are étale. -/
structure EtaleEquivalenceRelation where
  /-- The scheme on which the relation lives. -/
  U : Scheme.{u}
  /-- The scheme of related pairs. -/
  R : Scheme.{u}
  /-- The first projection `t = pr₀ ∘ j`. -/
  t : R ⟶ U
  /-- The second projection `s = pr₁ ∘ j`. -/
  s : R ⟶ U
  /-- The morphism `j = (t, s) : R ⟶ U × U` is a monomorphism. -/
  mono_lift : Mono (prod.lift t s)
  /-- Reflexivity on `T`-valued points: every pair `(a, a)` lies in `R`. -/
  refl : ∀ (T : Scheme.{u}) (a : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a
  /-- Symmetry on `T`-valued points: with `(t r, s r)` the pair `(s r, t r)` lies in `R`. -/
  symm : ∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t
  /-- Transitivity on `T`-valued points: `(x, y)` and `(y, z)` in `R` give `(x, z)` in `R`. -/
  trans : ∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
    ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s
  /-- The first projection is étale. -/
  etale_t : Etale t
  /-- The second projection is étale. -/
  etale_s : Etale s

namespace EtaleEquivalenceRelation

/-- The quotient `U/R` is represented by an affine scheme (Stacks Tags 03BD and 03C5): there
are an affine scheme `M` and a flat, locally finitely presented, surjective morphism
`q : U ⟶ M` such that `(t, s)` identifies `R` with `U ×_M U`. -/
def HasAffineQuotient (E : EtaleEquivalenceRelation.{u}) : Prop :=
  ∃ (M : Scheme.{u}) (q : E.U ⟶ M), IsAffine M ∧ IsPullback E.t E.s q q ∧
    Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q

/-- A cartesian morphism `(f, g) : E' ⟶ E` of étale equivalence relations (Stacks Tag 0APD):
`f : E'.U ⟶ E.U` and `g : E'.R ⟶ E.R` commute with both projections, and the square formed by
`g`, the second projections `E'.s` and `E.s`, and `f` is a pullback. -/
def IsCartesianHom (E' E : EtaleEquivalenceRelation.{u}) (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R) :
    Prop :=
  g ≫ E.t = E'.t ≫ f ∧ IsPullback g E'.s E.s f

/-- `E` has a finite surjective cartesian cover by an étale equivalence relation with an
affine quotient: there are such an `E'` and a cartesian morphism `(f, g) : E' ⟶ E` whose
component `f` on the underlying schemes is finite and surjective. -/
def HasFiniteSurjectiveCoverWithAffineQuotient (E : EtaleEquivalenceRelation.{u}) : Prop :=
  ∃ (E' : EtaleEquivalenceRelation.{u}) (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R),
    IsCartesianHom E' E f g ∧ IsFinite f ∧ Surjective f ∧ E'.HasAffineQuotient

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
