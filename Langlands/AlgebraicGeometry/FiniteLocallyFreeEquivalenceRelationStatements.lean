import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Finite locally free equivalence relations on schemes

Two statements from the Stacks Project, Groupoids: Proposition 39.23.9 (Tag 03BM) and
Lemma 39.24.1 (Tag 03JE), in the absolute setting: schemes over `Spec ℤ`, so that `U × U` is
the categorical product of schemes, as in `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`.
A finite locally free morphism is a finite, flat morphism locally of finite presentation.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Stacks Project, Groupoids, Proposition 39.23.9: let `t, s : R ⟶ U` be such that
`j = (t, s) : R ⟶ U × U` is a monomorphism whose `T`-valued points form an equivalence relation
on the `T`-valued points of `U` for every scheme `T`, and such that `t` and `s` are finite
locally free. If `U` is affine, then there are an affine scheme `M` and a finite locally
free surjective morphism `q : U ⟶ M` such that `(t, s)` identifies `R` with `U ×_M U`. -/
def FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U),
    Mono (prod.lift t s) →
    (∀ (T : Scheme.{u}) (a : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a) →
    (∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t) →
    (∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
      ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s) →
    IsFinite t → Flat t → LocallyOfFinitePresentation t →
    IsFinite s → Flat s → LocallyOfFinitePresentation s →
    IsAffine U →
    ∃ (M : Scheme.{u}) (q : U ⟶ M), IsAffine M ∧ IsPullback t s q q ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q

/-- Stacks Project, Groupoids, Lemma 39.24.1, for a finite set of points: let `t, s : R ⟶ U`
be as in `FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement`, without any
affineness assumption on `U`. Let `E` be a finite set of points of `U` such that every point
`t r` with `s r ∈ E` lies in an affine open `W` of `U`. Then some affine open `V` of `U`
contains `E` and is `R`-invariant: `s⁻¹(V) = t⁻¹(V)`. -/
def FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U),
    Mono (prod.lift t s) →
    (∀ (T : Scheme.{u}) (a : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a) →
    (∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t) →
    (∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
      ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s) →
    IsFinite t → Flat t → LocallyOfFinitePresentation t →
    IsFinite s → Flat s → LocallyOfFinitePresentation s →
    ∀ (E : Set U) (W : U.Opens), E.Finite → IsAffineOpen W →
      (∀ r : R, s r ∈ E → t r ∈ W) →
      ∃ V : U.Opens, IsAffineOpen V ∧ E ⊆ (V : Set U) ∧ s ⁻¹ᵁ V = t ⁻¹ᵁ V

end Langlands.AlgebraicGeometry
