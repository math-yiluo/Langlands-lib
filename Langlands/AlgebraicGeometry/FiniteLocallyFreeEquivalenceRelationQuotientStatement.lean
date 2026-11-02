import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Quotients of schemes by finite locally free equivalence relations

The existence part of Stacks Project, Properties of Algebraic Spaces, Proposition 66.14.1
(Tag 07S6), when the equivalence class of every point lies in an affine open. The setting and
hypotheses are those of `Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Stacks Project, Properties of Algebraic Spaces, Proposition 66.14.1: let `t, s : R ⟶ U` be
such that `j = (t, s) : R ⟶ U × U` is a monomorphism whose `T`-valued points form an equivalence
relation on the `T`-valued points of `U` for every scheme `T`, and such that `t` and `s` are
finite locally free. If for every point `u` of `U` the equivalence class `t(s⁻¹({u}))` lies in
an affine open of `U`, then there are a scheme `M` and a finite locally free surjective morphism
`q : U ⟶ M` such that `(t, s)` identifies `R` with `U ×_M U`. -/
def FiniteLocallyFreeEquivalenceRelationQuotientStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U),
    Mono (prod.lift t s) →
    (∀ (T : Scheme.{u}) (a : T ⟶ U), ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a) →
    (∀ (T : Scheme.{u}) (r : T ⟶ R), ∃ r' : T ⟶ R, r' ≫ t = r ≫ s ∧ r' ≫ s = r ≫ t) →
    (∀ (T : Scheme.{u}) (r r' : T ⟶ R), r ≫ s = r' ≫ t →
      ∃ r'' : T ⟶ R, r'' ≫ t = r ≫ t ∧ r'' ≫ s = r' ≫ s) →
    IsFinite t → Flat t → LocallyOfFinitePresentation t →
    IsFinite s → Flat s → LocallyOfFinitePresentation s →
    (∀ u : U, ∃ W : U.Opens, IsAffineOpen W ∧ ∀ r : R, s r = u → t r ∈ W) →
    ∃ (M : Scheme.{u}) (q : U ⟶ M), IsPullback t s q q ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q

end Langlands.AlgebraicGeometry
