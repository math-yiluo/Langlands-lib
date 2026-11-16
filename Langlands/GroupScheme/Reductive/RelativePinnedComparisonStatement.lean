import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: natural inner corrections of comparisons of pinned models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open AffinePinnedModel

/-- A supplied natural comparison operation on affine pinned split models.
Its outputs preserve the chosen torus and positive-coroot cocharacter; the
original comparison differs from its output by an adjoint-point action.
The common test schemes and their refinements are arbitrary. -/
structure RelativePinnedComparison where
  compare : ∀ (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base), Comparison f g → Comparison f g
  compare_refl : ∀ (M : AffinePinnedModel.{u}) (T : Scheme.{u}) (f : T ⟶ M.base),
    compare M M f f (Iso.refl (M.groupOver f)) = Iso.refl _
  compare_trans : ∀ (M N K : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (h : T ⟶ K.base)
    (e : Comparison f g) (d : Comparison g h),
    compare M K f h (e ≪≫ d) = compare M N f g e ≪≫ compare N K g h d
  compare_pull : ∀ (M N : AffinePinnedModel.{u}) (T W : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g) (q : W ⟶ T),
    compare M N (q ≫ f) (q ≫ g) (pullComparison e q) =
      pullComparison (compare M N f g e) q
  torus : ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    ∃ τ : splitTorus T M.coordinates ≅ splitTorus T N.coordinates,
      M.inclusionOver f ≫ (compare M N f g e).hom = τ.hom ≫ N.inclusionOver g
  cocharacter : ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    M.cocharacterOver f ≫ (compare M N f g e).hom = N.cocharacterOver g
  inner : ∀ (M N : AffinePinnedModel.{u}) (T : Scheme.{u})
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g)
    (A : GroupScheme T) (p : M.groupOver f ⟶ A),
    RelativeRoot.IsFppfQuotient (center (M.groupOver f)) p →
    ∀ c : AutomorphicAction A (M.groupOver f),
      c.restrict p = AutomorphicAction.conjugation (𝟙 (M.groupOver f)) →
      ∃ x : Over.mk (𝟙 T) ⟶ A.X,
        c.basePointIso x = e ≪≫ (compare M N f g e).symm

/-- The relative pinning splitting in the form needed for invariant overlap
comparisons. This is a consequence of the pinned Isomorphism Theorem and the
sheaf-level splitting of automorphisms (Conrad, Theorems 6.1.17 and 7.1.9(3)),
allowing locally varying outer classes on arbitrary schemes. -/
def RelativePinnedComparisonExistenceStatement : Prop :=
  Nonempty RelativePinnedComparison.{u}

end Langlands.GroupScheme
