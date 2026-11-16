import Langlands.GroupScheme.Reductive.AffinePinnedLocalPinning
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: geometric fppf-local normalization of actual comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffinePinnedModel

/-- The local geometric existence input for canonical comparisons. An actual
comparison becomes the composite of a concretely pinned comparison and an
actual inner conjugation after an fppf cover. This statement asserts no
uniqueness, independence or natural choice of its local representatives. -/
def FppfLocalPinnedNormalizationExistenceStatement : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) {T : Scheme.{u}}
    (f : T ⟶ M.base) (g : T ⟶ N.base) (e : Comparison f g),
    ∃ (U : Scheme.{u}) (q : U ⟶ T),
      Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
        ∃ (d : Comparison (q ≫ f) (q ≫ g))
          (c : Over.mk (𝟙 U) ⟶ (M.groupOver (q ≫ f)).X),
          IsLocallyPinned d ∧
            (M.groupOver (q ≫ f)).innerIso c = pullComparison e q ≪≫ d.symm

end Langlands.GroupScheme
