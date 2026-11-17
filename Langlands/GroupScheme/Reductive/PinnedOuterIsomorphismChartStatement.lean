import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.OuterIsomorphismScheme
import Mathlib.AlgebraicGeometry.Limits

/-! # Constant outer charts for two pinned split reductive models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A pinned split pair has a complete family of outer representatives indexed
by an actual constant scheme, with a unique adjoint discrepancy on every test. -/
def PinnedOuterIsomorphismChartStatement : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (S : Scheme.{u})
    (f : S ⟶ M.base) (g : S ⟶ N.base)
    (A : GroupScheme S) (q : M.groupOver f ⟶ A)
    (hq : IsRelativeAdjointQuotient q)
    (I : GroupIsomorphismScheme (M.groupOver f) (N.groupOver g)),
    ∃ (D : Type u)
      (s : Over.mk (Sigma.desc (fun _ : D => 𝟙 S)) ⟶ I.parameter),
      ∀ (T : Over S), Function.Bijective
        (fun z : (T ⟶ A.X) ×
            (T ⟶ Over.mk (Sigma.desc (fun _ : D => 𝟙 S))) =>
          lift z.1 (z.2 ≫ s) ≫ I.actionHom hq.innerAction)

end Langlands.GroupScheme
