import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic

/-! # Generic reductivity on a principal open -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth affine group over a Noetherian domain with connected reductive
fraction-field fibre has connected reductive fibres at every field-valued point
of some nonempty principal open. -/
def GenericReductivitySpreadingStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    IsConnectedReductive ((baseChange (Spec.algebraMap R K)).obj G) →
    ∃ r : R, r ≠ 0 ∧
      ∀ (k : Type u) [Field k] [Algebra R k], algebraMap R k r ≠ 0 →
        IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj G)

end Langlands.GroupScheme
