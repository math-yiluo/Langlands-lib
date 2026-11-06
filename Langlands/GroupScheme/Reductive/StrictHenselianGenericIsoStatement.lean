import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing

/-! # Generic-fibre determination over strictly Henselian local domains -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Reductive groups over a strictly Henselian local domain with isomorphic
fraction-field fibres are abstractly isomorphic over the original ring. -/
def StrictHenselianGenericIsoStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    Nonempty (((GroupScheme.baseChange (Spec.algebraMap R K)).obj G) ≅
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H)) →
    Nonempty (G ≅ H)

end Langlands.GroupScheme
