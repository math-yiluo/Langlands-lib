import Langlands.AbelianScheme.Isogeny
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing

/-! # Prescribed-map isogeny rigidity over a strictly Henselian DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The generic fibre of a fibrewise isogeny between reductive groups over a strictly
Henselian discrete valuation ring is an isomorphism if its special fibre is an
isomorphism. This refers to the specified homomorphism, rather than an abstract
isomorphism of the generic-fibre groups. -/
def StrictHenselianDVRIsogenyRigidityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ f : G ⟶ H,
      (∀ s : Spec (CommRingCat.of R),
        IsIsogeny ((GroupScheme.baseChange
          ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map f)) →
      IsIso ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map f) →
      IsIso ((GroupScheme.baseChange (Spec.algebraMap R K)).map f)

end Langlands.GroupScheme
