import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing

/-! # Splitting and quasi-splitting from the special fibre over a henselian DVR -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Conrad, Exercise 5.5.3(ii): for a reductive group scheme over a henselian
discrete valuation ring, if the special fibre is quasi-split (resp. split), then so
is the generic fibre. Split means having a split maximal torus. -/
def HenselianDiscreteSpecialFibreSplitStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G →
      let G₀ := (GroupScheme.baseChange
        (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G
      let G_K := (GroupScheme.baseChange (Spec.algebraMap R K)).obj G
      (IsQuasiSplit G₀ → IsQuasiSplit G_K) ∧
      ((∃ (T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
          (i : T.toGrp ⟶ G₀), IsSplitTorus T.toGrp ∧ IsMaximalTorus i) →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G_K),
          IsSplitTorus T.toGrp ∧ IsMaximalTorus i)

end Langlands.GroupScheme
