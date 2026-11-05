import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Quasi-splitness over Henselian discretely valued fields -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Connected reductive groups over Henselian discretely valued fields with
algebraically closed residue field have field-defined geometric Borels. -/
def HenselianDiscreteQuasiSplitStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring) →
    ∀ (H : GroupScheme (Spec (CommRingCat.of K))),
      IsConnectedReductive H → IsQuasiSplit H

end Langlands.GroupScheme
