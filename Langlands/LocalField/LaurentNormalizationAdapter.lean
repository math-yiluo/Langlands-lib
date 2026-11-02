import Langlands.LocalField.NormalizationConsumer
import Langlands.LocalField.LaurentSeries

/-! # The p-adic and Laurent-series fields as instances of one consumer -/

universe u v

namespace Langlands.LocalField.Laurent

attribute [local instance] valuativeRel

variable (k : Type u) [Field k] [Finite k]

/-- The actual X-adic Laurent-series field instantiates the common consumer at `Nat.card k`. -/
theorem normalizedAt : NormalizedAt (LaurentSeries k) (Nat.card k) :=
  (normalizedAt_iff (LaurentSeries k) _).mpr (residueCardinality_eq k)

/-- Integer powers of an order-one Laurent series have absolute value `(Nat.card k) ^ (-n)`. -/
theorem residueNormalizedAbsoluteValue_zpow_of_ord_one {π : LaurentSeries k}
    (hπ : FML.ord (LaurentSeries k) π = 1) (n : ℤ) :
    residueNormalizedAbsoluteValue (LaurentSeries k) (π ^ n) = (Nat.card k : ℝ) ^ (-n) :=
  (normalizedAt k).2.2 π hπ n

end Langlands.LocalField.Laurent

namespace Langlands.LocalField

/-- The canonical realization of every p-adic field and the X-adic Laurent-series field
over every finite field instantiate the same consumer at their residue cardinalities. -/
def PadicLaurentNormalized : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (k : Type v) [Field k] [Finite k],
    (letI := F.canonicalTopologicalData.topology; letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      NormalizedAt F.Carrier F.canonicalTopologicalData.residueCardinality) ∧
    (letI := Laurent.valuativeRel k; NormalizedAt (LaurentSeries k) (Nat.card k))

theorem padicLaurentNormalized : PadicLaurentNormalized.{u, v} :=
  fun _ _ F k _ _ => ⟨F.canonical_normalizedAt, Laurent.normalizedAt k⟩

end Langlands.LocalField
