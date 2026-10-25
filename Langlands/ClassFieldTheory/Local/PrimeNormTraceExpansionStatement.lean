import Langlands.LocalField.Canonical
import Langlands.LocalField.Normalization.Definitions
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

/-! The prime-degree norm expansion with an actual trace preimage. -/

namespace Langlands.LocalClassField

universe u v

/-- Serre V.3, Lemma 5, in the canonical totally ramified p-adic setting. -/
def PrimeNormTraceExpansion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        ∀ (n : ℕ) (x : TL.Integers),
          x ∈ (IsLocalRing.maximalIdeal TL.Integers) ^ n →
            ∃ z : TL.Integers,
              z ∈ (IsLocalRing.maximalIdeal TL.Integers) ^ (2 * n) ∧
                Algebra.norm F.Carrier (1 + (x : L.Carrier)) - 1 -
                    Algebra.trace F.Carrier L.Carrier (x : L.Carrier) -
                    Algebra.norm F.Carrier (x : L.Carrier) =
                  Algebra.trace F.Carrier L.Carrier (z : L.Carrier)

end Langlands.LocalClassField
