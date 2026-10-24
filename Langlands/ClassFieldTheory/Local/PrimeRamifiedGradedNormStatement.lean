import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.LocalField.RelativeIntegers
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Trace.Basic

/-! Actual norm containments and residue formulas at a prime ramification break. -/

namespace Langlands.LocalClassField

universe u v

/-- The prime totally ramified graded norm, using actual residue coordinates
and exact trace/norm representatives for its coefficients. -/
def PrimeRamifiedGradedNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        ∀ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TL F.Carrier i =
            if i ≤ t then ⊤ else ⊥) →
          let ψ : ℕ → ℕ := fun n => if n ≤ t then n else t + ell * (n - t)
          let r := PadicField.TopologicalData.relativeResidueMap
            (F := F) (E := L) TF TL
          let N := normUnits F.Carrier L.Carrier
          Function.Bijective r ∧
          (∀ (n : ℕ) (x : TL.unitFiltration (ψ n)),
            N (x : L.Carrierˣ) ∈ TF.unitFiltration n) ∧
          (∀ (n : ℕ) (x : TL.unitFiltration (ψ n + 1)),
            N (x : L.Carrierˣ) ∈ TF.unitFiltration (n + 1)) ∧
          (∀ (x : TL.unitFiltration 0) (y : TF.unitFiltration 0),
            (y : F.Carrierˣ) = N (x : L.Carrierˣ) →
            Units.map r.toMonoidHom (TF.zeroUnitCoordinate y) =
              TL.zeroUnitCoordinate x ^ ell) ∧
          ∀ (πF : F.Carrier) (hF : TF.ord πF = 1)
            (πL : L.Carrier) (hL : TL.ord πL = 1),
            (∀ n : ℕ, 0 < n → n < t →
              ∃ a : TF.Integers,
                (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n ∧
                TF.residue a ≠ 0 ∧
                ∀ (x : TL.unitFiltration n) (y : TF.unitFiltration n),
                  (y : F.Carrierˣ) = N (x : L.Carrierˣ) →
                  r (TF.residue (TF.unitCoefficient πF hF n y)) =
                    r (TF.residue a) * TL.residue (TL.unitCoefficient πL hL n x) ^ p) ∧
            (0 < t →
              ∃ a b : TF.Integers,
                (a : F.Carrier) = Algebra.norm F.Carrier πL ^ t / πF ^ t ∧
                (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ t) / πF ^ t ∧
                TF.residue a ≠ 0 ∧ TF.residue b ≠ 0 ∧
                ∀ (x : TL.unitFiltration t) (y : TF.unitFiltration t),
                  (y : F.Carrierˣ) = N (x : L.Carrierˣ) →
                  r (TF.residue (TF.unitCoefficient πF hF t y)) =
                    r (TF.residue a) * TL.residue (TL.unitCoefficient πL hL t x) ^ p +
                    r (TF.residue b) * TL.residue (TL.unitCoefficient πL hL t x)) ∧
            (∀ n : ℕ, t < n →
              ∃ b : TF.Integers,
                (b : F.Carrier) = Algebra.trace F.Carrier L.Carrier (πL ^ ψ n) / πF ^ n ∧
                TF.residue b ≠ 0 ∧
                ∀ (x : TL.unitFiltration (ψ n)) (y : TF.unitFiltration n),
                  (y : F.Carrierˣ) = N (x : L.Carrierˣ) →
                  r (TF.residue (TF.unitCoefficient πF hF n y)) =
                    r (TF.residue b) *
                      TL.residue (TL.unitCoefficient πL hL (ψ n) x))

end Langlands.LocalClassField
