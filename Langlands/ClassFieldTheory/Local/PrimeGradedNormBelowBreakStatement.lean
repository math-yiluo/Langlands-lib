import Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormStatement
import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsStatement
import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionStatement

namespace Langlands.LocalClassField
open Langlands.PadicField.TopologicalData
universe u v

/-- The below-break coordinate clause, conditional on the two exact arithmetic inputs. -/
def PrimeGradedNormBelowBreakFromArithmetic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
    (_htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
    (_htrace : PrimeRamifiedTraceIdeals.{u,v}) (_hexpansion : PrimeNormTraceExpansion.{u,v})
    (_hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
    (_hpat : ∀ i : ℕ, Ramification.Padic.lowerRamificationGroup L.canonicalTopologicalData F.Carrier i =
      if i ≤ t then ⊤ else ⊥)
    (πF : F.Carrier) (hF : F.canonicalTopologicalData.ord πF = 1)
    (πL : L.Carrier) (hL : L.canonicalTopologicalData.ord πL = 1)
    (n : ℕ) (_hn : 0 < n) (_hnt : n < t),
    ∃ a : F.canonicalTopologicalData.Integers,
      (a : F.Carrier) = Algebra.norm F.Carrier πL ^ n / πF ^ n ∧
      F.canonicalTopologicalData.residue a ≠ 0 ∧
      ∀ (x : L.canonicalTopologicalData.unitFiltration n) (y : F.canonicalTopologicalData.unitFiltration n),
        (y : F.Carrierˣ) = normUnits F.Carrier L.Carrier (x : L.Carrierˣ) →
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData
          (F.canonicalTopologicalData.residue (F.canonicalTopologicalData.unitCoefficient πF hF n y)) =
        relativeResidueMap F.canonicalTopologicalData L.canonicalTopologicalData (F.canonicalTopologicalData.residue a) *
          L.canonicalTopologicalData.residue (L.canonicalTopologicalData.unitCoefficient πL hL n x) ^ p

end Langlands.LocalClassField
