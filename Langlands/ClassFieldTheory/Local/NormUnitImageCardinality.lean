import Langlands.ClassFieldTheory.Local.Norms
import Langlands.ClassFieldTheory.Local.Units
import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.FieldTheory.Galois.Abelian

/-! # The numerical norm filtration of a finite abelian local extension -/

noncomputable section

namespace Langlands.LocalClassField

universe u v

/-- The image of a unit level in the actual norm quotient has the order of the
corresponding upper ramification group, including nonnegative real levels. -/
def FiniteAbelianNormUnitImageCardinality : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI : FiniteDimensional F.Carrier E.Carrier :=
      Module.Finite.of_restrictScalars_finite (Padic p) F.Carrier E.Carrier
    ∀ a : ℝ, 0 ≤ a →
      Nat.card ((T.unitFiltration ⌈a⌉₊).map
        (normQuotientProjection F.Carrier E.Carrier)) =
          Nat.card (Ramification.Padic.upperRamificationGroup S F.Carrier a)

end Langlands.LocalClassField
