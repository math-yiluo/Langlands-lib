import Langlands.JacquetLanglands.CharacterStatements

/-!
# Irreducible smooth representations of `Dˣ` are finite-dimensional

The proposition `IrreducibleDivisionUnitsFiniteDimensionalStatement`, not proved here: the closed
form of `IrreducibleDivisionUnitsFiniteDimensional`, quantified over every nonarchimedean local
field `F` and every finite-dimensional central division algebra `D` over `F` with its module
topology.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uW

/-- Closed form of `IrreducibleDivisionUnitsFiniteDimensional`: for every nonarchimedean local
field `F` and every finite-dimensional central division algebra `D` over `F` with its module
topology, every irreducible smooth representation of `Dˣ` with carrier in `Type uW` is
finite-dimensional. -/
def IrreducibleDivisionUnitsFiniteDimensionalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D],
    IrreducibleDivisionUnitsFiniteDimensional.{u, uW} F D

end Langlands.JacquetLanglands
