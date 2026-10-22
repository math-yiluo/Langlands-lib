import Langlands.VirtualRepresentation.Supercuspidal.Basic

/-!
# Norm-one extraction on the actual unitary supercuspidal lattice

The two conclusions are deliberately separate: the integral norm determines
a basis class up to sign, and strictly positive group-rank degree fixes the sign.
No correspondence map, isometry, or surjectivity is a construction assumption.
-/

namespace Langlands.VirtualRepresentation.Supercuspidal

universe uF uV

/-- An integral norm-one vector determines a unique genuine unitary
supercuspidal class up to sign, across all positive group ranks. -/
def UnitarySignedBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (v : PadicSupercuspidal.UnitaryLattice.{uF, uV} F),
    PadicSupercuspidal.unitaryPairing F v v = 1 →
      ∃! b : PadicSupercuspidal.UnitaryBasis.{uF, uV} F,
        v = generator b ∨ v = -generator b

/-- Strictly positive degree chooses the positive multiplicity-one generator.
The degree is the general linear group rank, not the carrier dimension. -/
def UnitaryPositiveBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (v : PadicSupercuspidal.UnitaryLattice.{uF, uV} F),
    PadicSupercuspidal.unitaryPairing F v v = 1 →
      0 < PadicSupercuspidal.unitaryDegree F v →
        ∃! b : PadicSupercuspidal.UnitaryBasis.{uF, uV} F,
          v = generator b

/-- The actual target-side signed and positive extraction assertions.
This proposition asserts no relation descent, isometry or final surjectivity. -/
def UnitaryNormOneExtractionStatement : Prop :=
  UnitarySignedBasisStatement.{uF, uV} ∧
    UnitaryPositiveBasisStatement.{uF, uV}

end Langlands.VirtualRepresentation.Supercuspidal
