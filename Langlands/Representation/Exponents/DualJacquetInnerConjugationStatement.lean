import Langlands.Representation.Exponents.WeakCritical

/-! Inner-conjugation invariance of the actual opposite-dual Jacquet spectrum.
These closed proposition definitions state algebraic transport, without proving it. -/

namespace Langlands

universe uF uV

/-- Inner pullback preserves every actual dual Jacquet exponent, with the
same character on the same ordered block shape. -/
def GLDualJacquetInnerConjugationNonunitaryStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (P : Exponents.ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ),
      T.IsDualJacquetExponent P.shape (P.pullbackRep A) χ ↔
        T.IsDualJacquetExponent P.shape A χ

/-- Inner pullback preserves every actual unitary dual Jacquet exponent,
with no irreducibility, admissibility, temperedness or rank-positivity hypothesis. -/
def GLDualJacquetInnerConjugationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (P : Exponents.ConjugateBlockPair n F.Carrier)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (χ : (Fin P.shape.length → F.Carrierˣ) →* ℂˣ),
      T.IsUnitaryDualJacquetExponent P.shape (P.pullbackRep A) χ ↔
        T.IsUnitaryDualJacquetExponent P.shape A χ

end Langlands
