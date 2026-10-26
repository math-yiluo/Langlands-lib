import Langlands.Group.GL.Mirabolic
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Compact opposite-character mirabolic test functions

An existence target for the compact mirabolic functions used before the
Kirillov lift in the equal-rank JPSS argument. This module defines a proposition;
it supplies neither its proof nor an integral identity.
-/

namespace Langlands.Whittaker

universe uF

/-- Compact opposite-character functions on the actual mirabolic subgroup,
extended by zero to the ambient general linear group.

The common compact open right stabilizer has normalized determinant norm one.
An ambient compact open subgroup restricts inside this stabilizer, providing
the ambient formulation of smoothness on the mirabolic subgroup only. -/
def MirabolicUnitTestStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier,
    let G := GeneralLinear (n + 1) F.Carrier
    let P : Subgroup G := GeneralLinear.mirabolic n F.Carrier
    let N : Subgroup G := GeneralLinear.upperUnipotent (n + 1) F.Carrier
    let χ := standardCharacter ψ n
    ∃ (P₀ : OpenSubgroup P)
      (φ : RankinSelberg.WhittakerFunctions ψ n)
      (φ' : RankinSelberg.InverseWhittakerFunctions ψ n)
      (J₀ : OpenSubgroup G),
      let C : Set G := (fun k : P => k.val) '' (P₀ : Set P)
      let S : Set G := {g | ∃ u : N, ∃ k : P₀, g = u.val * k.val.val}
      IsCompact (P₀ : Set P) ∧
      IsCompact (J₀ : Set G) ∧
      (∀ k : P₀, T.determinantNorm (n + 1) k.val.val = 1) ∧
      (∀ j : G, j ∈ J₀ → j ∈ P → j ∈ C) ∧
      (∀ (u : N) (k : P₀),
        φ.val (u.val * k.val.val) = (χ u : ℂ) ∧
        φ'.val (u.val * k.val.val) = ((χ u : ℂ)⁻¹)) ∧
      (∀ g : G, g ∉ S → φ.val g = 0 ∧ φ'.val g = 0) ∧
      (∀ (g : G) (k : P₀),
        φ.val (g * k.val.val) = φ.val g ∧
        φ'.val (g * k.val.val) = φ'.val g)

end Langlands.Whittaker
