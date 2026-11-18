import Langlands.Global.Arithmetic.HenniartHarrisDatumStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerData

/-!
# Henniart's global characters as data for Proposition 4.8 under the exact stabilizer condition

Henniart (2000), Section 3.6, Lemme 3, read in the hypotheses of Harris (1998),
Proposition 4.8, with the auxiliary character subject to Harris's condition (4.12)
(proof of Lemma 4.7): the published `HarrisDatumCharacterRealizationStatement` with
`IsProposition48Datum` replaced by `Harris.IsProposition48ExactStabilizerDatum`.
Everything else is unchanged. The new statement implies the published one. The
statement is not proved here.
-/

noncomputable section

universe uF uE uE' uL

namespace Langlands.Global

open NumberField LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

/-- Henniart 2000, Lemma 3 of Section 3.6, in the hypotheses of Harris 1998,
Proposition 4.8, with the auxiliary character subject to condition (4.12). On every
paired-place configuration, for every normalized reciprocity family `e` and every
continuous character `χ₀` of `F'ˣ`, there are characters `χ, χs` of `F'ˣ` and a Hecke
character `ξ` of `E'` satisfying `IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ`
(so the stabilizer of the restriction of the Weil character of `χs` to the Weil group
of `F̃` is exactly the Weil group of `F'`), with `χ` equal to `χ₀` on the units of the
valuation ring of `F'`.

This is `HarrisDatumCharacterRealizationStatement` with
`Harris.IsProposition48ExactStabilizerDatum` in place of `IsProposition48Datum`;
nothing else is changed. -/
def HarrisDatumCharacterRealizationExactStabilizerStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL)
    [Field E] [Field E'] [Field L] [NumberField E] [NumberField E'] [NumberField L]
    [IsCMField E] [IsCMField E'] [IsCMField L]
    [Algebra E E'] [Algebra E L] [Algebra E' L]
    (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field)
    (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
    IsPairedPlaceConfiguration K₀ P Ps φ φs θ →
    ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
    ∀ χ₀ : FieldCharacter F F',
      ∃ (χ χs : FieldCharacter F F') (ξ : HeckeCharacter E'),
        Harris.IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ ∧
        ∀ u : F'.fieldˣ, (fieldData F F').discreteValuation (u : F'.field) = 1 →
          χ u = χ₀ u

/-- The exact-stabilizer realization implies the published realization, because every
exact-stabilizer datum is a datum (`IsProposition48ExactStabilizerDatum.isProposition48Datum`,
through `generalPositionOfExactStabilizer`). -/
theorem harrisDatumCharacterRealizationStatement_of_exactStabilizer
    (h : HarrisDatumCharacterRealizationExactStabilizerStatement.{uF, uE, uE', uL}) :
    HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL} := by
  intro p _ F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ K₀ P Ps φ φs θ hconf e he χ₀
  obtain ⟨χ, χs, ξ, hD, hχ⟩ := h F F' E E' L K₀ P Ps φ φs θ hconf e he χ₀
  exact ⟨χ, χs, ξ, hD.isProposition48Datum, hχ⟩

end Langlands.Global
