import Langlands.Global.Arithmetic.HarrisProposition48Statement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerData

/-!
# Harris's Proposition 4.8 under the exact Weil stabilizer condition

Harris (1998), Proposition 4.8 (page 201), restated with the hypotheses
`IsProposition48ExactStabilizerDatum`: the auxiliary character satisfies
Harris's condition (4.12) (proof of Lemma 4.7, page 204) instead of being in
general position. The binders, instance arguments, universes and four-part
conclusion are those of the published `Proposition48Statement`.

The theorem at the end shows that the published `Proposition48Statement`
implies the restated proposition, through the proved implication (4.12) ⇒
general position (`generalPositionOfExactStabilizer`).
-/

noncomputable section

universe uF uE uE' uL uV

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure

/-- Harris 1998, Proposition 4.8, with the auxiliary character subject to
condition (4.12). For a normalized reciprocity family `e` and data satisfying
`IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ`, there is an
irreducible cuspidal class `c : CuspidalOperatorRealization.IsoClass E r` of
`GL_{r+1}(𝔸_E)` that is a weak automorphic induction of `ξ` (so that
`r + 1 = [E' : E]`, Harris's `n`, by `IsWeakAutomorphicInductionOf.rank_eq`),
has Clozel's regular algebraic type at infinity, is conjugate self-dual, and
has a supercuspidal local component at the auxiliary place `v(*)₁ = Ps.v`.

This is `Proposition48Statement` with `IsProposition48ExactStabilizerDatum` in
place of `IsProposition48Datum`; nothing else is changed. -/
def Proposition48ExactStabilizerStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
    [IsCMField E] [IsCMField E'] [CompactSpace (AdeleQuotient E)]
    (e : ReciprocityFamily F) (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E'),
    NormalizedReciprocity F e → IsProposition48ExactStabilizerDatum e χ χs K₀ P Ps ξ →
      ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r),
        c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ ∧
        c.IsRegularAlgebraic ∧
        c.IsConjugateSelfDual ∧
        c.HasSupercuspidalComponent.{uE, uV} Ps.v

/-- The published general-position form of Proposition 4.8 implies the
exact-stabilizer form, because the exact-stabilizer datum implies the
general-position datum. -/
theorem proposition48ExactStabilizerStatement_of_proposition48Statement
    (h : Proposition48Statement.{uF, uE, uE', uL, uV}) :
    Proposition48ExactStabilizerStatement.{uF, uE, uE', uL, uV} := by
  intro p _ F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ e χ χs K₀ P Ps ξ he hD
  exact h F F' E E' L e χ χs K₀ P Ps ξ he hD.isProposition48Datum

end Langlands.Global.Harris
