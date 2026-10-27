import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.SupercuspidalComponent

/-!
# Harris's Proposition 4.8: weak automorphic induction with a supercuspidal place

Harris (1998), Proposition 4.8, page 201: for a normalized reciprocity family
and under the hypotheses `IsProposition48Datum` of Section 4, there is a
cuspidal automorphic
representation `Π ∈ U(n, E)` that is a weak automorphic induction of `ξ` and
whose local component at the auxiliary place `v(*)₁` is supercuspidal.
-/

noncomputable section

universe uF uE uE' uL uV

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure

/-- Harris 1998, Proposition 4.8. For a normalized reciprocity family `e` and
the data of Section 4 (pages 200--201) satisfying
`IsProposition48Datum e χ χs K₀ P Ps ξ`, there is an irreducible
cuspidal class `c` of `GL_n(𝔸_E)` such that:

* `c` is a weak automorphic induction of `ξ` (Definition 1.3(b)), so that
  `n = [E' : E]`;
* `c` has Clozel's regular algebraic type at infinity (`c ∈ Reg(n, E)`);
* `c` is conjugate self-dual, `Π ≅ Π̌ ∘ c` (Theorem 1.2(ii));
* the local component of `c` at the auxiliary place `v(*)₁ = Ps.v` is
  supercuspidal.

The last three conditions, with the hypotheses that `Ps.v` lies above `p` and
that `p` splits in `K₀`, give `Π ∈ U(n, E)`.

The datum reads Harris's "algebraic" in the normalization of page 195:
`IsAlgebraicAfterTwist (n - 1) ξ`, so `ξ · ‖·‖^{(n-1)/2}` has an integral
infinity type. -/
def Proposition48Statement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
    [IsCMField E] [IsCMField E'] [CompactSpace (AdeleQuotient E)]
    (e : ReciprocityFamily F) (χ χs : FieldCharacter F F') (K₀ : IntermediateField ℚ E)
    (P Ps : PlaceDatum F F' E E' L) (ξ : HeckeCharacter E'),
    NormalizedReciprocity F e → IsProposition48Datum e χ χs K₀ P Ps ξ →
      ∃ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r),
        c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ ∧
        c.IsRegularAlgebraic ∧
        c.IsConjugateSelfDual ∧
        c.HasSupercuspidalComponent.{uE, uV} Ps.v

end Langlands.Global.Harris
