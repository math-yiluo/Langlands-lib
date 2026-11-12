import Langlands.Galois.WeakAssociation
import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Harris (1998), Theorem 1.2: weakly associated compatible families

Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134 (1998), Theorem 1.2, printed p.185 (mostly due to Clozel):
let `E = E₀ K₀` be a CM field with `E₀` totally real and `K₀` imaginary
quadratic, and let `π ∈ Reg(n, E)` have cuspidal spectrum `(nᵢ, πᵢ)`. Suppose
each `πᵢ` is conjugate self-dual, has a square-integrable local component at a
finite place `vᵢ`, and the rational prime below `vᵢ` splits in `K₀`. Then
`π ∈ C(n, E)`: some compatible family of `λ`-adic representations, a sum of
pure families, is weakly associated to `π`.

These are unproved statement definitions. Weak association is almost
everywhere unramified matching; no ramified local compatibility is asserted.
-/

noncomputable section

universe uE uJ uL uV uW

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Unramified Langlands.Automorphic
open NumberField (IsTotallyReal IsTotallyComplex IsCMField)

/-- The CM conjugation of `E` fixes every totally real intermediate field, so
when `E = E₀ K₀` it is the nontrivial element `c` of `Gal(E/E₀)`. -/
theorem complexConj_apply_of_mem_totallyReal {E : Type uE} [Field E] [NumberField E]
    [IsCMField E] (E₀ : IntermediateField ℚ E) [IsTotallyReal E₀] {x : E} (hx : x ∈ E₀) :
    IsCMField.complexConj E x = x := by
  have hle := IsTotallyReal.le_maximalRealSubfield (K := E) E₀.toSubfield
  exact IsCMField.complexConj_apply_eq_self (K := E) ⟨x, hle hx⟩

/-- Harris (1998), Theorem 1.2, for an isobaric representation given by its
cuspidal spectrum, a finite family `c` of irreducible cuspidal classes of
`GL_{nⱼ}(𝔸_E)`.

Hypotheses: `E` is a CM field with intermediate fields `E₀` totally real and
`K₀` imaginary quadratic such that `E = E₀ K₀`; every `cⱼ` has Clozel's regular
algebraic type at infinity (`π ∈ Reg(n, E)`), is conjugate self-dual for the CM
conjugation (Theorem 1.2(ii)), and has a square-integrable local component at
some finite place `vⱼ` whose residue characteristic splits in `K₀`
(Theorem 1.2(i) and the splitting assumption).

Conclusion (`π ∈ C(n, E)`, Definition 1.1 and p.184): there are a number field
`L` with an embedding `ι : L → ℂ`, a finite set of excluded places of `L`, and
finitely many collections `Rₖ` of genuine `λ`-adic representations of
`Gal(Ē/E)`, each compatible and pure of some weight `wₖ`, of total dimension
`n = ∑ nⱼ`, whose direct sum is weakly associated to the cuspidal spectrum. -/
def Harris1998Theorem12Statement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    ∀ (J : Type uJ) [Fintype J] (c : J → PositiveRankCuspidalClass E),
      (∀ j, (c j).2.IsRegularAlgebraic) →
      (∀ j, (c j).2.IsConjugateSelfDual) →
      (∀ j, ∃ v : FinitePlace E,
        CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uE, uW} (c j).2 v ∧
          Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀) →
      ∃ (L : Type uL) (fieldL : Field L),
        letI : Field L := fieldL
        ∃ (numberFieldL : NumberField L),
          letI : NumberField L := numberFieldL
          ∃ (ι : L →+* ℂ) (excluded : Finset (FinitePlace L)) (m : ℕ)
            (R : Fin m → Collection.{uE, uL, uV} E L excluded) (w : Fin m → ℤ) (d : Fin m → ℕ),
            (∀ k, IsPureCompatible excluded (R k) (w k)) ∧
            (∀ k, HasRank excluded (R k) (d k)) ∧
            ∑ k, d k = ∑ j, (c j).rank ∧
            PositiveRankCuspidalClass.IsSpectrumWeaklyAssociated.{uE, uL, uV, uW} c ι excluded R

/-- The cuspidal case of Harris (1998), Theorem 1.2: a single cuspidal class of
`GL_{r+1}(𝔸_E)` with the same hypotheses; the conclusion is the same
membership in `C(r + 1, E)`, with a sum of pure collections weakly associated to
the class. -/
def Harris1998Theorem12CuspidalStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
      c.IsRegularAlgebraic → c.IsConjugateSelfDual →
      CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uE, uW} c v →
      Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀ →
      ∃ (L : Type uL) (fieldL : Field L),
        letI : Field L := fieldL
        ∃ (numberFieldL : NumberField L),
          letI : NumberField L := numberFieldL
          ∃ (ι : L →+* ℂ) (excluded : Finset (FinitePlace L)) (m : ℕ)
            (R : Fin m → Collection.{uE, uL, uV} E L excluded) (w : Fin m → ℤ) (d : Fin m → ℕ),
            (∀ k, IsPureCompatible excluded (R k) (w k)) ∧
            (∀ k, HasRank excluded (R k) (d k)) ∧
            ∑ k, d k = r + 1 ∧
            CuspidalOperatorRealization.IsoClass.IsSumWeaklyAssociated.{uE, uL, uV, uW}
              c ι excluded R

end Langlands.GaloisRepresentation
