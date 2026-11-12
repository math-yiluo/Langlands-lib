import Langlands.Galois.WeakAssociation
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Harris (1999), Theorem 5.9(i): a pure compatible family for `Π`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), Theorem 5.9(i), printed pp.314-315 (due to
Clozel and Kottwitz): let `𝒦` be a CM field containing an imaginary quadratic
field, and let `Π` be a cuspidal automorphic representation of `GL(n, 𝒦)` of
cohomological type with `Π^c ≅ Π^∨`, supercuspidal at a finite place `v` of
`𝒦` that is split over the maximal totally real subfield. Then there are a
number field `C` and a compatible family `σ_λ(Π)` of `λ`-adic representations
of `Gal(𝒦̄/𝒦)`, `λ` running over all finite places of `C`, pure of some weight
`m`, whose normalized local Artin `L`-functions agree with the standard local
factors of `Π` at almost all places.

This is an unproved statement definition. The matching is almost everywhere
unramified matching; Theorem 5.9(ii), the local-global compatibility at `v`,
is not stated here.
-/

noncomputable section

universe u𝒦 uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic
open NumberField (IsTotallyComplex IsCMField)

/-- Harris (1999), Theorem 5.9(i), for a cuspidal class `c` of
`GL_{r+1}(𝔸_𝒦)`.

Context (Harris 1999, §1 and §4): `𝒦` is a CM field, the totally imaginary
quadratic extension of its maximal totally real subfield, it contains an
imaginary quadratic field `𝒦₀`, and `n = r + 1 > 1`.

Hypotheses of Theorem 5.9: `c` is of cohomological type (encoded as regular
algebraic), `c` is conjugate self-dual (`Π^c ≅ Π^∨`), the finite place `v` of
`𝒦` differs from its complex conjugate (the place of the maximal totally real
subfield below `v` splits in `𝒦`), and `c` has a supercuspidal component at
`v`.

Conclusion (i): there are a number field `L` (Harris's `C`) with an embedding
`ι : L → ℂ` and one collection `R` of genuine `λ`-adic representations of
`Gal(𝒦̄/𝒦)`, indexed by all finite places `λ` of `L`, of rank `r + 1`,
compatible and pure of some weight `m`, and weakly associated to `c`: at
almost all places the normalized local Artin `L`-function (5.6) of `R` is the
standard local factor of `c`. -/
def Harris1999Theorem59iStatement : Prop :=
  ∀ (𝒦 : Type u𝒦) [Field 𝒦] [NumberField 𝒦] [IsCMField 𝒦] [CompactSpace (AdeleQuotient 𝒦)]
    (𝒦₀ : IntermediateField ℚ 𝒦),
    Module.finrank ℚ 𝒦₀ = 2 → IsTotallyComplex 𝒦₀ →
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (c : CuspidalOperatorRealization.IsoClass 𝒦 r) (v : FinitePlace 𝒦),
      c.IsRegularAlgebraic → c.IsConjugateSelfDual →
      Harris.conjPlace 𝒦 v ≠ v →
      CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{u𝒦, uW} c v →
      ∃ (L : Type uL) (fieldL : Field L),
        letI : Field L := fieldL
        ∃ (numberFieldL : NumberField L),
          letI : NumberField L := numberFieldL
          ∃ (ι : L →+* ℂ) (R : Collection.{u𝒦, uL, uV} 𝒦 L ∅) (m : ℤ),
            IsPureCompatible ∅ R m ∧ HasRank ∅ R (r + 1) ∧
            CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{u𝒦, uL, uV, uW}
              c ι ∅ R

end Langlands.GaloisRepresentation
