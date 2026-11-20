# Supercuspidal cases of the GL pole-region statement

This internal module supports the proof `Langlands.Global.glPairPoleRegion` of
`Langlands.Global.GLPairPoleRegionStatement`. It handles two supercuspidal cases
of Henniart (1986), Proposition 4.5(ii), `GL_n` side:

- unequal rank with the representation `π` of larger rank supercuspidal;
- equal rank with `σ` supercuspidal.

Everything is over the canonical realization `F.canonicalTopologicalData`, with
residue cardinality `q`.

## Auxiliary results

- `isOfWhittakerType_of_scale_neg_one ψ h`: Whittaker type for the standard
  character of `ψ.scale (-1)` implies Whittaker type for the standard character
  of `ψ`. The smoothness and finiteness clauses are kept. The published
  `characterChangeFunctionalEquiv ψ π (-1)` identifies the two spaces of Whittaker
  functionals.
- `character_center_eq_of_twisted_bilinear`: let `π` and `σ` act on the center by
  `ωπ` and `ωσ`. Let `β` be a nonzero bilinear form with
  `β(π g v, σ g w) = χ(g)⁻¹ β(v, w)`. Then `χ(z)⁻¹ = ωπ(z) ωσ(z)` for central `z`.
  To see this, evaluate at a pair `v, w` with `β v w ≠ 0`.
- `IsContragredientTwistParameter.pow_eq_pow`: let `π` and `σ` be irreducible
  admissible on `GL_(r+1)(F)`. Any two parameters `a`, `b` in the published
  `IsContragredientTwistParameter F π σ` satisfy `a^(r+1) = b^(r+1)`.
  - Such a parameter is `a = q^(-u)`, where `|·|^(-u) ∘ det` twists `π` into the
    smooth contragredient of `σ`.
  - The published `exists_twisted_bilinear_of_contragredient_equiv` turns this
    equivalence into a twisted invariant pairing.
  - The central characters come from `admissibleSchur_centralCharacter`.
  - The previous lemma is applied at the inverse-uniformizer scalar
    `z = ϖ⁻¹ · 1`. This is the published `centralSpectralElement`, the scalar
    matrix of the inverse of the chosen uniformizer `ϖ`. Here
    `|det z| = q^(r+1)`, so the twisting character takes the value
    `χ(det z) = q^(-u(r+1)) = a^(r+1)`
    (`determinantWeight_centralSpectralElement`). The lemma gives
    `a^(r+1) = (ωπ(z) ωσ(z))⁻¹`, whose right side does not depend on the
    parameter. Equivalently, `a^(r+1) = ωπ(ϖ · 1) ωσ(ϖ · 1)`.
  - This calculation is the formal proof's own. It is not taken from Henniart.

## Unequal rank, `π` supercuspidal

`hasNoReflectedCommonZero_of_supercuspidal_unequalRank` has the following
hypotheses:

- `t < r`;
- `π` on `GL_(r+1)(F)` irreducible and supercuspidal;
- `σ` on `GL_(t+1)(F)` of Whittaker type for `ψ`;
- `P` the p-adic pair L-polynomial of `(π, σ)` at a self-dual `ν`.

It concludes that `P` has no reflected common zero with any `Pdual`. The published
`supercuspidalUnequalRankLFactor` (JPSS 1983, (8.1)(i)) gives the pair
L-polynomial `1`. Uniqueness (`IsPadicPairLPolynomial.unique`) gives `P = 1`,
which has no zero.

## Equal rank, `σ` supercuspidal

`hasNoReflectedCommonZero_of_supercuspidal_equalRank` has the following
hypotheses:

- `π`, `σ` irreducible on `GL_(n+1)(F)`, with `σ` supercuspidal;
- both of Whittaker type for `ψ`;
- `P` the p-adic pair L-polynomial of `(π, σ)` for `ψ` at a self-dual `ν`;
- `Pdual` that of `(π^ι, σ^ι)` for `ψ.scale (-1)` at the same `ν`.

It concludes `HasNoReflectedCommonZero q P Pdual`. The proof has four steps.

1. The published `supercuspidalParameterProduct` is applied to the pair `(σ, π)`,
   with the supercuspidal member first. This is JPSS (1983), (8.1)(ii), p.443.
   The parameters are those of the unramified twists to the contragredient. This
   convention matches Henniart (2002), §3.3, p.598, where `L(s, π × π′)` is the
   product of the `L(s, χ)` over the quasicharacters `χ` with `π ≃ χπ′^∨`. It
   gives a finite set
   `A` of parameters `IsContragredientTwistParameter F σ π`, with these
   properties:
   - `∏_{a∈A} (1 - aX)` is the pair L-polynomial of `(σ, π)`;
   - `∏_{a∈A} (1 - a⁻¹X)` is that of `(σ^ι, π^ι)` for `ψ.scale (-1)`.
2. Equal-rank pair L-polynomials are symmetric at the same character and measure
   (`isPadicPairLPolynomial_swap_equalRank`). Uniqueness then gives
   `P = ∏ (1 - aX)` and `Pdual = ∏ (1 - a⁻¹X)`.
3. A reflected common zero `z` gives `a, b ∈ A` with `a z = 1` and
   `b⁻¹ q⁻¹ z⁻¹ = 1`. Hence `a = q b`.
4. By `pow_eq_pow`, `‖a‖ = ‖b‖`. Together with `‖a‖ = q ‖b‖`, `q > 1` and
   `b ≠ 0`, this is a contradiction.

This route is the formal proof's own. Henniart (1986), §4.8 (printed p.163),
handles a cuspidal member by citing "the same reasoning as in 4.7", the
juxtaposition argument of §4.7 (printed pp.161–162). Here the formal proof does
not follow that argument. It uses the explicit parameter product of
JPSS (8.1)(ii) and the central-character equality of `pow_eq_pow` instead.

## Dependencies

The module imports `Langlands.Global.Factors.GLPoleRegionTransport` (this
submission) and the published modules
`RankinSelberg/SupercuspidalUnequalRankLFactorReduction`,
`RankinSelberg/SupercuspidalParameterProductProof`,
`RankinSelberg/UnitaryContragredientTwistParameters`,
`RankinSelberg/EqualRankFactorSwapProof` and `Whittaker/CharacterChange`. It
introduces no axioms and no hypotheses.
