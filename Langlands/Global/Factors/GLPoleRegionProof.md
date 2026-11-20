# Proof of the GL pole-region statement

The theorem `Langlands.Global.glPairPoleRegion` proves the published statement
`Langlands.Global.GLPairPoleRegionStatement.{uF, uV, uW}` of
`Langlands/Global/Factors/GLPoleRegionStatement`. This is the `GL_n` half of
Henniart (1986), Proposition 4.5(ii), for JPSS L-polynomials. For every prime
`p`, p-adic field `F` and realization `T`:

- in equal rank `n + 1`, if `π` and `σ` are both essentially tempered or `σ` is
  supercuspidal;
- in unequal ranks `n + (j + k + 1) + 1 > n + 1`, block `j`, if both are
  essentially tempered or either is supercuspidal;

the JPSS L-polynomial `P` of `(π, σ)` and the normalized generator `Pdual` of the
dual-pair values of `(π^ι, σ^ι)` for `ψ⁻¹` satisfy
`HasNoReflectedCommonZero q P Pdual`. The universe levels of the field and of the
two carriers are independent, and the statement is unchanged. The proof uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

1. **Canonical realization.** `PadicField.TopologicalData.eq_canonicalTopologicalData`
   (`GLPoleRegionTransport`) shows `T = F.canonicalTopologicalData`. The proof
   substitutes `T`, so all later steps use the canonical topology, valuative
   relation and local-field structure. These are the setting of the Library's
   p-adic local-factor theorems.
2. **Measures.** The published `HighlyRamified.nonempty_selfDualHaar` gives a
   self-dual Haar measure `ν` for `ψ` and `νd` for `ψ.scale (-1)`. These choices are
   internal. The statement's `P` and `Pdual` are relations at an arbitrary
   compatible `μ` and, in unequal rank, at an arbitrary additive Haar measure
   `ν₀`. The proof identifies them with p-adic pair L-polynomials at the chosen
   measures.
3. **Reduction.** `isPadicPairLPolynomial_of_equalRank` and
   `isPadicPairLPolynomial_of_unequalRank` (`GLPoleRegionTransport`) turn the
   hypotheses on `P` and `Pdual` into the following:
   - `IsPadicPairLPolynomial F ψ ν π σ P`;
   - `IsPadicPairLPolynomial F (ψ.scale (-1)) ν' π^ι σ^ι Pdual`, with `ν' = νd`
     in the tempered cases and `ν' = ν` in the supercuspidal cases.

   This uses the genericity hypotheses: `π` generic for `ψ`, `σ` for `ψ⁻¹`.
4. **Cases.** Write `r + 1` and `t + 1` for the ranks of `π` and `σ`, with
   `t ≤ r`.
   - **Both essentially tempered**, equal or unequal rank:
     `hasNoReflectedCommonZero_of_essentiallyTempered` (`GLPoleRegionTempered`).
     It uses irreducibility from genericity, and `t ≤ r` (`le_rfl` in equal rank,
     `omega` in unequal rank).
   - **Equal rank, `σ` supercuspidal:**
     `hasNoReflectedCommonZero_of_supercuspidal_equalRank`
     (`GLPoleRegionSupercuspidal`). Whittaker type for `ψ` comes from
     `RankinSelberg.isOfWhittakerType_of_isGeneric`. For `σ`, which is generic for
     `ψ⁻¹`, it also uses `isOfWhittakerType_of_scale_neg_one`.
   - **Unequal rank, `σ` supercuspidal** (of the smaller rank):
     `hasNoReflectedCommonZero_of_supercuspidal_le`
     (`GLPoleRegionSmallSupercuspidal`), which is the Zelevinsky-segment argument.
   - **Unequal rank, `π` supercuspidal** (of the larger rank):
     `hasNoReflectedCommonZero_of_supercuspidal_unequalRank`
     (`GLPoleRegionSupercuspidal`). There `P = 1` by JPSS (8.1)(i). It uses
     `t < r` and the Whittaker type of `σ` for `ψ`.

## Helper modules

The proof is split into four internal helper modules. Each has its own Markdown
file:

- `Langlands/Global/Factors/GLPoleRegionTransport`: realizations, Haar measures,
  identification of the statement's relations, and zero-free disks.
- `Langlands/Global/Factors/GLPoleRegionTempered`: the essentially tempered case.
- `Langlands/Global/Factors/GLPoleRegionSupercuspidal`: the two cases solved by
  JPSS (8.1) directly.
- `Langlands/Global/Factors/GLPoleRegionSmallSupercuspidal`: a generic first
  member against a supercuspidal second member, via Zelevinsky's classification
  and the published pole-order formula.

The formal route compares with Henniart (1986), §§4.7–4.8 (printed pp.161–163),
as follows.

- Both essentially tempered: the zero-free-disk separation of §4.8. The pole
  bounds come from the Library's tempered pole-freeness, as in JPSS (8.4).
- Second member `σ` supercuspidal: Henniart's §4.8 invokes "the same reasoning
  as in 4.7", the juxtaposition argument of §4.7.
  - Unequal rank: the formal proof follows that argument with Zelevinsky
    segments. The explicit check that a segment is not adjacent to itself (the
    case `i = j`) is the formal proof's own.
  - Equal rank: the formal proof's own route. It uses the explicit parameter
    product of JPSS (1983), (8.1)(ii), whose parameters are unramified twists to
    the contragredient, as recorded in Henniart (2002), §3.3, p.598. A
    central-character calculation at the inverse-uniformizer scalar then shows
    that all parameters have the same absolute value.
- First member `π` supercuspidal of the larger rank: `P = 1` by JPSS (8.1)(i),
  so there is nothing to separate. This direct step is the formal proof's own.

The proof uses the Library's closed local-factor theorems: JPSS (8.1)(i)/(ii),
the square-integrable and segment-head factors, Langlands pair factor existence,
tempered pole-freeness and Gelfand–Kazhdan transport. It also uses Zelevinsky's
Theorem 9.7 exhaustion, as published. No hypothesis, axiom or substitute
definition is introduced.

## Source

Guy Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*,
Annals of Mathematics (2) 123 (1986), 145–203 (`henniart-1986-cyclic`),
Proposition 4.5(ii), printed p.160, and its proof in §4.8, printed pp.162–163,
which refers back to §4.7, printed pp.161–162. H. Jacquet, I. I.
Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg Convolutions*, Amer. J.
Math. 105 (1983), 367–464 (`jpss-1983-rankin-selberg`), Proposition (8.1),
p.443, and (8.4). Guy Henniart, *Une
caractérisation de la correspondance de Langlands locale pour GL(n)*, Bull. Soc.
Math. France 130 (2002), §3.3, p.598 (`henniart-2002-characterization`).
The statement's Markdown `GLPoleRegionStatement.md` records the formalization
choices.
