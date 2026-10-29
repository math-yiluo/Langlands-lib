# Rank-one JPSS `I₁ = I₃`: character zeta values versus matrix–Whittaker integrals

`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement.{uF,uV}` is
a closed Prop-valued statement. This module contains only the statement; it
proves nothing. Compiling it checks only that the proposition is well typed.

## Quantifiers

The proposition quantifies, in this order, over:

- every prime `p` with `[Fact p.Prime]`;
- every `F : PadicField.{uF} p`;
- every bundled `HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, formed
  for the canonical topology `F.canonicalTopologicalData.topology`. This
  structure bundles continuity, unitarity and nontriviality of `ψ`;
- every `n : ℕ`, so that the representation has actual rank `d = n + 1 ≥ 1`;
- every carrier `V : Type uV` with `AddCommGroup V` and `Module ℂ V`;
- every actual `σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V`.

The field universe `uF` and the carrier universe `uV` are independent.
After these binders the statement installs, by `letI`, the canonical
topology, valuative relation and nonarchimedean local-field structure of
`F.Carrier`. It also installs the Borel measurable spaces, with their
`BorelSpace` instances, on `GL(0 + 1)`, on its upper-unipotent subgroup
`upperUnipotent (0 + 1)` and on the actual left quotient
`LeftUnipotentQuotient 0 F.Carrier`. This is the same explicit telescope as
the analytic statements in `Langlands.Representation.RankinSelberg.AnalyticStatement`,
specialized to the rank-one quotient. `0 + 1` is definitionally `1`, so
`upperUnipotent (0 + 1)` is the subgroup `upperUnipotent 1` named in the task.

## Hypotheses

1. The sole representation premise is the full published
   `IsOfWhittakerType n (standardCharacter ψ n) σ`. It consists of
   `IsAdmissible σ`, which includes smoothness; finite generation of
   `σ.asModule` over the actual group algebra
   `MonoidAlgebra ℂ (GL(n + 1))`; and a complex linear equivalence between
   the entire space of standard Whittaker functionals and `ℂ`.
   Irreducibility, finite dimensionality, a chosen model or carrier
   equivalence are not assumed. Reducible representations of Whittaker type
   are included.
2. `ℓ : Whittaker.glFunctionals ψ n σ` is an arbitrary standard Whittaker
   functional with `ℓ.val ≠ 0`.
3. Every instance `[Measure.IsMulRightInvariant (unipotentHaar F.Carrier 0)]`
   is quantified, as in the analytic-statement telescope.
4. Every measure `μ` on `LeftUnipotentQuotient 0 F.Carrier` with
   `QuotientIntegration.IsCompatible (upperUnipotent (0 + 1) F.Carrier)
   (generalLinearHaar F.Carrier 0) (unipotentHaar F.Carrier 0) μ`
   is quantified. This is a hypothesis on a measure, not on `σ`. The
   published module `Langlands.Representation.RankinSelberg.RankOneQuotient`
   constructs such a measure separately, so the statement is not vacuous in
   `μ`. No additive Fourier measure enters.

## Conclusion

The conclusion is the equality of Laurent submodules of `RationalFunctions`

```text
zetaSpan (characterZetaValues q ψ abv μ (1 : F.Carrierˣ →* ℂˣ) n σ)
  = GodementJacquet.Padic.jpssI3 F ψ σ ℓ,
```

with `q = F.canonicalTopologicalData.residueCardinality` and
`abv = normalizedAbsoluteValue F.canonicalTopologicalData`. Both sides are
`zetaSpan`s, that is, `LaurentCoefficients`-submodules spanned by the
rational values in a set.

**Left side (`I₁`).** `characterZetaValues` is the published value set of
`σ × χ` from `Langlands.Representation.RankinSelberg.LocalFactor`, here with
`χ` the trivial bundled monoid homomorphism `1`. Its second member is
`rankOneCharacter 1`, the trivial scalar representation of `GL(1)` on `ℂ`.

- For `n = m + 1 > 0` it is the unequal-rank family
  `unequalRankZetaValues q ψ abv 0 m μ (Measure.dirac 0)
  (σ.comp (characterPairRank m).toMonoidHom) (rankOneCharacter 1)`,
  with `j = 0`, `k = m`, the published identity rank reindexing
  `characterPairRank m`, and the unit point mass on the zero-dimensional
  rectangular matrix space `Matrix (Fin 0) (Fin 1)`, which carries the
  discrete measurable structure. The integrand on `N₁ \ GL₁` is
  `W(diag(g, 1_n)) · W'(g) · |det g|^(s - n/2)` with exponent
  `s - (j + k + 1)/2 = s - n/2`, for `W` in the published `whittakerSet` of
  the reindexed `σ` and `W'` an inverse-character Whittaker function of the
  trivial character.
- For `n = 0` it is the actual equal-rank family
  `equalRankZetaValues q ψ abv μ σ (rankOneCharacter 1)`, whose integrand
  on `N₁ \ GL₁` is `W(g) · W'(g) · Φ(lastRow g) · |det g|^s` with a
  Schwartz–Bruhat function `Φ` on `F¹`.

A value is a rational function `R` such that the integral converges
absolutely on a right half-plane and agrees there with `R` at the spectral
point `q^(-s)`.

**Right side (`I₃`).** `GodementJacquet.Padic.jpssI3 F ψ σ ℓ` from
`Langlands.Representation.GodementJacquet.Zeta` is the `zetaSpan` of
`whittakerRationalValues`. A value there is a rational function `R` such
that, for some Schwartz–Bruhat `Φ` on all `(n+1) × (n+1)` matrices
(singular matrices included) and some vector `w` of the coefficient-image
model `glCoefficientModel ψ n σ ℓ`,
`HasShiftedRationalValue` holds for the model function `W = glModelFunction w`.
This means that
`∫_{GL(n+1)} Φ(g) W(g) |det g|^(s + n/2) dg` converges absolutely on a right
half-plane and agrees there with `R(q^(-s))`. Here `n/2 = jpssShift n` is a
complex number, `dg` is the shared `generalLinearHaar F.Carrier n` of mass
one on the integral general linear group, and the canonical Borel space on
`GL(n+1)` is used. The rational-function variable is the unshifted `s`. The
right side uses the coefficient image of the specified `ℓ`, not all
`N`-equivariant functions.

## Source correspondence

- JPSS (1983), `jpss-1983-rankin-selberg`, Section 5.2, printed page 420
  (one-based PDF page 55). The section takes `L(s, σ) = L(s, σ × 1)` with
  the rank-one trivial character. It assumes that `σ` acts on its Whittaker
  model `W(σ; ψ)`. Display (1) is
  `Ψ(s, W) = ∫_{F×} W(diag(a, 1, …, 1)) |a|^(s - (t-1)/2) d×a` with
  `t = n + 1`. Display (3) is the Godement–Jacquet integral
  `Z(Φ, s, W) = ∫ Φ(g) W(g) |det g|^s dg`.
- JPSS (1983), printed page 421 (PDF page 56). `I₁` is spanned by the
  integrals (1) and `I₃` by `Z(Φ, s + (t-1)/2, W)`. The text states that
  `I₁ = I₃` was seen in JPS I (Theorem (4.3) and Remark (4.2)).
- JPS (1979), `jps-1979-gl3-i`, Section 4.1, printed page 188 (PDF page 21).
  `L(s, π)` is the g.c.d. of `Z(Φ, s + (r-1)/2, W)`. Display (4.1.2) is
  `Ψ(s, W; 0)`. Theorem (4.3) and Remark (4.2) are on printed page 190 (PDF
  page 23). Remark (4.2) extends Theorem (4.3) to any space of functions
  satisfying Remark (2.2.5), printed page 183 (PDF page 16), which allows
  finitely generated admissible translation spaces of Whittaker functions,
  with the g.c.d. of the integrals `Z(Φ, s + (r-1)/2, W)` in place of
  `L(s, π)`. The proof, printed pages 191–194, uses Lemmas (4.3.1) and
  (4.3.4). It writes each `Z(Φ, s + (r-1)/2, W)` as `Ψ(s, W'; 0)` with
  `W'` an average of right translates of `W`, and conversely recovers each
  `Ψ(s, W; 0)` by a suitable choice of `Φ`. It thus shows that the two
  families span the same ideal of `ℂ[q^(-s), q^s]`. Rank-one
  quasicharacters are discussed on printed page 181 (PDF page 14).

No registered erratum to these passages was found.

The Lean premise matches this scope. `IsOfWhittakerType` retains
admissibility and finite generation, as Remark (4.2) with Remark (2.2.5)
requires, and keeps the full one-dimensional functional space. The
`characterZetaValues` exponent `s - n/2` and the matrix exponent
`s + n/2 = s + (t-1)/2` reproduce the normalizations of displays (1) and
(3) with `t = n + 1`, and both sides use the spectral variable `q^(-s)`.

## The actual-rank-one case `n = 0`

At actual rank one, JPS (1979) Section 4 has an empty range
`0 ≤ j ≤ r - 2`, and its Theorem (4.3) is not used. `characterZetaValues`
uses the equal-rank `GL(1) × GL(1)` integral instead. The comparison is then
a direct Tate-type bridge. The trivial-character inverse Whittaker
functions are constants. `N₁` is trivial and `unipotentHaar F.Carrier 0` is
the unit point mass, so the Weil formula in `IsCompatible` relates
`μ`-integrals of descended functions directly to
`generalLinearHaar F.Carrier 0`-integrals on `GL(1)`. The function `Φ(lastRow g)` on
`F¹` corresponds to a test function on the `1 × 1` matrix space. The
exponents agree because `n/2 = 0`. This boundary case is an internal part
of the stated comparison and is included in the same quantification over
`n`. It is not a transcription of a separately numbered result in either
source.

## Coefficient model versus the original carrier

JPSS (1983) first replaces `σ` by its action on its Whittaker model. The
Lean statement keeps the original arbitrary carrier `V` and its premise.
On the right it uses the actual coefficient-image model of the specified
nonzero `ℓ`, the image of `Whittaker.modelMap`, which is a quotient of `σ`.
On the left, the published `whittakerSet` ranges over the coefficient models
of all standard functionals of `σ`, after the identity reindexing
`characterPairRank` when `n > 0`. Under the one-dimensional functional
space, every functional is a scalar multiple of `ℓ`. These coefficient
models are then contained in that of `ℓ`.

The statement says nothing about matrix coefficients of the original
carrier. The Library's `jpssI2` uses `biSmoothMatrixCoefficients σ` of
`V`. The equality `I₂(σ) = I₃` for the original carrier is not asserted
here; a sibling statement treats `I₂` of the coefficient-model
representation.

## What is not asserted

The statement equates Laurent submodules before any packaging. It does not
assert analytic existence of the integrals or of their rational
continuations, a common denominator, a fractional ideal or a normalized
generator. It also asserts no L-factor identity, functional equation,
multiplicativity or `I₂(σ) = I₃` for the original carrier.

## Future proof obligations

A proof needs to pass from `σ` to its coefficient-model quotient. For
`n > 0` it then follows JPS (1979) Theorem (4.3) with Remark (4.2). For
`n = 0` it uses the Tate bridge above. The quotient inherits the
Whittaker-type hypotheses: admissibility through
`Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective`, and
finite generation through
`Representation.IntertwiningMap.equivLinearMapAsModule` and
`Module.Finite.of_surjective`. These are obligations of a separate proof
task, not premises of this statement.
