# Unconditional convergence of the adjacent-rank tensor integral

`Langlands.RankinSelberg.adjacentRankModelConvergence.{uF,uV}` proves the
unchanged closed Library proposition
`Langlands.RankinSelberg.AdjacentRankModelConvergenceStatement.{uF,uV}`.
Worker 455 implemented the proof and this explanation; Worker 450 contributed
the source, dependency and full-telescope audit.

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464, registered
as `jpss-1983-rankin-selberg`, Section 6.1, printed pp.427–431, especially
formula (8) and its convergence proof on p.429. The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.428–429 were visually checked, with p.429 at zero-based PDF index
63. No source-specific errata file was found in the prescribed project
locations.

## Scope and exact conclusion

The theorem retains the target's complete telescope: every prime and canonical
`PadicField.{uF}`, supplied nontrivial unitary additive character `ψ`,
additive Haar measure `ν` and self-duality proof `hself`, every `r : ℕ`,
every complex module `V : Type uV`, and every representation `σ` of the
actual `GL_(r+1)` with the published full
`IsOfWhittakerType r (standardCharacter ψ r) σ`. The field and carrier
universes are independent. For every functional `ℓ`, quasicharacter `χ`,
algebraic test tensor `Ψ` and `g : GL_(r+2)`, the conclusion is exactly

```text
Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g.
```

This is complex Bochner integrability with the canonical normalized absolute
value and exactly `generalLinearHaar F.Carrier r`. Only smoothness
`hσ.1.1` is used from the full-type premise; the pure-tensor helper is proved
for any smooth `σ`. Rank zero, zero functionals, zero coefficients and
reducible representations are included. The proof uses no topology or norm
on `V` or its coefficient image and imposes no growth bound on `χ`.

## Imported analytic inputs

The proof imports the unchanged model and statement. Its two additional
imports are `EqualRankSliceSupportProof` and `LastRowCompactOrbitProof`.
The invoked results are:

- `Whittaker.smoothSimpleRootSupport`: smoothness of the actual coefficient
  image gives a constant `R > 0` bounding the absolute values of every
  adjacent diagonal ratio wherever the coefficient is nonzero, uniformly
  over the integral factor in Iwasawa decomposition. Its proof uses smooth
  stabilizers and the additive conductor.
- `normalizedAbs_determinant_le_of_simpleRoot`: for a Whittaker function
  with that ratio bound, a bound `C ≥ 0` on every entry of the last row of
  a matrix `k` gives
  `|det k| ≤ ∏ i : Fin (r+1), R^(r-i.val) * C`.
  This is the elementary Iwasawa determinant estimate from
  `EqualRankSliceSupportProof`; the present proof invokes this helper,
  without invoking the equal-rank slice theorem.
- `isEmbedding_generalLinear_val`: the actual inclusion of GL into matrix
  space is a topological embedding over the canonical local field.
- `glModelFunction_continuous`: coefficients of a smooth representation
  are locally constant, hence continuous as complex-valued functions.
- The published `generalLinearHaar` is a Haar measure, finite on compact
  sets. Mathlib's `Continuous.integrable_of_hasCompactSupport` therefore
  applies to continuous complex-valued functions of compact support.

These inputs require neither a unitary central character nor irreducibility.
The proof imports no unrestricted two-block multiplicativity or finite-block
parent theorem and uses no later adjacent-rank analytic conclusion.

## Compact support on the inner group

Write
`K(h) = adjacentRankKernelMatrix h = [h, (h⁻¹)ᵀ ε]`.
Its first `r+1` columns are `h`, and its last column has entries
`lastRow h⁻¹ j`. The new `continuous_adjacentRankKernelMatrix` proves its
continuity entry by entry, using continuity of GL matrix entries and inversion.

For a rectangular Schwartz–Bruhat function `Φ`,
`exists_adjacentRank_lastColumn_bound` bounds the continuous function

```text
m ↦ ∑ j, |m j (last column)|
```

on the compact set `tsupport Φ`. Replacing the resulting bound by its maximum
with `1` gives `C > 0`. Nonnegativity of each summand then implies
`|lastRow h⁻¹ j| ≤ C` whenever `Φ(K(h)) ≠ 0`.

The main new support lemma, `adjacentRankPure_hasCompactSupport`, applies the
imported smooth simple-root theorem to `W` and the determinant estimate to
`h⁻¹`. On the nonvanishing locus of `Φ(K(h)) W(h⁻¹)` it obtains

```text
|det h⁻¹| ≤ D,       D = ∏ i : Fin (r+1), R^(r-i.val) * C > 0.
```

Multiplicativity of the normalized absolute value gives
`D⁻¹ ≤ |det h|`. Meanwhile, `h` lies in the image of `tsupport Φ` under the
continuous first-columns projection. Define the matrix set

```text
S = firstColumns '' tsupport Φ ∩ {A | D⁻¹ ≤ |det A|}.
```

The first set is compact, and the second is closed by continuity of determinant
and normalized absolute value. Thus `S` is compact. Its determinant lower
bound is strictly positive, so every matrix in `S` is invertible. Pulling
`S` back through the published GL embedding yields a compact subset of the
actual inner GL containing the nonzero locus of `Φ(K(h)) W(h⁻¹)`.
`HasCompactSupport.intro` gives compact support. At `r = 0` the simple-root
conditions are empty and the positive determinant estimate still applies.

## Integrability and arbitrary tensors

For a fixed ambient `g`, the pure-tensor theorem first replaces `Φ` by the
Schwartz–Bruhat function `Φ' = rectangularRho0 ψ ν (r+1) hself g Φ`.
The model's definition then identifies its exact scalar integrand with

```text
h ↦ Φ'(K(h)) W(h⁻¹) χ(det h) |det h|^(r/2).
```

The kernel and coefficient factors are continuous by the results above.
The quasicharacter and determinant are continuous. The new
`continuous_adjacentRank_determinantWeight` proves continuity of the complex
power for every complex exponent: its real base is strictly positive on GL,
so its image lies in the complex slit plane. Multiplying these factors
preserves the compact support already proved for `Φ'(K(h)) W(h⁻¹)`.
Consequently `Continuous.integrable_of_hasCompactSupport` proves actual
integrability for the exact shared Haar measure.

Finally `adjacentRankTestSpace_induction` reduces an arbitrary algebraic test
tensor to pure tensors and addition. The pure case is the preceding theorem.
The addition case is the model's `AdjacentRankModelConverges.add`, whose two
integrability premises have already been proved by induction. This covers the
entire algebraic tensor product.

## Relation to the source

On printed p.429 the source absorbs the ambient action into the test function,
reduces to decomposable factors, and combines Iwasawa decomposition,
Whittaker gauge bounds and Schwartz support to restrict the integration
variables to compact sets. The implemented argument has the same support
geometry, expressed by a compact matrix projection and a determinant lower
bound. The root estimate comes from the Library's smooth-stabilizer proof,
so the source's gauge majorization theorem and its central-character
restriction are not needed. The new support and continuity helpers are
internal derived results justified by the steps above.

This theorem establishes convergence of formula (8) for arbitrary `χ`.
The source's sufficiently large positive twist is used in its separate
induced-model spanning argument and double integral (13). Model-image
equality, star transforms and adjacent-rank gamma/L identities remain
separate obligations.
