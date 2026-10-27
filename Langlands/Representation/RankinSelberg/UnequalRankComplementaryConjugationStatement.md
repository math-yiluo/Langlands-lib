# Complementary lower-row conjugation and translated-dual equivariance

`Langlands.RankinSelberg.UnequalRankComplementaryConjugationStatement.{uF,uV}`
is an internal proposition. It has two uniformly quantified clauses joined by `∧`.
The first is an identity between actual matrices in `GL_(r+1)`. The second is
its consequence for the translated first dual model equivalence. The proposition
is the pure algebra of the paired complementary-block transfer of
Jacquet–Piatetski-Shapiro–Shalika. It contains no Fourier transform, measure,
support or integral. This module states the proposition only and proves nothing.

## Ranks and actual matrices

For natural numbers `n j k`, the large rank is the canonical

```text
r = n + ((j + 1) + k + 1),
```

so the large group is `GL_(r+1)(F)` and the small rank `n + 1` satisfies
`n < r`. All of `n = 0`, `j = 0` and `k = 0` are allowed. Three published
matrices occur, and the proposition defines no new matrix.

- `a = blockWeylAt n r _`, the published unsigned block Weyl element
  `diag(I_(n+1), w_(r-n))`. Here `w_(r-n) = weylLong (r - n) F` is the
  permutation matrix of `Fin.rev`, with all nonzero entries `+1`. On indices it
  fixes `i < n + 1` and sends `i ≥ n + 1` to `r + n + 1 - i`.
- `U(z)` for a row `z : Fin (n + 1) → F` is
  `GeneralLinear.reindex (finCongr _) (unequalRankSmearingUnipotent n k j z)`.
  The published `unequalRankSmearingUnipotent n k j z` lives in
  `GL_(n+((k+1)+j+1)+1)`. Note the argument order: `k` comes before `j`. Its
  matrix is `1 + E(z)`. The only nonzero entries of `E(z)` are
  `E(z) i (n + k + 2) = z i` for `i < n + 1`. The reindexing by `finCongr` only
  identifies the equal natural numbers `n + ((k+1)+j+1) + 1` and
  `n + ((j+1)+k+1) + 1` and does not move entries. So `U(z)` is the upper
  unipotent matrix with column `n + k + 2` equal to `z` above the diagonal block
  `I_(n+1)`.
- `L(x) = rectangularUnipotent (j + 1) k (Fin.snoc 0 x)`, already in
  `GL_(n+((j+1)+k+1)+1) = GL_(r+1)`. The published `rectangularUnipotent` has
  matrix `1 + X`, where `X` places its `(j+1) × (n+1)` argument in rows
  `n + 1, …, n + j + 1` and columns `0, …, n`. The argument `Fin.snoc 0 x` has
  zero rows except its last row, `x`. So `L(x)` is the lower unipotent matrix
  whose row `n + j + 1` (zero-based) is `x` in columns `0, …, n`.

All indices are zero-based.

## The proposition

Clause 1 is the matrix identity. It is quantified over every field
`F : Type uF` with no topology, all `n j k`, and every row
`z : Fin (n + 1) → F`:

```text
inverseTranspose (r + 1) F (a⁻¹ * U(z) * a) = L(-z).
```

Here `inverseTranspose (r + 1) F g` is the published multiplicative involution
`g ↦ (g⁻¹)ᵀ`. Its `(p, q)` entry is the `(q, p)` entry of `g⁻¹`. Equality is
equality in `GL_(r+1)(F)`. The right side has the exact minus sign:
`Fin.snoc 0 (-z)`.

Clause 2 is equivariance of the translated dual model. It is quantified over:

- every field `F : Type uF` with a topology making it a topological ring
  (`[TopologicalSpace F] [IsTopologicalRing F]`, which the model APIs require),
  and all `n j k`;
- every unitary additive character `ψ`;
- every complex vector space `V : Type uV`, with the representation universe
  independent of the field universe, and every complex representation
  `π : Representation ℂ (GL_(r+1)(F)) V`;
- every functional `ℓ : glFunctionals ψ r π`, including `ℓ = 0`;
- every `f` in the actual coefficient image `(coefficientModel π ℓ).toSubmodule`,
  and every row `z : Fin (n + 1) → F`.

With `D = translatedFirstDualModelEquiv ψ π ℓ a`, the conclusion is

```text
D (modelRepresentation π ℓ (L(-z)) f)
  = modelRepresentation (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ) (U(z)) (D f).
```

`modelRepresentation` is right translation on the coefficient image, which is
`(ρ(h) f)(x) = f(x h)`. The published `D` sends `f` to the function
`x ↦ f(w_(r+1) · θ(x a))`, with `θ = inverseTranspose (r + 1) F` and
`w_(r+1) = weylLong (r + 1) F`. This is `translateWhittaker` of
`firstDualFunction`; see `translatedFirstDualModelEquiv_val`. `D` is a linear
equivalence from the model of `(π, ℓ)` onto the model of
`(inverseTransposePullback π, firstDualFunctional ψ π ℓ)`, whose character is
`ψ.scale (-1)`. Clause 2 asserts that `D` intertwines right translation by `L(-z)`
with right translation by `U(z)`.

No smoothness, irreducibility, admissibility, Whittaker-type, nonvanishing,
character-normalization, central-character or multiplicity-one hypothesis is
imposed. Clause 2 does not assume clause 1, and the proposition has no other
hypotheses.

## Index and sign check

Write `τ` for the involution of `Fin (r + 1)` that fixes `i < n + 1` and sends
`i ≥ n + 1` to `r + n + 1 - i`. Then `a` is the permutation matrix of `τ`, and
for any `g` the `(p, q)` entry of `θ(a⁻¹ g a)` is the `(τ q, τ p)` entry of
`g⁻¹`. Take `g = U(z)`, so `g⁻¹ = 1 - E(z)`. Since `E(z)` vanishes on the
diagonal, the diagonal entries of `θ(a⁻¹ U(z) a)` are `1`. Its off-diagonal
`(p, q)` entry is `-E(z) (τ q) (τ p)`. So it can be nonzero only when
`τ q = q < n + 1` and `τ p = n + k + 2`, and every other off-diagonal entry is
`0`. Since `n + k + 2 ≥ n + 1`, the second condition means

```text
p = r + n + 1 - (n + k + 2) = n + j + 1,
```

the last row of the rectangular block of `L`. When both conditions hold, the
entry is `-z q`. It is `0` exactly when `z q = 0`. For example, for `z = 0`
every off-diagonal entry vanishes and both sides are the identity. The tail
reversal therefore sends the column `n + k + 2` of `U` to the row `n + j + 1` of
`L`, and the inverse in `θ` supplies the minus sign. No signed Weyl
representative and no transpose of the leading `n + 1` coordinates occurs.

## Provenance

The proposition is derived/internal. It is the explicit algebra behind two
sources:

- Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3) I*, Ann. of
  Math. 109 (1979), registered as `jps-1979-gl3-i`: the inductive step of the
  proof of Theorem (4.5), printed pp. 197–198. The source smooths `W` as
  `W'(g) = ∫ W(g u(y)) Φ(y) dy`, where `u(y)` has the entry `y` in the first
  column of row `j + 2` (one-based). In `(W')~`, the inverse transpose turns
  `u(y)` into the upper unipotent with `-y` in column `j + 2` of the first row,
  placed to the right of `w'`. Moving it to the left of `w'` gives the entry
  `(-1)^(j+r-1) y` in column `k + 2` (p. 198). The sign comes from the source's
  conventions. That computation is the case `t = 1` (our `n = 0`). There the
  source's `r` is our `r + 1`, its `j` is our `j`, and its `k` is our `k + 1`.
- Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*, Amer.
  J. Math. 105 (1983), registered as `jpss-1983-rankin-selberg`: §(2.8), "First
  step", printed p. 395. The source notes that for `t = 1` the equivalence of
  the functional equations (2.7.2) is Theorem (4.5) of the 1979 paper. It then
  says "The proof for general t is similar, one need only replace them (4.1.5)
  (loc. cit.) by lemma (2.7) above", that is, by the unnumbered Lemma of §(2.7),
  printed pp. 394–395.

Neither source states clause 1 or clause 2 as such. This Lean interface uses the
project's actual conventions: the unsigned block Weyl element `blockWeylAt`, the
plus-sign unipotents `1 + E` and `1 + X`, the inverse transpose
`inverseTranspose`, and the published coefficient-image model equivalence
`translatedFirstDualModelEquiv`. With these conventions the sign is exactly `-1`
instead of the source's `(-1)^(j+r-1)`. The proposition records this sign as
it is. Removing it is left to the consumer, which plans to use a separately
stated even Fourier pair. The
parametrization `r = n + ((j + 1) + k + 1)` is that of the published
unequal-rank interfaces (`rectangularUnipotent`, `unequalRankSmearingUnipotent`).
No errata for either source were found in the project, the Library or the
central library. The central library's correction by Jacquet (2012) concerns the
different 1981 paper *Conducteur des représentations du groupe linéaire*. The
proposition was requested for the JPSS paired-transfer proof (task
`60e55e09-11c3-4f2f-bd81-5011f07445f7`). It should not be read as a verbatim
statement from either paper.

## Why the proposition is expected to hold

A separate proof task will establish the proposition. The expected proof is
elementary and does not use the sources:

1. Identify `blockWeylAt n r _` with `permutation (r + 1) F τ`, comparing the
   entries of `blockSum (1, weylLong (r - n) F)` blockwise.
2. Use `inverseTranspose` of a permutation matrix and the entry formulas for
   products with permutation matrices. These give
   `θ(a⁻¹ g a) p q = g⁻¹ (τ q) (τ p)`.
3. Prove clause 1 entrywise, using `g⁻¹ = 1 - E(z)` and the index computation
   above.
4. For clause 2, compare values. The left side at `x` is
   `f(w θ(x a) L(-z))`. The right side is `f(w θ(x U(z) a))`, which equals
   `f(w θ(x a) θ(a⁻¹ U(z) a))` because `θ` is multiplicative. Clause 1 then
   finishes the proof.

A private development check (not submitted) has carried out this route and
compiled it.
