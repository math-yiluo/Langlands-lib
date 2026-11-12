# Dual comparison of essential vectors (JPSS 1981, (5.3))

Author: Worker 5032. This module defines one proposition,
`Langlands.Conductor.EssentialDualComparisonStatement` (universes `uF`, `uV`).
It is a statement only: nothing here proves it, and no declaration assumes it.

## Statement

The binders are those of the published
`Langlands.Conductor.EssentialVectorLevelStatement`
([`EssentialStatement`](EssentialStatement.md)), in the same order, with one
extra hypothesis `h'` placed right after `h`:

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
  `IsNonarchimedeanLocalField F`, `T2Space F`, `TotallyDisconnectedSpace F`
  and a Borel measurable structure; any characteristic is allowed and there is
  no `PadicField` restriction;
- `n : ℕ` with the measurable and Borel structures of that statement on
  `GL_(n+1)(F)`, its unipotent subgroup, `GL_1(F)`, its unipotent subgroup,
  and the quotients `LeftUnipotentQuotient n F` and `LeftUnipotentQuotient 0 F`;
- `q`, `ψ`, `abv`, `ϖ`, `μ` and `h : IsJacquetNormalization q ψ abv ϖ μ`
  (Jacquet's normalizations, documented in [`Essential`](Essential.md));
- `h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ`, the same
  normalizations for `ψ̄ = ψ.scale (-1)`, the character `x ↦ ψ(-x)`;
- an additive Haar measure `ν` on `F` with `IsSelfDual ψ ν`.

Then for every `V : Type uV` (independent of `uF`) and
`π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V` with
`IsGeneric ψ (n + 1) π`:

- every `ℓ : glFunctionals ψ (n + 1) π` with `ℓ.val ≠ 0`;
- every `w : (coefficientModel π ℓ).toSubmodule` with
  `IsEssentialVector h π ℓ w`;
- every `ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π)`
  with `ℓ'.val = (dualFunctional ψ π ℓ).val`;
- every `w' : (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule`
  with `IsEssentialVector h' (inverseTransposePullback π) ℓ' w'`;
- every `c : ℂˣ` and `m : ℤ` with
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`;

there is `C : ℂ` such that for every `g : GeneralLinear ((n + 1) + 1) F`

```
dualFunction (n + 1) w.val.val g = C * w'.val.val (g * rankInclusion 1 (scalar (ϖ ^ m)))
```

The rank is `r = n + 2 ≥ 2`; `n = 0` (rank two) is included. The identity is
asserted at every element of the whole group, for the actual essential vectors.
The exponent `m` is an integer; it is not truncated to a natural number.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214; registered
source `jpss-1981-conductor`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`,
SHA-256 `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`
(printed page 199 is PDF page 1). Pages read rendered:

- (1.2), display (3), printed page 200 (PDF page 2):
  `W̃(g) = W(w_r ᵗg⁻¹)` with `w_r` the antidiagonal permutation matrix, and
  `W̃ ∈ W(π̃; ψ̄)` for `W ∈ W(π; ψ)`.
- (5.1), display (1), printed page 211 (PDF page 13): `m` is the integer with
  `ε_π(X, ψ) = C X^m`, where `X = q^(-s)`.
- (5.3), printed page 213 (PDF page 15): `W` is the essential vector of
  `W(π; ψ)`, `W'` the essential vector of `W(π̃; ψ̄)`,
  `W₁(g) = W'(g a)` with `a = diag(ϖ^m, ϖ^m, ..., ϖ^m, 1)`, and "il y a une
  constante `C'` telle que `Ψ(X, W̃, X₁, ..., X_(r-1)) = C' Ψ(X, W₁, X₁, ...,
  X_(r-1))`. D'après le lemme (3.4) cela implique `W̃ = C' W₁` sur le
  sous-groupe (4.2)(3). Donc, d'après une remarque déjà faite, `W̃ = C' W₁`."

The statement is the final equality `W̃ = C' W₁`, with:

- `W̃` the published `dualFunction (n + 1) w.val.val`, which is
  `g ↦ w(weylLong · inverseTranspose g)`, that is, `W(w_r ᵗg⁻¹)`;
- `rankInclusion 1 (scalar (ϖ ^ m))` the block matrix `diag(ϖ^m · 1_(n+1), 1)`,
  that is, `a = diag(ϖ^m, ..., ϖ^m, 1)` of rank `n + 2`; so
  `w'.val.val (g * rankInclusion 1 (scalar (ϖ ^ m)))` is `W₁(g)`;
- `C` the source's `C'`;
- `m` the exponent of the epsilon factor. The published
  `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)` says that the
  epsilon factor of `π` against the trivial character of `GL_1(F)` is
  `c q^(-ms) = c X^m`, which is the source's `ε_π(X, ψ) = C X^m`. As in
  `EssentialVectorLevelStatement`, the Library uses the JPSS pair epsilon factor
  of `π × 1`; its agreement with the Godement–Jacquet factor `ε_π` of the source
  is a separate theorem, discussed in [`EssentialStatement`](EssentialStatement.md).
  The source proves `m ≥ 0` only after (5.3), from this very identity, so `m`
  is kept in `ℤ`.

The essential vectors are the corrected ones of H. Jacquet, *A correction to
Conducteur des représentations du groupe linéaire*, Pacific J. Math. 260
(2012), 515–525 (registered source `jacquet-2012-conductor-correction`, SHA-256
`98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`; printed
pages 515–517 = PDF pages 2–4: normalizations, Theorem 1 and the uniqueness
remark). The predicate `IsEssentialVector` is used unchanged; a proof must not
use the flawed 1981 existence argument.

## The dual model

The source places `W'` in the Whittaker model `W(π̃; ψ̄)` of the contragredient.
Here the dual model is the coefficient model of the published
`inverseTransposePullback π` (the representation `g ↦ π(ᵗg⁻¹)` on the same
carrier `V`) for the functional `ℓ'` with `ℓ'.val = (dualFunctional ψ π ℓ).val`,
that is `ℓ'(v) = ℓ(π(w_r) v)`. The published `dualFunction_coefficient` shows
that `dualFunction` sends the coefficient of `v` for `ℓ` to the coefficient of
`v` for this functional, so `W̃` lies in exactly this model, as in the source.
Fixing this specific `ℓ'` makes the statement independent of two facts that
are not part of `IsGeneric`: the isomorphism of the inverse-transpose pullback
with the contragredient (Gelfand–Kazhdan), and multiplicity one of Whittaker
functionals. The functional `ℓ'` is a standard functional for `ψ.scale (-1)`
because the standard character of `ψ.scale (-1)` is the inverse standard
character (published `standardCharacter_scale_neg_one`); the published
`EssentialDualSetup.scaledDualFunctional` constructs such an `ℓ'`, and
`isGeneric_inverseTransposePullback` shows the pullback is generic for
`ψ.scale (-1)`.

## The hypothesis `h'`

`h'` costs no generality: `ψ.scale (-1)` again has conductor `O`, and all other
fields of `IsJacquetNormalization` (residue cardinality, uniformizer,
normalized absolute value, quotient measure, Borel quotients) do not involve
`ψ`. The published `IsJacquetNormalization.scaleNegOne` derives `h'` from `h`.
It is kept as a binder because the essential-vector predicate of the dual model
is indexed by a normalization proof for `ψ.scale (-1)`.

## Why `C` only exists

The source asserts only the existence of a constant `C'`, without a formula
for it and without asserting `C' ≠ 0`. The statement records exactly this: it
asserts the existence of `C : ℂ` and claims neither `C ≠ 0` nor a formula.

The functions on both sides do not depend on how the Whittaker functionals are
normalized. For `a ≠ 0` the coefficient of `v` for `a ℓ` is the coefficient of
`a v` for `ℓ`, so `coefficientModel π (a ℓ) = coefficientModel π ℓ` as spaces
of functions on the group, and likewise for `ℓ'`. `IsEssentialVector`
constrains the function itself (the normalized identity of Jacquet (2012),
Theorem 1, and right `GL_(n+1)(O)`-invariance of its restriction), and by
Jacquet's uniqueness remark (printed page 517) at most one function in the
model satisfies it. So rescaling `ℓ`, and with it `ℓ'`, by a nonzero scalar
leaves both essential functions, and hence the relation defining `C`,
unchanged.

## What this statement does not supply

It assumes both essential vectors and the epsilon factor, so it gives neither
existence nor uniqueness of essential vectors (Jacquet 2012, Theorem 1), nor
existence of the epsilon factor. It also is not the conductor theorem JPSS (5.1):
deducing `K(m)`-invariance needs in addition the `H(0)`-invariance of `w` and
`w'` (integral last-row support and mirabolic restriction injectivity), and the
dimension and minimality parts need the argument on printed pages 213–214. The
published `mem_levelFixedVectors_of_rankInclusion_dual_comparison` consumes
exactly this conclusion together with those invariances.

## Imports

Only the published `Langlands.Representation.Conductor.EssentialStatement`,
whose import closure supplies `IsJacquetNormalization`, `IsEssentialVector`,
`IsPairEpsilonFactor`, `rankOneCharacter`, `IsSelfDual`, `dualFunction`,
`dualFunctional`, `inverseTransposePullback`, `UnitaryAdditiveCharacter.scale`,
`rankInclusion` and `scalar`.
