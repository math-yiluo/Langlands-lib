# Integral last-row support of the essential vector

Author: Worker 5032. This module defines one proposition,
`Langlands.Conductor.EssentialIntegralLastRowSupportStatement` (universes `uF`,
`uV`). It is a statement only: nothing here proves it, and no declaration
assumes it.

## Statement

The quantifiers up to the representation are copied verbatim from the published
`Langlands.Conductor.EssentialVectorStatement`
([`EssentialStatement`](EssentialStatement.md)):

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`
  and `IsNonarchimedeanLocalField F` (any characteristic; no `PadicField`
  restriction);
- `n : ℕ` and the measurable and Borel structures on `GL_(n+1)(F)`, on its upper
  unitriangular subgroup, on `GL_1(F)`, and the measurable structures on the
  quotients `LeftUnipotentQuotient n F = N_(n+1) \ GL_(n+1)(F)` and
  `LeftUnipotentQuotient 0 F`;
- `q : ℕ`, `ψ : UnitaryAdditiveCharacter F`, `abv : AbsoluteValue F ℝ`,
  `ϖ : Fˣ`, a measure `μ` on `LeftUnipotentQuotient n F`, and
  `h : IsJacquetNormalization q ψ abv ϖ μ`. The published normalization says that
  `q` is the residue cardinality, `ϖ` is a uniformizer, `abv` is the normalized
  absolute value (`abv ϖ = q⁻¹`, `abv = 1` on valuation units), `ψ` has
  conductor `O` (`HasIntegerConductor ψ`), and `μ` is the quotient measure
  compatible with the Haar measures giving `GL_(n+1)(O)` and `N_(n+1)(O)` mass
  one, with Borel quotients. These are Jacquet's normalizations on printed pages
  515–516 of Jacquet (2012).

Then, for every complex vector space `V : Type uV` (the carrier universe is
independent of `uF`) and every representation
`π : Representation ℂ (GeneralLinear ((n + 1) + 1) F) V` with
`IsGeneric ψ (n + 1) π` (irreducible, admissible, with a nonzero standard
`ψ`-Whittaker functional), every `ℓ : glFunctionals ψ (n + 1) π` with
`ℓ.val ≠ 0`, every `w : (coefficientModel π ℓ).toSubmodule` with
`IsEssentialVector h π ℓ w`, and every `g : GeneralLinear (n + 1) F`:

```
w.val.val (rankInclusion 1 g) ≠ 0 →
  ∀ j : Fin (n + 1), g.val (Fin.last n) j ∈ (ValuativeRel.valuation F).integer
```

Here `w.val.val : GL_(n+2)(F) → ℂ` is the actual Whittaker function of the
model vector `w`, `rankInclusion 1 g` is the published block matrix
`diag(g, 1)`, `g.val (Fin.last n) j` is the `j`-th entry of the last row of `g`,
and `(ValuativeRel.valuation F).integer` is the valuation ring `O` of `F`.

### Rank conventions

`π` acts on `GL_r(F)` with `r = n + 2 ≥ 2` and `g` ranges over `GL_(r-1)(F)`,
exactly as in the source. Rank `r = 2` (`n = 0`) is included: then `g` is a
`1 × 1` matrix and the conclusion says that `g` itself is integral when
`w(diag(g, 1)) ≠ 0`.

### The essential vector used

`IsEssentialVector h π ℓ w` is the published corrected essential-vector
predicate of [`Essential`](Essential.md), unchanged: `w` satisfies the
Rankin–Selberg identity of Jacquet (2012), Theorem 1 (printed page 517), with
the standard L-polynomial of `π`, and its restriction to `diag(GL_(n+1), 1)` is
right `GL_(n+1)(O)`-invariant (`IsIntegralInvariantOnRestriction π ℓ w`).
These are the two conditions under which Jacquet (2012), printed page 517,
recalls that the vector is unique and calls it the essential vector.

### Relation to the published restriction invariance and support predicate

The published `IsIntegralInvariantOnRestriction π ℓ w` says
`w(diag(g k, 1)) = w(diag(g, 1))` for `k ∈ GL_(n+1)(O)`. It constrains the
dependence of `w(diag(g, 1))` on the right `GL_(n+1)(O)`-coset of `g`, but says
nothing about where `g ↦ w(diag(g, 1))` vanishes. The conclusion here is a
support condition. It is not a formal consequence of the invariance, which
only says that the function is constant on each right coset `g GL_(n+1)(O)`;
such a function may be nonzero at matrices with a nonintegral last row. In the
source the support is derived from the Rankin–Selberg identity, as recalled
below.

The conclusion is, by definition, the published predicate
`HasIntegralLastRowSupport ψ (ValuativeRel.valuation F).integer w.val` of
`Langlands.Representation.Conductor.JacquetRestrictionInvariance`; this module
writes the formula out instead of importing that module. Together with the
restriction invariance and injectivity of mirabolic restriction, the published
`mem_jacquetFixedVectors_of_integral_restriction` turns it into invariance of
`w` under the group `H(0)` of JPSS (5.2) (the matrices `(h u; 0 1)` with
`h ∈ GL_(r-1)(O)` and integral column `u`).

### What this statement does not supply

It assumes an essential vector and says nothing when none exists, so it does not
give existence (Jacquet 2012, Theorem 1) or uniqueness of the essential vector.
It also does not give the conductor theorem JPSS (5.1): that further needs the
epsilon factor of `π`, the comparison (5.3) with the essential vector of the
contragredient, invariance under the transposed group `ᵗH(m)`, and the
minimality argument on printed pages 213–214.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des
représentations du groupe linéaire*, Math. Ann. 256 (1981), 199–214; registered
source `jpss-1981-conductor`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`,
SHA-256 `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`
(one page per printed page; printed page 199 is PDF page 1).

- Section (5.2), printed page 211 (PDF page 13): introduces `H(a)` and reduces
  the `H(0)`-invariance of the essential vector to the following lemma.
- Lemma, printed page 212 (PDF page 14), rendered and read: "Si `W` est le
  vecteur essentiel de `W(π; ψ)` alors la relation `W(g 0; 0 1) ≠ 0`,
  `g ∈ G_(r-1)`, entraîne que la dernière ligne de `g` est à coefficients
  entiers." Its proof splits by the degree `u` of `P_π`: `u = r` (unramified
  case), `u < r - 1` (lower-rank spherical function and the unramified
  Rankin–Selberg product), and `u = r - 1` (the characteristic function of the
  integral last row), using Lemma (3.4).

The 1981 existence proof of the essential vector contains an error, corrected
in H. Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012), 515–525; registered source
`jacquet-2012-conductor-correction`, file
`/home/taskhub/central-library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`,
SHA-256 `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
Printed pages 515–517 (PDF pages 2–4) give the normalizations, Theorem 1 and
the uniqueness remark that define the essential vector used here. The lemma of
(5.2) is stated for that vector; a proof must not use the flawed 1981
existence argument.

## Imports

Only the published `Langlands.Representation.Conductor.Essential`, which
supplies `IsJacquetNormalization`, `IsEssentialVector` and, through its imports,
`IsGeneric`, `glFunctionals`, `coefficientModel`, `rankInclusion` and the
quotient types.
