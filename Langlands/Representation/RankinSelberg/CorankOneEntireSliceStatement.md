# Entire dependence of corank-one determinant-slice coefficients

Module
`Langlands.Representation.RankinSelberg.CorankOneEntireSliceStatement`
contains the single closed proposition definition
`Langlands.RankinSelberg.CorankOneEntireSliceStatement.{uF,uV}`.
It states restricted integrability and entire dependence for actual corank-one
determinant-slice integrals. It supplies no Lean proof of the proposition.

## Source and derived provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. The retained file is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The exact locators are Section (4.5), printed pages 408–409, especially
the uniform compact open level and pointwise analyticity in the lemma and
the compact-support argument for analytic determinant-slice coefficients on
page 409; and Sections (6.1)–(6.3), printed pages 427–438. Section (6.1)
on page 427 refers back to (4.5) when restricting the twist of the second,
rank-one block to large positive real parameters. Section (6.3) on page 432
repeats that restriction, and pages 433–438 develop the determinant coefficients
and polynomial-cleared functional equation. These pages were read visually
from the registered scan: one-based PDF pages 43–44 and 62–73.
No JPSS-specific erratum was found in the bounded project-note and literature
index search.

Provenance is **derived**. Page 409 treats an equal-rank integral with a
Schwartz–Bruhat factor and a particular induced deformation. This proposition
extracts its common-level support and finite-evaluation argument for a general
corank family, with the corank embedding furnishing the bound otherwise supplied
by the last-row test function. The generality below is an internal consequence
of that argument, not a verbatim theorem of JPSS. The rationale below explains
the extraction; its formal proof is a separate obligation.

## Quantifiers, groups and measures

The definition quantifies over every prime `p`, every
`F : PadicField.{uF} p`, every
`ψ : UnitaryAdditiveCharacter F.Carrier`, and every `r : ℕ`, including `r = 0`.
Write `T = F.canonicalTopologicalData`, `d = r + 1`, and
`Q = LeftUnipotentQuotient r F.Carrier = N_d \ GL_d(F)`.
The additive-character structure already includes continuity, nontriviality
and values in the unit circle.

All field, matrix, subgroup and quotient topologies are induced from
`T.topology`. The statement installs `T.valuativeRel`, `T.localField`,
and the Borel measurable structures of the field, `GL_d`, `N_d` and `Q`,
with their actual `BorelSpace` certificates. The absolute value is exactly
`normalizedAbsoluteValue T`, with uniformizer norm `q_F⁻¹`, where
`q_F = T.residueCardinality`.

The ambient and unipotent measures are exactly
`generalLinearHaar F.Carrier r` and `unipotentHaar F.Carrier r`.
These are normalized by the integral matrix subgroup and integral unipotent
subgroup, respectively. The definition retains a supplied instance of
`Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)`, a supplied Borel
measure `ν` on `Q`, and the actual hypothesis

```text
QuotientIntegration.IsCompatible (upperUnipotent (r+1) F.Carrier)
  (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν.
```

This compatibility means that `ν` is nonzero and regular, invariant under
the actual right translations, and satisfies the Weil integral formula and
orbital-average integrability for compactly supported continuous tests.
Regularity includes finiteness on compact sets. No quotient measure is chosen
by the proposition.

The field universe `uF` and the original representation-carrier universe `uV`
are independent. The definition has no free term parameters.

## The two inputs

The fixed input is any original complex module `V : Type uV` with
`AddCommGroup V` and `Module ℂ V`, and any actual representation
`τ : Representation ℂ (GeneralLinear d F.Carrier) V` satisfying

```text
IsOfWhittakerType r (inverseStandardCharacter ψ r) τ.
```

This is the full published condition: admissibility (including smoothness),
finite generation over the group algebra, and a linear equivalence of the
whole inverse-character functional space with `ℂ`. It does not require
irreducibility, unitarity or a central character.
For every `ℓ : glInverseFunctionals ψ r τ`, including `ℓ = 0`, the statement
takes every
`Wprime : (coefficientModel τ ℓ).toSubmodule`.
Thus `Wprime.val` is an actual inverse-character Whittaker function on `GL_d`,
in the coefficient image of this original representation and this functional.
It is represented by `g ↦ ℓ.val (τ g v)` for some original vector `v`.
No equivalence with the entire representation or with all equivariant functions
is assumed. Zero coefficients and reducible `τ` are allowed.

The varying input is directly
`U : ℂ → WhittakerFunctions ψ (r + 1)`, whose values are standard-character
equivariant functions on the actual `GL_(d+1)(F)`. There are exactly two extra
family hypotheses:

1. There exists one compact open subgroup `K` of this actual larger group
   such that `(U u).val (g * k) = (U u).val g` for every `u`, `g`, and `k : K`.
   The existential choice of `K` precedes all complex parameters.
2. For every actual `g` and every `u : ℂ`,
   `AnalyticAt ℂ (fun z => (U z).val g) u`.

In particular the varying family has no supplied representation carrier,
inducing realization, coefficient-image condition, asymptotic expansion,
support hypothesis, or integral-analyticity premise.

## Exact integral conclusion

For every integer `m`, the conclusion is the conjunction of
integrability for every `u` and analyticity at every `u`:

```text
∀ u, SliceIntegrableAt T ν
  (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U u) Wprime.val 0) m

∀ u, AnalyticAt ℂ
  (fun z => sliceCoefficient T ν
    (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) Wprime.val 0) m) u.
```

These use the literal published integrand, quotient and restricted Bochner
integral. On a representative `g : GL_d(F)`, the integrand at parameter `z` is

```text
(U z).val (rankInclusion 1 g) * Wprime.val.val g
  * determinantWeight (normalizedAbsoluteValue T) g (0 - 1/2).
```

Here `rankInclusion 1 g = diag(g,1)`. The spectral variable is `s = 0`;
the existing corank shift `s - 1/2` is retained, so the determinant factor
is `|det g|^(-1/2)`, rather than `1`. The complex family parameter `z`
is distinct from this fixed spectral variable. Standard and inverse
unipotent characters cancel, so this is the actual function on `Q`.

`determinantSlice T r m` is `{q | determinantOrder T r q = m}`.
For a representative this is `T.ord (det g) = m`, equivalently
`|det g| = q_F^(-m)`. `SliceIntegrableAt` means `IntegrableOn` for this set
and `ν`, and `sliceCoefficient` is its actual restricted Bochner integral.
The first conclusion ensures that the second concerns genuinely integrable
coefficients, including all zero cases.

## Why the derived assertion is sound

The following is a proof rationale, not a supplied Lean proof or an additional
premise of the definition.

Choose a sufficiently deep principal congruence subgroup of `GL_(d+1)(O_F)`
inside the common level `K`. It is normal in that integral compact group.
In an Iwasawa representative `g = n a k` for `GL_d`, write
`a = diag(a₁,…,a_d)`, and append `a_(d+1) = 1` in the corank embedding.
For the value of any `U z` at `diag(a k,1)` to be nonzero, its right invariance
and left unipotent covariance force
`ψ((a_i/a_(i+1)) x) = 1` for all `x` in fixed small additive lattices,
for every simple root `i = 1,…,d`. The level and these lattices work for
all `z` and all `k` in the integral compact group.
Since `ψ` is nontrivial, the annihilator of such a lattice is bounded.
Consequently there are constants independent of `z` with
`|a_i/a_(i+1)| ≤ C_i` and, for the final root, `|a_d| ≤ C_d`.
This last bound uses the appended coordinate `1`; no central-character
or asymptotic-expansion argument is needed.

These inequalities bound every `|a_i|` above. On the fixed slice,
`∏ |a_i| = q_F^(-m) > 0`, so they also bound each `|a_i|` below.
Thus all diagonal entries range in compact annuli in `Fˣ`. Together with
the compact Iwasawa factor this gives one compact subset of `N_d \ GL_d`
containing the supports of all slice-restricted products, independently
of `z`. It is the supported part that is compact; a whole determinant
slice need not be compact.

Smoothness of `τ` gives an open right stabilizer of the fixed coefficient
`Wprime`. Intersect it with the inverse image of `K` under `rankInclusion 1`,
and refine to a compact open subgroup `J` with determinant norm `1`.
Then all the slice-restricted products are right `J`-invariant.
The corresponding right orbits on the quotient are compact open, and the
common compact support meets only finitely many of them.
They are disjoint or equal, so a fixed finite list covers all supported
orbits. Each orbit has finite `ν`-mass by compatibility's regularity.
The products are constant on these orbits and vanish elsewhere;
this yields their restricted Bochner integrability.

Choose one representative `g_j` for each of these finitely many quotient
orbits. The restricted integral is then a finite linear combination of
the values `(U z).val (rankInclusion 1 g_j)`, with coefficients incorporating
the fixed value of `Wprime`, the determinant weight, and the orbit mass.
The list and coefficients do not depend on `z`.
Pointwise analyticity and closure under finite linear combinations give
analyticity at every `u`. This finite decomposition is an argument to be
proved, not a replacement definition of the integral or an assumed expansion.
When `r = 0`, the same argument has one diagonal coordinate, and its norm
is already fixed by the determinant order; zero functionals and vectors
give identically zero integrands.

## Relation to deformation and specialization

The published theorem `Langlands.RankinSelberg.twoBlockWhittakerDeformation`
in `TwoBlockWhittakerDeformationProof` constructs inverse-character entire
families on actual normalized lower induction, with `+u` on the first block.
It gives one common compact open level and pointwise entire values. It does
not assert analytic dependence of the slice integrals.
The present proposition instead starts with a supplied standard-character
family on the larger corank group and concludes slice integrability and
entire coefficients. It neither constructs that family nor identifies it
with the first-block inverse-character family.

Using the second-block rank-one twist in Section (6.1), or a plus-character
family in that role, still requires the appropriate separate adapter.
Continuing factor polynomials and specializing a polynomial-cleared formal
functional equation are also separate obligations. This proposition assumes
no final factor identity, unrestricted multiplicativity, or renamed version
of its conclusion. It asserts no convergence of the unsliced integral over
the whole complex plane and proves neither parent adjacent-rank factor
proposition.
