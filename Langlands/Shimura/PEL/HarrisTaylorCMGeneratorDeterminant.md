# Finite generating families for the normalized Harris determinant

Author: Worker 344.

This internal derived construction reduces the existing normalized
Harris–Taylor rational Lie determinant condition to a single fixed finite
integer module-generating family of the actual Harris order. At every
finite free Lie chart and smaller open, it further reduces that one polynomial
identity to finitely many coefficient equations. The coefficient index set
depends only on the generating-family size and the two module ranks.
It does not depend on which coefficients vanish in a particular action.

The provenance is internal. The construction uses the published
`HarrisTaylorCMLieDeterminant` condition, the actual rational Lie section
action, the actual regular Hodge and descended reflex determinants, and
`harrisHodgePELIntegralOrder_finite` from
[HarrisIntegralOrder.md](HarrisIntegralOrder.md). The generic algebraic
proofs below use Mathlib finite-generation, linear-combination and homogeneous
polynomial results. No new theorem from the original literature is assumed.
The arithmetic normalization and its source comparisons remain those in
[HarrisTaylorCMLieDeterminant.md](HarrisTaylorCMLieDeterminant.md).

## Linear substitution

For finite new indices `ι`, old indices `η`, and a coefficient matrix
`r : ι → η → R`, `HodgeDeterminant.linearVariables r` is the ring map

```text
MvPolynomial η R →+* MvPolynomial ι R
X j ↦ ∑ i, C (r i j) * X i,
C a ↦ C a.
```

`map_linearVariables` proves compatibility with every homomorphism of
commutative coefficient rings, mapping each entry of `r` through that
homomorphism. The proof applies the multivariate evaluation identity and
checks the substituted expressions.

For an actual module basis `b` and a finite family of endomorphisms `f`,
`polynomial_sum_smul_family` proves

```text
polynomial b (fun i => ∑ j, r i j • f j)
  = linearVariables r (polynomial b f).
```

The proof commutes the substitution with the determinant, compares each
universal matrix entry, exchanges the two finite sums and uses commutativity
of the coefficient ring. `polynomial_sum_zsmul_family` specializes to
integer combinations. No field, domain or reducedness hypothesis occurs.

`lieRationalSectionDeterminant_sum_zsmul_family` applies the integer
identity to the actual rational Lie action, on the same free chart and the
same smaller open. The action preserves sums and integer scalar
multiplication because it is a ring homomorphism. The proof uses the
existing finite basis of actual sections supplied by that chart.

`kottwitzHodgeDeterminant_sum_zsmul_family` applies the same identity to
the actual positive regular Hodge representation, using its existing tensor
inclusions and left action. The `_ReflexDeterminant_` version descends
the identity through the injective inclusion of the actual reflex field
into `ℂ`. The `_ReflexDeterminantBaseChange_` version then maps it
through any homomorphism to a commutative coefficient ring.

## One generating family

The normalized results retain the universe-zero hypotheses of the imported
condition: a totally real number field `E`, a totally complex quadratic
number-field extension `F/E`, the actual central simple unitary datum `D`
of degree `n` on `A`, its compatible rational, `E` and `F` algebra structures
and scalar towers, an imaginary quadratic CM number field `L`, an algebra
structure of `L` on `F`, an embedding `τ₀ : L →+* ℂ`, and signature charts
for precisely `harrisCMSection E (algebraMap L F) τ₀`.
An actual scheme `S`, morphism `p : S ⟶ Spec F`, abelian scheme `B/S`,
and rational action `i : A →ₐ[ℚ] End0 B` are fixed.

`harrisTaylorCMRationalLieDeterminantConditionAt_sum_zsmul` proves that
the existing local condition for any finite order-valued family `g`
implies the condition for every integer linear-combination family
`fun k => ∑ j, r k j • g j`. Both polynomials undergo the same
`linearVariables` substitution. The coefficient maps commute with it,
including the unchanged conjugated `harrisTaylorReflexToCM C` map
and the actual map `secHom p V.left` into the full section ring.

For any finite `g` whose integer linear span is the whole actual order,
`harrisTaylorCMRationalLieDeterminantConditionAt_iff_generators` proves
that testing `g` is equivalent to testing every finite family, on the
same fixed Lie chart `e` and smaller open `V`. For each family `a`, the
span hypothesis makes `Fintype.linearCombination ℤ g` surjective.
Choose integer coefficients for each `a k`, rewrite the family and apply
the preceding substitution theorem. The reverse direction simply selects
`g` from the quantified families. The generators need not be a basis.

`harrisHodgePELOrderGeneratorCount` and
`harrisHodgePELOrderGenerators` choose one finite generating family from
the already proved instance `Module.Finite ℤ (D.harrisHodgePELIntegralOrder C)`.
`span_harrisHodgePELOrderGenerators` proves its spanning property.
This family is chosen once from the arithmetic data and charts; it does
not depend on `S`, `p`, `B`, `i`, a Lie chart, or a smaller open.

`HarrisTaylorCMGeneratorLieDeterminantCondition` requires the original
local polynomial identity for that one chosen family on every finite
free Lie chart and every smaller open. Its `_iff` theorem proves exact
equivalence with `HarrisTaylorCMRationalLieDeterminantCondition`.
Its `_iff_reflex` theorem composes that equivalence with the existing
normalized-reflex-base comparison. Its `_iso` theorem transfers the
existing invariance under an actual equivariant rational isomorphism of
abelian schemes, using the displayed intertwining identity for every
element of `A`.

## A finite coefficient index set

For a finite variable type `σ`,
`HodgeDeterminant.homogeneousEquationIndices σ m n` is the finite set
of exponent vectors whose total degree is either `m` or `n`.
Finiteness follows from `Finsupp.finite_of_degree_eq` for each degree.
`mem_homogeneousEquationIndices` states this precise membership test.
`eq_iff_finite_coeff` proves that a homogeneous polynomial of degree `m`
equals a homogeneous polynomial of degree `n` exactly when their
coefficients agree on this finite set. Outside it, both coefficients
vanish by homogeneity.

`lieRationalSectionDeterminant_isHomogeneous` records that the actual
rational Lie section polynomial has degree `Fintype.card I`, the rank of
the chosen free chart. The prescribed reflex polynomial, after both
coefficient maps, has degree `Module.finrank ℂ (D.kottwitzHodgeModule C)`
by the existing Hodge and reflex homogeneity theorems.

`harrisTaylorCMRationalLieDeterminantConditionAt_iff_finite_coeff`
therefore expresses the original local condition for any finite
order family as equality of those finitely many coefficients in
`Γ(S, V.left)`. The two ranks need not be assumed equal: the index set
contains both possible homogeneous degrees.

Finally,
`harrisTaylorCMRationalLieDeterminantCondition_iff_finite_generator_coeff`
combines the fixed generating family and the finite coefficient
criterion. It retains quantification over every finite Lie chart and
smaller open; at each such chart and open it tests only the displayed
finite set of equations for the one chosen order family.

These identities hold in the full section ring, including rings with
nilpotents and zero rings. They require no injectivity of either
coefficient map used to reach that ring. Empty families and rank-zero
charts remain covered. The result supplies finite local coefficient
equations, not a construction of their common zero scheme or a claim
that the entire moduli problem is represented.
No abelian scheme satisfying the condition, geometric dimension
condition, full Lie-plus equivalence, moduli scheme, admissibility,
smoothness, projectivity or natural representability isomorphism is
constructed here. The exact published
`DivisionCMRepresentabilityStatement` and all its imported pairs are
preserved.
