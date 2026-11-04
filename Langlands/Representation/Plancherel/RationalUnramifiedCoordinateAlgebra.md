# Coordinate algebra of actual unramified characters

Author: Worker 200.

This derived construction identifies the existing algebra of actual unramified
character evaluations with the complex group algebra of the actual integer
valuation image. For a connected reductive group, its existing integer basis
identifies that algebra with a finite-variable Laurent polynomial algebra.
The monomial formula agrees with the existing finite coordinates on actual
unramified characters.

## Source and scope

Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, I.1, printed pp.239–240 (PDF pp.5–6), defines
`G¹`, the continuous unramified characters `X(G)`, their complex torus
structure, and the positive valuation convention. IV.1, printed pp.276–277
(PDF pp.42–43), uses the algebra `B` of polynomial functions on `X(M)`
and the elements `b_m(χ) = χ(m)` in the polynomial and rational
operator-family definitions. Registered source:
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The Lean argument is an internal algebraic derivation from already constructed
actual characters, positive characters, integer image, finite image basis and
canonical point topology. It realizes the evaluation-generated scalar algebra
as Laurent polynomial functions in the existing finite character coordinates.
It does not construct a scheme or a complex manifold, compare a scheme
spectrum with its complex points, or identify the image rank with the
dimension of the source's split central real space. Those additional
comparisons are not asserted by the algebra equivalences.

## Actual objects and hypotheses

The field `F : Type u` has instances `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`. The group scheme
is `G : GroupScheme (Spec (CommRingCat.of F))`. There is no restriction on
characteristic, splitness or quasisplitness.

Write `Λ = rationalDiscreteValuationImage G`. This is the actual image
of `rationalCharacterValuation G`, with its existing discrete topology,
not a freely selected lattice. Write `X_Λ = rationalImageCharacters G`.
Its members are the continuous homomorphisms `Λ → ℂˣ`.

The first group-algebra evaluation needs neither reductivity nor any chosen
point topology. To compare with the existing continuous unramified characters
on `GroupScheme.rationalPoints G`, the `PointTopology` section assumes that
point group has a topology and displays

```text
hp : Continuous (rationalValuationImageProjection G).
```

The actual character space is
`unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)`.
Its scalar algebra is exactly the existing `unramifiedRegularFunctions`
for this same rational norm-character family.

Only the finite Laurent description adds
`hG : GroupScheme.IsConnectedReductive G`. It uses
`rationalReductiveValuationBasis G hG`, whose finiteness is already
supplied by `GroupScheme.rationalCharacterLattice`. Its index set is
`Fin (rationalImageRank G)`. The rank is the rank of the actual image;
the rank-zero case is included.

The `CanonicalTopology` section assumes `IsAffine G.X.left` and
`LocallyOfFiniteType G.X.hom`. Its point topology is exactly
`rationalPointTopology F G.X`, and the published
`continuous_rationalValuationImageProjection G` discharges `hp`.
Affineness and local finite type hold for a connected reductive group;
they are displayed as instances in this section's interfaces.

## Faithful evaluation on image characters

`rationalImageCharacters_separate` says that two elements of `Λ` with
equal evaluation at every member of `X_Λ` are equal. The actual image is
contained in the integer dual of rational characters. For each rational
character `ψ`, its integer coordinate, cast to `ℝ`, is therefore an
additive real functional on `Λ`. The existing
`rationalImagePositiveCharacter` constructs a positive complex character
from this functional. Applying logarithmic modulus to the alleged equality
of its evaluations, and using `rationalImageRealPart_positive`, recovers
the real functional's values. Injectivity of the integer cast gives equality
of that integer coordinate. Extensionality over all `ψ` gives equality of
the original image elements. No finite-rank hypothesis enters this proof.

`rationalImageEvaluationHom G a` is evaluation at `a`, viewed as a monoid
homomorphism from `X_Λ` into `ℂ`. These homomorphisms are distinct by
separation. Mathlib's `linearIndependent_monoidHom` then proves
`rationalImageEvaluations_linearIndependent`, the Dedekind independence
of these complex-valued evaluation functions.

`rationalImageCoordinateEvaluation` is the algebra homomorphism

```text
ℂ[Additive Λ] →ₐ[ℂ] (X_Λ → ℂ),
```

where `ℂ[Additive Λ]` is `AddMonoidAlgebra ℂ (Additive Λ)`.
It is constructed with `AddMonoidAlgebra.lift`. The single-monomial
formula is `single a c ↦ (χ ↦ c * χ(a))`, with the unit value included
in `ℂ`. Its injectivity follows from the preceding linear independence:
the coefficient linear equivalence identifies evaluation with the finite
linear-combination map, which is injective.

## Comparison with the actual scalar algebra

`rationalUnramifiedCoordinateEvaluation G hp` transports the preceding
function-valued homomorphism along `rationalImageUnramifiedEquiv G hp`.
It precomposes each function with actual character descent. The theorem
`rationalUnramifiedCoordinateEvaluation_single_projection` proves

```text
single (Additive.ofMul (v(g))) c ↦ (χ ↦ c * χ(g)),
```

where `v = rationalValuationImageProjection G`. It uses the existing
`rationalImageUnramifiedDescend_projection` equality. Transport by an
equivalence preserves injectivity.

`rationalUnramifiedCoordinateEvaluation_range` identifies the range
with `unramifiedRegularFunctions` for the rational norm characters.
For one inclusion, induction on the additive monoid algebra reduces to
its monomials, addition and scalar multiplication. Surjectivity of the
actual image projection supplies an actual point for each monomial;
its evaluation is a generator of the scalar algebra. That subalgebra
is closed under addition and complex scalar multiplication. For the
other inclusion, every actual point evaluation is the image of its
corresponding formal monomial with coefficient one, so the generated
subalgebra lies in the range.

`rationalUnramifiedCoordinateAlgebraEquiv G hp` restricts the injective
homomorphism to its range and uses the proved range equality:

```text
ℂ[Additive Λ] ≃ₐ[ℂ] unramifiedRegularFunctions (rational norm characters).
```

Its application theorem records that the underlying function is the
original evaluation, with no replacement of the character space or generators.
`rationalCanonicalUnramifiedCoordinateAlgebraEquiv` specializes this
construction to the canonical point topology.

## Finite Laurent description and evaluation

Put `r = rationalImageRank G` and
`b = rationalReductiveValuationBasis G hG`. Then
`rationalImageLaurentAlgebraEquiv` transports the monoid algebra along
the inverse additive equivalence underlying `b.equivFun`:

```text
AddMonoidAlgebra ℂ (Fin r → ℤ) ≃ₐ[ℂ] ℂ[Additive Λ].
```

The source is the finite-variable Laurent polynomial algebra, written as
finite formal complex combinations of integer exponent vectors. Composing
with the preceding actual-image equivalence gives
`rationalUnramifiedLaurentAlgebraEquiv G hp hG`. The canonical topology
specialization is `rationalCanonicalUnramifiedLaurentAlgebraEquiv`.

`rationalImageCharacter_basis_formula` first proves evaluation at any
image element as a Laurent monomial in basis values. Its proof reconstructs
the character from its existing basis coordinates and applies
`rationalImageCharacterOfCoordinates_apply`.

The two Laurent-algebra single-monomial theorems use
`AddMonoidAlgebra.domCongr_single` and that basis formula. The inverse
law of `b.equivFun` identifies the resulting exponents with the original
integer vector. In the canonical topology, writing `z_i(χ)` for
`rationalCanonicalUnramifiedCharacterCoordinates G hG χ i`, the result is

```text
single m c ↦ (χ ↦ c * ∏ i, z_i(χ) ^ m(i)).
```

The product is formed in `ℂˣ` and then included in `ℂ`. Thus negative
integer exponents and all actual unramified characters occur in the
comparison. The canonical coordinate theorem is definitionally the same
formula as the descended-character version.

## Remaining application obligations

This unit supplies the actual scalar-algebra comparison needed for the
previous polynomial and common-denominator rational-family predicates.
It does not prove convergence or rationality of an intertwiner, construct
an open twist-orbit domain, descend operator families to representation
orbits, construct the same compact subgroup for two parabolics, or prove
any Plancherel assertion. The original integral and representation-theoretic
obligations remain separate.
