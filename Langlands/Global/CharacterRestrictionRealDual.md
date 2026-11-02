# Real duals of actual finite-index character restrictions

Author: Worker 112.

For a field `F`, actual group schemes `G`, `H` over `Spec F`, and an actual
homomorphism `i : H ⟶ G`, let `r = characterRestrict i`. Thus `r` is
precomposition on all actual rational algebraic characters. This module and
`AdelicCharacterLog` both use the published `GroupScheme.rationalCharacters`
carrier from `Rational.Characters`. This module constructs an inverse to the induced real-dual map when `r`
is injective and has finite-index range. Both hypotheses are supplied explicitly;
the module does not prove them for a general connected reductive group.

## The character lift

Write `n` for the index of the actual additive subgroup `r.range`. The quotient
of the character group of `H` by this range is abelian, so multiplication by
its cardinal `n` vanishes in the quotient. Accordingly `characterIndexMultiple`
sends a character `ψ` of `H` to `n • ψ` as an element of `r.range`. Injectivity
of `r` identifies its domain with its range. Applying that inverse gives the
additive homomorphism `characterIndexLift`, denoted `q`, satisfying

```
r (q ψ) = n • ψ,     q (r χ) = n • χ.
```

The range and index are those of the actual character restriction. No choice of
basis, freeness, finite generation or splitting of either group scheme is used.
The lift itself is defined even when the index is zero; the inverse construction
below explicitly assumes finite index, which makes `n` nonzero.

## The continuous real-linear inverse

The existing `RealCharacterDual F G` is the entire additive homomorphism space
`Hom_Z(X*(G)_F, ℝ)`, with its pointwise topology. Define

```
realCharacterDualExtend ℓ (ψ) = (n : ℝ)⁻¹ * ℓ (q ψ).
```

This is real-linear in `ℓ`. Each output coordinate is a constant multiple of one
input coordinate, so it is continuous for the existing pointwise topologies.
Finite index makes `(n : ℝ)` nonzero. The two lift identities and additivity of
real functionals then prove both inverse identities with the existing covariant
`realCharacterDualMap F H G i` (precomposition with `r`).

`realCharacterDualRestrictionEquiv` bundles these maps as an actual continuous
real-linear equivalence from the real character dual of `H` to that of `G`.
Its forward function is exactly the existing dual map; its inverse is the
explicit index-normalized extension. The construction also includes trivial
character groups and index one.

## Provenance and boundary

This is an internal algebraic and topological adapter for MW95, I.1.4,
printed pp.5–7, especially the finite-index restriction argument on p.6 and the
logarithmic pairing (4) on p.7. Source ID
`moeglin-waldspurger-1995-spectral-decomposition`, folder SHA-256
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`, chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`. MW applies the finite-index
restriction to a maximal split central torus of a reductive Levi over a global
field. The present extension formula and its coordinatewise continuity proof are
derived elementary implementations, valid for every field and every supplied
injective finite-index actual restriction. They do not use the topology of the
field.

The algebraic assertion that restriction to a split component has these
properties remains a separate theorem. This module neither identifies `H` with
a split component nor asserts reductivity, a torus splitting, adelic-logarithm
surjectivity, the split-centre/norm-one decomposition, a quotient-measure
comparison, reduction or finite volume. It is an intermediate construction for
those subsequent actual-group applications.
