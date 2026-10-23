# Away finite-adelic scalars on actual roots-of-unity twists

This internal construction gives the existing rational away roots-of-unity
limit its away finite-adelic action, conditional on the published normalized
scalar comparisons. It proves compatibility with full scalars, full-to-away
restriction, ring maps, ring automorphisms and the existing field-Galois action.
The namespace is `Langlands.TateTwist.Divisibility`.

## Inputs and provenance

Let `R` be a commutative ring and `m` an arbitrary natural number. The existing
`Away R m` is the coherent limit of actual roots of unity at positive orders
coprime to `m`, and `RationalAway R m` is `ℚ ⊗[ℤ] Away R m`.
No primality or nonzero hypothesis on `m` is required.

The inputs remain explicit:

- `h : Global.RationalProfiniteIntegerAdeleComparison`;
- `hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m`.

These are the published proposition-valued comparison statements. This file
does not prove either statement. It reuses their chosen equivalences from
`Tate.RationalScalars` and `Tate.AwayRationalScalars`. In particular, the away
integral and rational witnesses are coupled to each other, and their restriction
square uses the full witness selected by the same `h`.

The construction is an internal consequence of the published actual residue
actions and functorial root maps in `TwistRationalScalars`, together with the
comparison-square lemmas in `AwayRationalScalars`. It introduces no new
literature assertion and requires no additional source.

## Action and normalization

`primeToFiniteAdeleAction R hAway` is the composite algebra homomorphism

```text
PrimeToFiniteAdeles m
  -- inverse of the assumed rational comparison -->
ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m
  -- rationalAwayScalarAction -->
End_ℚ (RationalAway R m).
```

`primeToFiniteAdeleModule` is its module structure, supplied as a definition
for local installation. `primeToFiniteAdeleModule_smul` identifies this scalar
multiplication with the displayed action. The diagonal rational action agrees
with the existing rational-vector-space action, by the algebra-homomorphism
law. This also supplies the `ℚ` scalar-tower law.

`primeToFiniteAdeleAction_integral_tmul` proves the normalization formula:
for `a : PrimeToProfiniteIntegerRing m`, `q : ℚ` and `x : Away R m`,
the image of `a` under the coupled integral comparison acts on `q ⊗ x`
as `q ⊗ (a • x)`. The proof uses the rational comparison formula for `1 ⊗ a`,
then the pure-tensor formula of the existing residue action.

## Full and away compatibility

`finiteAdeleAction_eq_away` states that the previously constructed full
finite-adelic action on the away twist factors through
`Global.primeToFiniteRestriction m`. `rationalRestrictAway_finiteAdeleAction`
states that the existing map from the full rational root limit to the away
one intertwines the full action with the away action after that same scalar
restriction.

Both proofs unfold transport along the comparisons, use the existing
compatibility of full and away rationalized residue actions, and apply
`PrimeToRationalProfiniteIntegerAdeleComparison.rationalEquiv_symm_restrict`.
They therefore use the single coupled pair of witnesses, rather than
unrelated scalar identifications.

## Naturality and automorphisms

For any ring homomorphism `f : R →+* S`,
`rationalMap_primeToFiniteAdeleAction` proves scalar compatibility of the
existing root-induced rational map. `primeToFiniteAdeleMap` bundles that
same function as an away finite-adelic linear map, using `hAway` on both
rings. Its apply formula is definitional. Its identity and composition
laws follow pointwise from the existing rational-map laws; for `g : S →+* T`,
the map of `g.comp f` is the map of `g` composed with the map of `f`.

`rationalAutomorphismAction_primeToFiniteAdeleAction` says that every ring
automorphism commutes with this away scalar action. For fields `K` and `L`
with an algebra structure, `rationalGaloisAction_primeToFiniteAdeleAction`
specializes this to the existing action of `Gal(L/K)`. These proofs reuse
the corresponding rationalized away residue compatibility, evaluated at
the inverse comparison image of the adelic scalar. No Galois-extension
hypothesis is needed for this automorphism-action assertion.

## Scope

This unit is algebraic. It does not construct a rational topology, assert
continuity, prove the scalar-comparison hypotheses, identify the twist with
a free rank-one module, choose primitive roots or a trivialization, or
construct geometric monodromy or a Weil pairing. It supplies the away scalar
interface for the actual root limits; it does not complete the parent
abelian-scheme and PEL level-structure task.
