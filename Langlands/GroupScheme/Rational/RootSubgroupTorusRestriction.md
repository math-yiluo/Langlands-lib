# Intrinsic root functors under restriction between split tori

This internal derivation compares the existing all-test relative root functors
when the acting split torus changes. The ambient group is the same throughout.
It is a prerequisite for descent from a larger split torus in the building
construction.

For a homomorphism `f : S → T` of commutative group schemes,
`characterSemigroupPreimage f A` contains exactly the characters `χ` of `T`
such that `f ≫ χ` belongs to the additive subsemigroup `A` of characters of `S`.
It uses the existing additive character pullback and subsemigroup inverse image.
This definition and `subgroup_comp_torusHom_isStable` work over any scheme base.
The stability theorem says that conjugation by every point of `T` preserves the
intrinsic root functor for the composite map `S → T → G`. Its proof uses
commutativity of the points of `T` to show that this action fixes the map from
`S`, then invokes the existing root-functor stability theorem.

Over a field `k` in an arbitrary universe, let `G` be smooth and affine,
let `S` and `T` be split, and let `j : T.toGrp → G`. There is no monomorphism,
maximality, reductivity or connectedness assumption. For every additive
character semigroup `A`, `semigroupWeightSpan_comp_torusHom` proves

```text
weightSpan(conjugation(f ≫ j), A)
  = weightSpan(conjugation(j), characterSemigroupPreimage(f, A)).
```

The proof expands the actual weight spans and applies
`weightSpace_comp_eq_iSup` to each restricted weight space. In one direction,
every larger weight in the fiber belongs to the inverse image semigroup. In
the other, `weightSpace_le_comp` puts each larger weight into its restricted
weight space. Thus the comparison sums the entire fiber of characters.

For every nonzero character `a` of `S`,
`subgroup_comp_torusHom_eq_semigroupSubgroup` proves the equality of
subgroup functors

```text
subgroup(f ≫ j, a)
  = semigroupSubgroup(conjugation(j),
      characterSemigroupPreimage(f, cyclicTail(a, 1))).
```

This is equality on every test scheme, including nonreduced tests. The existing
intrinsic root functor is smooth, connected and closed, and its tangent image
is the positive cyclic weight span. The weight-span comparison rewrites that
image as the full selected larger-torus weight span. The proved larger-torus
stability then permits the existing exact-Lie-image uniqueness theorem for
semigroup subgroups to identify the two actual functors.

The provenance is the imported Library proofs: `Torus.WeightRestriction`,
`Rational.RootSubgroupCentralizerAction`,
`Rational.RootSubgroupLieImage`,
`Rational.CyclicRootFunctorComparisonProof`, and
`Rational.SemigroupRealizationGeometry`. No external assertion is introduced.
This result does not construct an ordered product of larger root subgroups,
valuation laws, initial apartment data, a building metric, or the special
vertex attached to a supplied integral model. Those remain obligations of
the unchanged `BuildingComparisonStatement`.
