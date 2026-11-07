# Actual Galois orbit blocks for the canonical Steinberg product

This internal unit constructs actual orbit blocks and a complete simple-root
ordering. It then descends the full image ideal of the canonical Steinberg
product for that order, conditional on orthogonality of the supplied action's
orbits and the explicit torus, character and whole-root-map compatibility data.
The construction removes supplied lists, their invariance proofs and a supplied
ordering from the existing descent interface. It does not prove that a
quasi-split group admits these compatible data or orthogonal orbits.

`Algebra.FiniteActionOrbitBlocks` works for a group `Γ` acting on a finite type
`I`, with independent universes. The acting group need not be finite. For each
element of the actual orbit quotient, `orbitList` lists its finite fibre without
repetition. `blocks` enumerates all those fibres once. Distinct fibres are
disjoint, so `flatten_nodup` proves that the concatenation has no duplicates.
`mem_flatten` shows that every element occurs. `ordering` is the resulting
equivalence from the finite list positions to `I`, and
`flatten_eq_ofFn_ordering` identifies the concatenation with that exact order.
The choices of finite enumerations impose no preferred order on the orbits.

`blocks_invariant` proves that every group element permutes each individual
orbit list. Its proof compares membership in the two lists, using the inverse
group element for the reverse implication. `same_orbit_of_mem_block` extracts an
actual group element carrying either specified entry of a block to the other.
These facts come from the actual action quotient, without assuming an abstract
partition or enumerating the acting group.

For a supplied split pinning `p` and a permutation representation `ρ` on its
simple-root support, `SplitPinning.simpleOrbitBlocks` and
`simpleOrbitOrdering` apply this construction to the action induced by `ρ`.
The support is finite because the pinning's root index is finite. The
Prop-valued predicate `OrthogonalSimpleOrbits` is

```
∀ σ a, a ≠ ρ σ a → p.rootDatum.IsOrthogonal a (ρ σ a).
```

It records orthogonality of distinct simple roots in an action orbit as an
explicit premise. From this premise, `simpleOrbitBlocks_pairwise` proves that
each constructed block is pairwise distinct and orthogonal. Duplicate-free
enumeration gives distinctness; the actual group element connecting two entries
lets the predicate supply their orthogonality. The adjacent lemmas prove exact
flattening, invariance under `ρ`, and same-orbit membership for these lists.

For arbitrary fields `k` and `K` in universe `u`, an algebra structure `k → K`
and an affine group `G` over `k`,
`SteinbergOrbitImageDescent.definingIdealDescent_of_orthogonalSimpleOrbits`
uses a split pinning on the actual base change of `G`. It requires:

- a commutative group `T` over `k`, a homomorphism `j : T.toGrp ⟶ G`, an
  isomorphism from the pinning torus to `T` base changed to `K`, and the actual
  commuting inclusion square;
- normalized simple-root maps and a representation `ρ` of `K ≃ₐ[k] K` on the
  supplied simple-root support;
- the ordinary root-character transport law through that torus isomorphism;
- `RootMapsGaloisCompatible`, expressing coefficient transport of the entire
  generic one-variable normalized root morphisms;
- `OrthogonalSimpleOrbits` for this `ρ`, and `IsGalois k K`.

The construction takes the simple roots themselves as polynomial coordinate
indices and uses `simpleOrbitOrdering` for both index equivalences.
`rootCoordinateAction_self` proves that the transported coordinate action is
exactly `ρ`. The preceding list lemmas therefore discharge all block, ordering
and pairwise orthogonality premises of
`definingIdealDescent_of_compatibleRootMaps`. That existing construction derives
canonical representative transport and factor transport from the compatible
root maps, and factor commutation from distinct orthogonal simple roots.

The result is actual `DefiningIdealDescent` data for the kernel ideal sheaf of
`steinbergProduct (p.simpleOrbitOrdering ρ) x
(canonicalSimpleReflectionRepresentatives x)`. Thus it supplies an ideal sheaf
on the original group whose pullback equals the full image ideal of this
chosen-order product. It asserts neither that the product is an immersion nor
that its image is a cross-section. It makes no assertion for arbitrary other
orders. Finite extension degree, perfectness and infinitude are not required.

The provenance is internal: finite action combinatorics and a specialization of
the existing actual-factor and full image-ideal descent constructions. No new
original-literature theorem is asserted. Compatible pinning and normalized-map
existence, orthogonality for applicable root systems, immersion and quotient
calculations, exceptional even-type-A substitutes, rational lifting and the
parent quotient proposition remain open.
