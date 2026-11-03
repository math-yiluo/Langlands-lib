# Full-domain comparison with actual ordinary-open pullback

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `A` an actual presented
positive-polyradius affinoid algebra, and `d : Domain K A` a full represented
affinoid domain. This module identifies `toIntrinsicSections d U` with the
previously constructed bounded-map pullback `OpenSections.pullback d.baseMap U`
for every ordinary open `U` of the ambient spectrum. No containment of `U` in
`d.locus` is needed for this equality. If `U ⊆ d.locus`, the actual pullback is
an algebra equivalence with the previously constructed intrinsic-to-ambient
inverse.

## The actual transport arrow

For an ambient rational chart `q`, an intrinsic rational chart `w`, and an
actual arrow

```text
g : w ⟶ RationalChart.pullback d.baseMap q,
```

`rationalTransportInclusion d q g` is an ambient full-domain arrow

```text
d.extend w.toDomain ⟶ q.toDomain.
```

Its bounded restriction is exactly
`g.restriction.comp (RationalChart.pullbackMap d.baseMap q)`.
Its structural equation follows from `pullbackMap_comp_baseMap`, associativity
of bounded composition, and `g.comp_baseMap`. Thus the arrow retains the
actual quotient transport rather than merely a containment of loci.

`sectionEvaluation_extend_transport` applies when `q` is contained in an
ambient subset `S` and `w` is contained in its full spectral preimage. It says
that evaluating an ambient family `s` on `d.extend w.toDomain` equals

```text
g.restriction (RationalChart.pullbackMap d.baseMap q (s.val q)).
```

The proof uses `sectionEvaluation_naturality` on the constructed ambient
arrow, followed by `sectionEvaluation_rational` for the source component.
This local result applies to arbitrary subsets; its arrow hypothesis is
explicit.

## Equality with ordinary-open pullback

`toIntrinsicSections_eq_pullback` is an equality of `K`-algebra homomorphisms.
At each target rational chart `e` in the preimage of `U`, use the existing
`OpenSections.pullbackRefinement d.baseMap U e`. Its `toFiniteCover` is a
finite full-domain cover of `e.toDomain`, with the same original bounded
restriction maps. `FiniteCover.algebra_ext_of_restrict_eq` reduces equality
of the actual elements of `e.algebra` to these restrictions.

On each refinement component, evaluation naturality along the extended
refinement arrow identifies the restriction of `toIntrinsicSections` with
evaluation on that extended component. The transport lemma identifies this
with the bounded transport of its labelled ambient chart element.
`OpenSections.pullbackElement_local` gives exactly the same expression for
the restriction of the existing ordinary-open pullback. Finite separation,
compatible-family extensionality, and algebra-homomorphism extensionality
finish the equality. This proves equality of quotient elements, including
nilpotents.

`sectionEvaluation_pullback` then identifies evaluation of the actual
pullback on every full intrinsic domain `V` contained in the preimage of `U`
with ambient evaluation on `d.extend V`, in their unchanged stored algebra.
It follows by the map equality and
`sectionEvaluation_toIntrinsicSections`.

## Actual pullback equivalences

For an ordinary open `U` with `hU : U ⊆ d.locus`,
`fromIntrinsicSections_pullback` and `pullback_fromIntrinsicSections` are
the two inverse identities for the actual ordinary-open pullback and
`fromIntrinsicSections d hU`. They follow by substituting the proved map
equality into the two subset-level inverse identities.

`openSectionsEquiv d U hU` is the algebra equivalence

```text
OpenSections.Sections U ≃ₐ[K]
  OpenSections.Sections (d.spectrumMap ⁻¹' U).
```

It is implemented by `subsetSectionsEquiv d hU`.
`openSectionsEquiv_toAlgHom` identifies its forward algebra homomorphism
with `OpenSections.pullback d.baseMap U`; `openSectionsEquiv_apply` gives
the elementwise version. `openSectionsEquiv_symm_apply` exposes the inverse
as `fromIntrinsicSections d hU`.

`openSectionsEquiv_restriction` proves naturality for every inclusion of
ambient ordinary opens contained in `d.locus`. Its underlying maps are
the subset comparisons, so the result is the already proved subset
restriction identity. The inverse restriction identity remains available
as `fromIntrinsicSections_restriction`.

## Provenance and scope

This is an internal derivation from `DomainSubsetSections`,
`RationalOpenPullback`, and `RationalChartBaseChange`, using the actual finite
full-domain separation imported by the subset comparison. The module
constructs the transport arrow, proves a local evaluation identity, compares
two constructed maps by finite separation, and substitutes this equality
into existing inverse and restriction laws. No new original-literature
assertion, assumed analytic output or private peer draft is used.

The result permits arbitrary positive radii, trivial valuations, nonreduced
or zero algebras and empty spectra or opens. The containing full domain need
not have open locus. On a closed domain this result compares sections on
ambient opens that are contained in the domain; it asserts no ordinary
inverse-image sheaf equivalence on that closed domain. Bundled sheaf and
locally ringed-space restriction comparisons for open domains,
unrestricted analytic atlases, analytic etale and quasi-etale sites,
equivariant sites, and the Harris tower remain separate constructions.
