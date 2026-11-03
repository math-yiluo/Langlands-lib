# Smooth-dual representatives in actual completed automorphic slices

Author: Worker 2.

This internal construction refines the intrinsic smooth Hilbert slices to
actual irreducible admissible objects and their existing smooth-dual classes.
It identifies those classes with the published embedded form-space local
components and transfers subgroup-fixed spaces from the given local factor.

## Inputs and actual representatives

The field `F : Type uF` is an arbitrary number field, rank is any natural
number, and scalars are complex. Original local factor carriers lie in an
independent universe `uV`. The groups and their topologies are the actual
finite-completion matrix groups. No topology is imposed on the original
algebraic factor carriers.

The input `P` remains a genuine tensor presentation of an actual invariant
form space `S`; `b` is a supplied invariant positive form on its action.
The published intrinsic smooth range is the intersection of the completed
invariant slice with the smooth vectors for the original completed global
action restricted along local insertion.

For an explicit nonzero complementary tensor and explicit irreducibility and
admissibility of the specified local factor, `sliceHilbertSmoothObject`
bundles exactly this inherited carrier and action in the existing irreducible
admissible full subcategory. It uses the published smoothness and property
transport laws. Irreducibility is algebraic irreducibility, including
nonzeroness. Admissibility uses the existing all-open-subgroups convention.
The carrier is in `uF`, regardless of `uV`.

`sliceHilbertSmoothDualClass` takes the existing quotient by actual categorical
isomorphisms. It selects no model factor in a different universe.

## Class comparisons

The generic `SmoothDualClass.ofRep_eq_iff_isoClass_eq` proves that two actual
irreducible admissible objects have equal refined classes exactly when their
underlying smooth classes agree. The proof uses the quotient equality
criterion, forgets a categorical isomorphism along the full-subcategory
inclusion in one direction, and lifts it with `ObjectProperty.isoMk` in the
other. Both objects use the same specified carrier universe.

`sliceHilbertSmoothDualClass_eq` applies this criterion to the published
smooth-class comparison. The original tensor family, exceptional set,
reference vectors and reference invariance data remain fixed; the global
realization, presentation, positive form and nonzero tail may vary.

`sliceHilbertSmoothDualClass_eq_localComponent` compares the completed smooth
slice with the existing embedded form-space component of the same
presentation. It additionally retains nonzeroness of `S`, as required by that
component's construction. Its proof composes the smooth-class comparison
with the algebraic slice and the published independence of the component's
chosen complementary tensor. The generic full-subcategory criterion then
gives equality in the actual smooth dual.

## Fixed vectors

`sliceHilbertSmoothFixedEquiv` applies the published `fixedVectorsEquiv` to
the genuine original-factor equivalence. It is a complex linear equivalence
between the specified factor's fixed space and the actual intrinsic smooth
slice's fixed space for any subgroup. Neither openness nor compactness of
that subgroup is required. This construction requires admissibility and the
nonzero tail, but does not require irreducibility.

`sliceHilbertSmoothDualClass_hasFixedVector_iff` uses the published nonzero
fixed-space invariance law and the definition of the quotient predicate.
Outside the exceptional set,
`sliceHilbertSmoothDualClass_hasIntegralFixedVector` applies this criterion
to the actual integral local subgroup. The presentation's nonzero reference
vector is fixed there by the supplied reference invariance.

## Provenance and limits

This is an internal derivation from the published smooth-slice objects and
equivalences, `PresentedLocalCategory`, the actual smooth representation
category, and the existing subgroup-fixed-space APIs. The implemented
quotient and transport arguments are described above. No identification with
an original-literature object or theorem is newly asserted.

All factor properties, the nonzero tail, the genuine presentation and the
global positive form remain explicit. The comparison with the existing form
component retains that component's global nonzeroness hypothesis. These
constructions prove no existence of presentations or positive forms,
factorization of arbitrary automorphic representations, uniqueness across
different tensor data, norm compatibility, embedded-subspace equality,
automorphic occurrence, spectral decomposition, dimension-one result, or
normalized Satake parameter.
