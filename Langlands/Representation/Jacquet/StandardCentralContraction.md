# Central strict contraction for an actual standard parabolic

This internal supporting construction packages the published strict element in
the abstract center of the same actual standard Levi. It then proves the existing
Jacquet contraction predicate for a supplied `StandardParabolicBasisMember`.
It does not prove either VI.9.4 target.

The data are a field `F`, an affine group scheme `G`, a torus map `i`, a
cocharacter `ν`, a standard index `J`, and a compatible split component `q`.
Over a nonarchimedean local field, a maximal-split-torus witness and one standard
cocharacter supply the already constructed `strictElement`. The new definition
`IsCompatibleStandardSplitComponent.centralStrictElement` is this same element,
viewed in `Subgroup.center (standardLeviPoints i ν J)`. Its ambient value is
exactly `strictElement`; it makes no new choice and does not depend on `K`.

The algebraic lemma `map_commute_standardLeviPoints` unpacks the compatibility
witness into a represented Levi inclusion `j`, a split component `a`, and the
equality `a ≫ j = q ≫ i`. The published
`IsSplitComponent.splitComponentLeviPointsMap_mem_center` says that the point map
through `a` and `j` has central values. Applying the ambient coercion to its
commutation identity and using the compatibility equality gives commutation
with every element of `standardLeviPoints`. This lemma needs no valuation or
topology. The lemma `mem_center_of_mem_standardComponentCA` applies that identity
to any element of the image subgroup `standardComponentCA`, with its given Levi
membership.

For an open subgroup `K` in the canonical rational-point topology,
`centralStrictElement_isIwahoriContraction` assumes the pointwise predicate
`StandardParabolicBasisMember i ν J q K.toSubgroup`. It combines its ordered
intersection and contraction/cofinality clauses with the four memberships from
`strictElement_spec`, using the published
`isIwahoriContraction_of_contractionAndCofinality`. The conclusion is exactly
`Jacquet.IsIwahoriContraction` for the ambient value of the central strict
element and the published standard unipotent, Levi, and opposite-unipotent
subgroups. Compactness of `K` is not required for this conclusion. No simultaneous
basis, inherited Levi basis, global root-system comparison, or new structural
premise is assumed.

The provenance is internal and derived from the published modules
`SplitComponentLeviPoints`, `JacquetStrictElement`, and
`JacquetContractionAssembly`. This file supplies a centrality and pointwise
assembly adapter for later use with Jacquet stabilization. It asserts no
stabilization, detection, subquotient generation, or categorical equivalence.
