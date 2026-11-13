# Maximal facets meeting the actual Galois fixed set

For the actual coefficient action on supplied integer-valued building data,
every Gamma-facet has a maximal Gamma-facet incident above it. Here
`GaloisFacet` retains the original full upstairs facet and requires that it
meet the actual coefficient-fixed subset. `IsMaximalGaloisFacet E` means
that every Gamma-facet incident above `E` equals `E`. The auxiliary
reflexivity, transitivity and antisymmetry lemmas restrict the original
upstairs incidence relation to this subtype.

The fields `K/k` lie in arbitrary universe `u`, with no characteristic
restriction. The parameters are those of `GaloisFixedFacetIncidence`:
a commutative `k`-group, an affine `k`-group, a base-changed monomorphic
inclusion, an integer-valued valuation on `K`, and a supplied Galois-stable
KP apartment. Connected reductivity, maximal splitness, centralizer data
and full V6 compatibility are supplied. Their existence is not proved here.

`GaloisMaximalFacetsStatement` has two clauses. First, every Gamma-facet
has an incident maximal Gamma-facet above it. Second, each actual fixed
point belongs to the combinatorial fixed closure of such a maximal
Gamma-facet, and there is a translated apartment containing both its
entire upstairs facet and its entire fixed closure. The theorem
`galoisMaximalFacets` proves both clauses. In particular, that apartment
contains the prescribed fixed point.

This is an internal deduction from `GaloisFixedFacetIncidence` and
`IntegerBuildingMaximalFacets`. Apply `exists_maximal_facet_in_subset`
to the subset of original full facets that meet the actual fixed locus.
A member of this subset is exactly the underlying object of a Gamma-facet.
Bundle the resulting upper facet with its nonempty-intersection proof;
subtype extensionality transfers the supplied maximality assertion to
Gamma-facets. The count-minimization argument is entirely in the imported
integer-valued theorem, so no finiteness or chain-completeness premise
is added here.

For a fixed point `y`, apply this extension to `galoisFacetAt y hy`, the
unique original full facet through `y` bundled with the fixedness witness.
Its incidence below the maximal upper facet places `y` in that upper
facet's combinatorial fixed closure by definition. Finally, present the
upper full facet in one of its translated apartments. The imported
`galoisFacetClosure_subset_apartment` places its entire fixed closure,
and hence `y`, in that same translated apartment.

The closures used here are combinatorial unions of incident lower fixed
parts. Maximality is among Gamma-facets, so it does not imply that the
upstairs facet is an ordinary chamber. The point is asserted to belong to
the closure; it need not lie in the maximal facet's open fixed part.
The apartment is not asserted to be Galois-stable or special, and no
descended model, residue-parabolic correspondence, torus lift or
prescribed-point split torus is constructed. The host task's
`UnramifiedFixedPointSplitTorusStatement` remains open.
