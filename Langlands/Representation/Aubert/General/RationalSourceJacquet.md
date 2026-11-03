# Actual source Jacquet maps from the literal rational Levi family

This internal adapter uses the unchanged simple-root labels of the actual point
Coxeter system. The generic `intersectionLeviIndex` reads `intersectionSubset`
as a finite subset of the subtype `J`. Its `leviIndex` is exactly the original
intersection subset: no label is discarded, because the defining subset is
contained in `J`. This construction needs neither finiteness of the whole
label type nor minimality of the Weyl representative.

`pointSourceDecomposition` works over any field in universe `u`, for an affine
ambient group scheme, the displayed connected-reductive group and maximal
split torus, and a generic cocharacter. The standard Levi intersection
statement, point normalizer/full-centralizer comparisons, a scheme relative
Weyl Coxeter system and both all-test twisted-intersection properties remain
explicit inputs. For every minimum point Weyl representative and every actual
normalizer lift, the theorem combines the literal restricted-standard
semidirect decomposition at `intersectionLeviIndex` with the three exact
point-source identities. It derives the actual source decomposition; that
decomposition is not an additional premise.

For the remaining constructions the field is topological, with the canonical
`pointTopology` on rational points. The rational-point group is locally compact
and nonarchimedean; all standard Levis and radicals are closed. No Hausdorff
or local-field premise is needed for this adapter. Inside the selected Levi
`L_J`, the displayed restricted standard radicals are limits of compact
subgroups and the literal normalized Jacquet functors preserve finite length,
at the carrier universe `max (u + 1) v` used by the rational target.

`pointSourceJacquetPreservation` derives finite-length and short-exact
preservation for the actual source Jacquet functor. Its proof applies
`geometricSourceJacquetPreservationOfEq` at the literal `leviIndex` label.
Restricted standard Jacquet exactness follows from
`jacquetFunctor_preservesShortExact` and the compact-subgroup-limit premise.
The ambient standard Levi inclusion is derived from the source Levi identity
itself. Thus no separate source preservation, structural inclusion or
induction-preservation premise is introduced.

`pointSourceJacquetK0` constructs the map of the actual source Jacquet functor
on the full exact finite-length Grothendieck groups using the derived
preservation witnesses. Its codomain is the actual source intersection Levi.
All points, finite root labels and inverse-conjugation conventions are those
of the original definitions.

The provenance is internal and consists of the named published definitions,
the source comparison and point-intersection transport, and the exactness
theorem named above. The two twisted structural properties and the final
rational-point Aubert induction-compatibility proposition remain unproved by
this unit. Its Jacquet and compact-limit premises are already present for the
literal restricted families in the final target; no premise is added to that
target.
