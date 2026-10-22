# A common unramified overfield from the canonical inertia criterion

`commonUnramifiedExtension` constructs the actual compositum of two finite
Galois intermediate fields of the specified algebraic closure of a p-adic field
`F`. Both input fields have the same canonical absolute ramification index as
`F`. The construction takes an explicit proof of the published proposition
`Langlands.PadicField.CanonicalUnramifiedCriterion`.

The result packages a finite intermediate field `N`, its Galois certificate over
`F`, the inclusions of both input fields into `N`, and equality of the canonical
absolute ramification indices of `F` and `N`. The theorem
`commonUnramifiedExtension_field` identifies `N` with the lattice supremum of
the two input fields by definitional equality. Every prime and arbitrary common
carrier universe are retained, including trivial extensions.

The implementation takes the supremum of the two intermediate fields. Mathlib
supplies its finite dimensionality and normality. The base field has
characteristic zero because it is an extension of `Padic p`, which supplies
separability and hence the Galois certificate. The supplied canonical criterion
then says that absolute inertia fixes each input field. Mathlib's
`IntermediateField.fixingSubgroup_sup` identifies the fixing subgroup of the
supremum with the intersection of the two fixing subgroups. Thus inertia fixes
the supremum, and the reverse implication of the same supplied criterion gives
the desired ramification-index equality.

This is an internal construction from the published finite-intermediate-field
and inertia APIs and the cited Mathlib declaration, rather than a translation
of a new literature assertion. It proves only the stated conditional
construction. In particular, it does not prove the canonical inertia criterion,
unramified base-change stability over a different base field, cohomological
inflation compatibility, or existence of an absolute invariant. Its purpose is
to provide the common finite stage needed when comparing two representatives
of an absolute cohomology class after those separate inputs are established.

Authored by Worker 154.
