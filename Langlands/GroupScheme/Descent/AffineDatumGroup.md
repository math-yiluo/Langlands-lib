# Group structure and effectivity for an affine Čech datum

This is an internal construction in arbitrary universe `u`. Let `B` and `S`
be schemes, `p : S ⟶ B`, `G` an actual group scheme over `S`, and
`D : Descent.Datum p G` an actual Čech datum. Its inputs are the overlap
isomorphism and its cocycle; effectivity is constructed below.

The first part starts with `s : AffineSchemeSolution D`, the supplied underlying
affine scheme solution from `AffineDatumScheme`. It contains an affine object
`s.obj : Over B`, a quotient map `s.proj`, a pullback square, and invariance of
the quotient map under the original relation. Assume that `p` is flat,
surjective and quasi-compact. No field, smoothness, reducedness, finite type,
or commutativity hypothesis is imposed. Test objects range over all schemes
in the fixed universe, including nonreduced schemes.

## From compatible sections to a group object

`AffineSchemeSolution.sectionEquiv U`, imported from `AffineDatumSections`,
identifies the actual maps `U ⟶ s.obj` with the subgroup of local sections on
`p*U` respecting `D` on every test scheme. `sectionGroup U` transfers the
subgroup's group structure across this equivalence. The private
`localSection_one` and `localSection_mul` proofs identify the transferred
operations with the actual operations on local sections.

`localSection_comp` proves that restriction commutes with precomposition.
Its proof uses the functoriality of slice pullback. Restriction is injective
by the imported fpqc section descent theorem, so precomposition preserves
unit and multiplication: these equations can be checked after restriction,
where they are the usual group-object section equations.

`sectionPresheaf` packages these groups and precomposition homomorphisms as
`(Over B)ᵒᵖ ⥤ GrpCat`. Identity and composition are the categorical identities
on actual maps. Its underlying set-valued presheaf is represented by `s.obj`:
`sectionRepresentableBy` uses the identity equivalence on each hom set.
Mathlib's `GrpObj.ofRepresentableBy` therefore constructs `groupObj` on
`s.obj`. This reconstructs unit, multiplication and inverse as actual
morphisms and proves their group identities. `groupScheme` bundles this
structure over `B`.

## Actual pullback comparison and compatibility

Mathlib's `yonedaGrpObjIsoOfRepresentableBy` identifies the section groups of
the reconstructed group object with the transferred groups. Applying its
unit and multiplication equations proves that `s.localSection` preserves
these operations for the reconstructed structure as well.

`iso_isMonHom` proves that the original underlying slice isomorphism
`s.iso : p*s.obj ≅ G.X` preserves group laws. The unit and multiplication of
a monoidal pullback are its monoidal comparison followed by pullback of the
original operation. For the unit, restriction of the reconstructed unit is
the local unit. For multiplication, restriction of the two product
projections and the monoidal comparison give the two local product
projections; their product is multiplication on `G`. These establish
`IsMonHom s.iso.hom`. Inverse preservation then follows from the group
structure. `groupIso` is the resulting actual isomorphism of group schemes,
with underlying maps exactly `s.iso.hom` and `s.iso.inv`.

`compatible_of_proj` shows that any group homomorphism from
`p*s.groupScheme` to `G` preserving the quotient projection respects the
canonical datum and `D`. The proof compares the two maps into the second
pullback of `G`. Their base projections agree because both are slice
morphisms. After projection to `G`, the given pullback square reduces equality
to equality over `S` and equality after `s.proj`. The latter follows from
`s.relation`, preservation of the quotient projection, and the defining
projection equation for the canonical overlap isomorphism. This proves
actual scheme-morphism equality, not only equality on field-valued points.

`groupIso_compatible` applies this criterion using `s.iso_hom_proj`.
`AffineSchemeSolution.solution` consequently supplies all three fields of
`Descent.Solution D`: the group scheme, its actual pullback isomorphism with
`G`, and compatibility of that isomorphism with the original datum.

## Constructed affine effectivity

`Datum.affineSolution` composes the reconstruction above with
`Datum.affineSchemeSolution`, which constructs the underlying affine solution
by faithfully flat affine ring descent. Its complete hypotheses are
`IsAffine B`, `IsAffine S`, `IsAffine G.X.left`, `Flat p` and `Surjective p`.
Quasi-compactness of `p` follows from these affine scheme hypotheses. The
result is a `Solution D`, and `Datum.affineSolution_isAffine` certifies that
its descended group scheme has affine underlying scheme.

Thus the input to `Datum.affineSolution` does not contain a descended object,
a solution, or a representability or group-effectivity premise. The
intermediate supplied-solution construction is explicitly composed with the
implemented underlying quotient construction. The result permits
noncommutative affine group schemes in arbitrary characteristic, and also
applies beyond field bases under the stated affine hypotheses.

## Provenance and scope

This adapter is derived internally from the imported actual datum, quotient,
and section constructions, together with Mathlib's group transfer and
represented group-object APIs. The group laws, comparison laws, and datum
compatibility are implemented in this file; there is no new external
literature assertion or unproved effectivity premise.

The module does not assert semisimplicity, simple connectedness, or a central
isogeny, and it does not construct the descent datum of a universal cover.
Those remain obligations of the cover-existence task. Compatible homomorphism
descent is supplied separately by `Descent.FpqcHomDescent`, and an exact-target
proof of the finite-Galois effectivity statement remains a separate successor
once that statement has been published.
