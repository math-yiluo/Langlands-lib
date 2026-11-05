# Separated models over the actual arithmetic integer rings

`Langlands.Global.adelicSpreadSeparatedExistence` proves the unchanged
`Langlands.Global.AdelicSpreadSeparatedExistenceStatement` in both
arithmetic branches.

First plain arithmetic spread existence gives a finite superlevel `T`,
a finite-type model `M` over its actual integer ring, and an isomorphism
over the original field between its actual generic fiber and the given
field scheme `Y`. The compatibility of this isomorphism with the field
structure maps expresses the generic-fiber structure map as an
isomorphism followed by the separated structure map of `Y`.
Separatedness is preserved by that composition.

The eventual-separatedness theorem now supplies a finite superlevel
`U` of `T` such that the actual base change `N` of `M` to the outside-`U`
integer ring is separated. Local finite type and quasi-compactness
persist under this base change, so `N` is finite type. Containment of
the original initial set follows by transitivity.

The proof constructs an isomorphism over the original field from the
actual generic fiber of `N` to that of `M`. The published
`PointTopology.modelPullbackCompIso` identifies the iterated pullback with
the pullback along the composite spectrum map. The composite of the
two literal integer-ring inclusions is the original inclusion into
the field, giving equality of these spectrum maps. Transport along
that equality finishes the comparison in the over-category.
Composing with the original generic-fiber isomorphism gives exactly
the isomorphism to `Y` required by the target.

The function-field and number-field clauses repeat this construction
with their respective actual integer rings. They retain arbitrary
nonaffine schemes, perfect function-field constants without a
finiteness assumption, possibly inseparable specified rational-function
extensions, and possibly empty initial place sets. No initial model or
additional geometric premise is assumed.

The source consequence is Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.5–6, combining Theorem
3.4(1) with the separatedness case of (2), as detailed in the paired
target statement. The proof imports the separate plain-existence and
eventual-separatedness proofs, both already published.
It makes no adelic topology assertion.
