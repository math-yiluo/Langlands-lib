# Field-level adelic pullbacks from independent spreads

The three proposition definitions in the paired Lean file state the actual
adelic pullback comparison for a limiting cone of field schemes over a separated
field scheme `Z`. The function-field and full-number-field clauses are conjoined
in `Langlands.Global.AdelicSpreadPullbackStatement`.

The two factors `X`, `Y` and the cone vertex each have a specified finite-type
arithmetic spread over independently specified finite place sets `S`, `T`, `U`,
and arbitrary specified generic-fiber isomorphisms. Finite type is expressed by
`LocallyOfFiniteType` and `QuasiCompact` on each model structure map. The two
arrows are arbitrary morphisms over the field; they need not come from maps of
the specified models. No model or finite-type premise is imposed on `Z`;
its structure map to the field spectrum must be separated. Neither factor nor
the cone vertex is required to be affine or separated.

Points are the existing actual morphisms from the full-adele spectrum over the
field, not an auxiliary restricted-product set. The comparison is precisely
`affineSchemePullbackPointComparison`: postcompose with the two cone legs and
record their equality after mapping to `Z`. Despite this declaration's historical
name, its definition and the corresponding point equivalence use the universal
property in all schemes over the field and impose no affineness assumptions.
The source has the specified vertex spread topology. The target is the
compatible-pair subtype of the ordinary product of the two specified factor
spread topologies.

Both clauses have arbitrary common universe `u`. The function-field clause
retains arbitrary perfect constants, the specified rational-function-field
action and scalar tower, and potentially inseparable finite extensions. Initial
finite sets may be empty. The number-field clause uses full adeles, retaining
every infinite factor. No local compactness or finite-residue-field premise is
added.

## Provenance and scope

This is a derived statement based on Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, December 31, 2011, printed pp.8–9, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Page 8 states finite-level compatibility with fiber products and closed
immersions. Page 9 constructs the full-adele final topology and discusses
fiber products in its separated-scheme discussion.

The stated scope follows from independent-spread binary products and the
closed-immersion comparison. In the field product of `X` and `Y`, the pullback
is the equalizer of the two composites to `Z`. Separatedness of `Z` makes its
inclusion a closed immersion. A finite-type arithmetic model of the field
product is obtained by enlarging the factor spreads to their union and taking
their actual model product. The closed-immersion comparison embeds the vertex
point space in that product point space. The algebraic universal property then
identifies the image with exactly the compatible pairs, giving the asserted
homeomorphism. This rationale explains the additional nonseparated-factor and
perfect-constant scope; it is not a claim that Conrad explicitly states this
generality.

The separated-base hypothesis is retained throughout. The statement does not
adopt an unrestricted nonseparated-base interpretation of the phrase “for
general X” on p.9. This pair supplies proposition targets; their proofs require
separate proof contributions.
