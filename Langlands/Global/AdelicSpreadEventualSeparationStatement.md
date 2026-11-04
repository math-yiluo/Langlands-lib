# Eventual separatedness of supplied arithmetic spreads

`Langlands.Global.AdelicSpreadEventualSeparationStatement` is the conjunction
of the function-field and number-field forms of eventual separatedness for
a supplied finite-type arithmetic model.

In the function-field clause, `k` is an arbitrary perfect field and `F` is
a function field over `k`, with the specified compatible rational-function
action and scalar tower. For any finite set `S` of actual curve places and
any scheme `M` over `Spec (curvePlaceSIntegers k F S)` whose structure map
is locally of finite type and quasi-compact, the statement asserts

* the actual generic fiber of `M` over `F` is separated if and only if
* there is a finite set `T` containing `S` such that the actual pullback
  of `M` to the outside-`T` integer ring is separated over that ring.

The number-field clause asserts the same equivalence for a number field
`K` and its original outside-`S` and outside-`T` integer rings. The finite
sets index finite places; adjoining all archimedean places gives Conrad's
full place-set convention. This assertion concerns arithmetic schemes and
does not remove or alter the infinite factors in any adelic construction.

The generic fibers are precisely `curvePlaceModelGenericFiber` and
`numberFieldModelGenericFiber`. The models at larger sets are precisely
`curvePlaceLevelModelBaseChange` and `numberFieldLevelModelBaseChange`.
All four use categorical pullbacks along the literal inclusions of the
original integer subrings. `IsSeparated` refers to the indicated structure
map, so the conclusion is relative to the relevant integer ring or field.

There is no affine, separated, or quasi-separated premise on `M` beyond
finite type. The actual integer bases are Noetherian, so finite type
implies the quasi-separatedness and finite-presentation conditions used
by the general limit argument. The initial finite set may be empty.
Neither clause asserts that the initial model is already separated.
The assertion supplies a separated base change of a given model; it does
not assert existence of an arithmetic model for every field scheme.

## Source and derived scope

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.5–6, Theorem 3.4(2) with property
“separated,” and Remark 3.5's system of outside-`S` integer rings with
colimit the original field. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Apply that property-descent assertion to the structure map from the
supplied model to its affine arithmetic base. Noetherianity supplies finite
presentation from finite type. For the converse direction, separatedness
is stable under base change from a separated stage to the original field.
This also explains why the separated stage need not be the initial one.

The arbitrary-perfect-constant formulation and the allowance of empty
initial sets are derived scope. The actual integer rings form a filtered
diagram with colimit `F`, including for an empty initial set, and are
Noetherian. The scheme-limit separatedness argument applies to this
diagram without using finite constants, local compactness, or
separability of the finite extension of the rational-function field.
Specializing `k` to a finite field and restricting to Conrad's nonempty
place sets gives his function-field case. The number-field clause uses
the same argument for its actual integer-ring diagram.

This pair states the result. Its proof, the arithmetic colimit proof, and
the generic separatedness-descent proof retain their own independent
review and publication obligations.
