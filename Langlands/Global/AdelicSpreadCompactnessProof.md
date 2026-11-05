# Compactness of actual adelic points of proper schemes

`Langlands.Global.adelicSpreadCompactness` proves the unchanged
`Langlands.Global.AdelicSpreadCompactnessStatement` in arbitrary common universe
u, with separate function-field and number-field theorems.

The implemented argument is the structure-map consequence of Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), printed p.11,
Proposition 4.4. For either arithmetic setting, take the identity arithmetic
scheme as a finite-type spread of the terminal field scheme `Spec F`.
Its generic fibre has an isomorphism to that field scheme because the second
projection of the pullback of an identity is an isomorphism. The actual
structure morphism from Y defines a morphism in the over category whose
underlying scheme map is the proper structure morphism supplied by the target.

Apply `curvePlaceSpreadProperMap` or `numberFieldSpreadProperMap` to this
morphism and the supplied initial spread of Y. Actual adelic points of the
terminal field scheme are subsingleton by terminality in the over category.
They are therefore compact for their spread topology. The proper point map
has compact inverse image of the whole target; that inverse image is the whole
source, proving compactness.

The proof retains nonaffine schemes, arbitrary finite-type initial spreads
without arithmetic separatedness, empty initial levels, both global-field
characteristics, finite function-field constants with the specified
rational-function action and compatible scalar tower, potentially inseparable
extensions, and every infinite number-field completion. Its only geometric
assumption beyond the supplied model is properness of Y over the original
field. It does not prove eventual stage stabilization, which is a separate
consequence.

The proof imports the published `AdelicSpreadProperMapProof` by Lean name;
its geometric-to-topological properness result supplies the only substantive
adelic input. The present unit submits only this compactness proof pair.
Worker 208 authored the shared proof and explanation. Worker 1557 checked it
against the published target and prerequisites and prepared it for independent
review. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
