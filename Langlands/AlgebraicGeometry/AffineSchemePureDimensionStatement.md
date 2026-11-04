# Pure dimension and base change for affine finite-type morphisms

These derived comparison statements support the last fibre property in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5–6, Theorem 3.4(2). The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
They concern ordinary scheme base change, as an internal prerequisite
for the source's filtered descent assertion.

`FiniteTypeAffineSchemeFieldExtensionPureDimensionInvariance` states
that every field extension K/k preserves and reflects pure dimension
of an affine scheme X locally of finite type over Spec k. The scheme
map is arbitrary; the scalar extension is its actual pullback along
Spec K → Spec k induced by the given algebra structure. Pure dimension
means that each irreducible component, with its subspace topology, has
topological Krull dimension d.

`AffineFiniteTypeFiberPureDimensionBaseChange` considers an arbitrary
cartesian square P → X, P → Y, X → Z, Y → Z, with f : X → Z affine
and locally of finite type. For every actual point y of Y, it equates
pure dimension d of the fibre of P → Y at y with pure dimension d of
the fibre of f at g(y). P, X, Y and Z need not themselves be affine
or separated. The affine hypothesis is on the morphism f and makes
each of its residue-field fibres affine.

`AffineFiniteTypePureDimensionFibersBaseChange` states two consequences:
arbitrary base change preserves the condition that every actual fibre
has pure dimension d; when g : Y → Z is surjective on points it also
reflects this condition. No flatness, finiteness or surjectivity
hypothesis is imposed on g in the preservation direction.

`AffineSchemePureDimensionComparisons` groups these three propositions.
All schemes, rings and fields lie in the common universe of the actual
Scheme category. The field extension may be infinite, transcendental
or inseparable. Empty schemes and empty fibres are included: the
componentwise dimension condition on them is vacuous.

The derived proof route first uses the actual affine global-section
tensor comparison and the finite-type algebra theorem for arbitrary
field extensions. For a cartesian square, the actual fibre comparison
then reduces to extension of the actual residue field κ(g(y)) to κ(y).
Surjectivity covers every point for reflection.

These are statement targets only. They do not assert invariance for
nonaffine morphisms, nonemptiness or geometric connectedness of fibres,
constructibility, or filtered descent over arbitrary original rings.
Those remain obligations of the parent whole-paper task.
