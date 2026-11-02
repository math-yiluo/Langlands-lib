# Relative flatness of actual module sheaves

This internal supporting construction supplies the flatness condition in Stacks
Project, Section 99.5, Situation 99.5.1 (Tag 08KA), specialized to schemes.
The retained original is `08KA.html` in the registered source
`stacks-coherent-sheaf-stack-08ka-2026-11-01`.

For an arbitrary morphism of schemes \(f:X\to Y\) and an actual
\(\mathcal O_X\)-module \(M\), `IsFlatOver f M` requires every stalk \(M_x\)
to be a flat module over \(\mathcal O_{Y,f(x)}\). Its module action is
restriction of the canonical \(\mathcal O_{X,x}\)-action along the actual
scheme stalk map \(f^\#_x\). This definition imposes no quasi-coherence,
finiteness, noetherian, or quasi-compactness condition.

`stalk` reuses the underlying abelian-group stalk, and `stalkModule` reuses
Mathlib's filtered-colimit module action. `stalkMap` is the actual induced
map on stalks, with linearity proved by representing a scalar and a module
element by germs on one common open neighborhood and applying sectionwise
linearity. `stalkIso` and `relativeStalkIso` retain the actual maps of stalks
induced by a module isomorphism. Flatness transports across this linear
equivalence, proving `isFlatOver_iff_of_iso` and closure of the object
property `isFlatOver f` under isomorphisms.

This focused unit provides the intrinsic flatness predicate and its
isomorphism invariance. Pullback preservation and the coherent-family
groupoid are subsequent units of the same task; no algebraicity result is
asserted here.
