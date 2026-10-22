# Cochain maps between cocycle extensions

This module constructs maps between the actual normalized cocycle extensions.
For `c` on `G` with coefficients `A`, `d` on `H` with coefficients `B`,
homomorphisms `f : A →* B` and `φ : G →* H`, `MapData` contains a cochain
`b : G → B`, action equivariance, and the equation

`f(c(g,h)) * b(g*h) = b(g) * (φ(g) • b(h)) * d(φ(g),φ(h))`.

Normalization of both cocycles implies `b(1)=1`; the module proves this
without an additional assumption. The actual map is
`(a,g) ↦ (f(a)*b(g),φ(g))`. Its multiplicativity follows by expansion,
equivariance, and the displayed equation. It restricts to `f` on coefficients,
covers `φ` on quotient groups, and maps the distinguished section to the
target section multiplied by the cochain.

Identity data have constant-one cochain. Composition transports the first
cochain through the second coefficient map and multiplies by the second
cochain evaluated on the first group map. The module proves that these give
the identity and composite extension homomorphisms. Injectivity and
surjectivity follow from those of both component homomorphisms, using the
two coordinates; bijective component maps give a multiplicative equivalence.
Continuity follows from continuous component maps, continuous cochain and
continuous multiplication in the target coefficients, using product topology.

For multiplicative equivalences `f` and `φ`, `equivOfEquivs` constructs the
inverse explicitly:
`(a,h) ↦ (f⁻¹(a / b(φ⁻¹(h))), φ⁻¹(h))`. If the component equivalences are
continuous in both directions, the cochain is continuous and `B` is a
topological group, `continuousEquivOfEquivs` is a continuous multiplicative
equivalence. Continuity of the inverse follows from the displayed formula.
In particular, identity component equivalences and a cochain witnessing the
displayed coboundary equation identify the two cocycle extensions, including
their topologies when the cochain is continuous. No discreteness or
finite-dimensionality assumption is needed here. All group and coefficient
universes are independent.

Source: Artin and Tate, *Class Field Theory* (2009), Chapter XIII section 1,
printed p.129 (PDF p.138), registered as
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The displayed equation is their equation (*) multiplied by `b(g*h)` in
the abelian coefficient group. Composition, bijectivity and continuity are
derived directly from these coordinate formulas. These constructions require
actual cochains satisfying the stated equation; they do not assert arithmetic
norm compatibility or select a global fundamental class.
