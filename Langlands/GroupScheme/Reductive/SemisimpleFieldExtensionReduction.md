# Reduction of Milne 4.19 to semisimple algebra scalar extension

This module proves the unchanged full
`SemisimpleRepresentationFieldExtensionStatement` conditional on the internal
generic algebra statement `Langlands.Algebra.SemisimpleScalarExtensionStatement`
in the required universe instance. The generic prerequisite remains explicit;
this module does not assert an unconditional proof of Milne 4.19.

The simple and semisimple descent assertions and the scalar-intertwiner
irreducibility ascent assertion use the preceding proved actual-representation
helpers. For semisimplicity ascent, the original operator module is semisimple,
so its faithful finite-dimensional operator algebra is semisimple.
The target's étale-centre hypothesis transfers from the actual self-intertwiner
algebra to this operator algebra through the proved centre equivalence.
The supplied generic algebra theorem then makes the tensor-extended operator
algebra semisimple. Its image on the extended coordinate space is a semisimple
ring, since a quotient of a semisimple ring is semisimple.

Actual stable subspaces are precisely invariant subspaces for that image.
`extendedSubmodule` supplies the corresponding operator module, and restriction
of scalars preserves complements. Hence every actual subspace has an actual
stable complement, proving semisimplicity of the new operator module and the
target's raw simple-subspace sum formula.

Provenance: internal proof reduction for Milne, *Algebraic Groups* (2017),
Proposition 4.19, pp. 90–91 (`milne-2017-algebraic-groups`). The representation
target is used unchanged and keeps all universes, all affine tests, and both
alternatives of its semisimplicity-ascent hypothesis.
