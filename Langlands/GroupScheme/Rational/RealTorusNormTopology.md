# Continuity and identity-component image of the torus norm

This module supplies the topological step for the connectedness proof of
real points. Its provenance is the Library's algebraic Galois norm, affine
Weil restriction point comparison, and split torus point coordinates.

`GaloisNorm.rationalNormContinuousHom` equips the existing rational norm of
an affine commutative group scheme locally of finite type with continuity.
The extension is finite Galois. The fields have topological ring structures
and the extension field carries its module topology over the base field.
Both rational point spaces carry their evaluation topologies. The proof
identifies extension points continuously with base points of the affine
Weil restriction, applies the continuous map induced by the algebraic norm,
and identifies the result with the existing rational norm.

`GaloisNorm.connectedSpace_complexPoints` uses an isomorphism from the
complexified group to a split torus. On complex points this gives a
homeomorphism with a finite product of copies of the complex unit group.
The latter group is path connected by Mathlib.
`GaloisNorm.rationalNorm_mem_connectedComponent_one` sends the connected
complex point space into the real point space along the continuous norm.
The image contains the real identity because the norm preserves the
identity. Every norm value therefore lies in its real connected component.
