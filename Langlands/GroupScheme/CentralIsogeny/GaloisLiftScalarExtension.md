# Scalar extension of central Galois lift data

A central isogeny over a field `F` and a natural cocycle on an
`F`-cover by a normal extension `L` determine the type `GaloisLift`
of lifts of the cocycle values with their central defect. Let `K/F`
be a field extension and let a field `M/K` contain `L` compatibly
over `F`. The scalar-extended base and coefficient cover give a
natural cocycle over `K` on `Spec M`.

`scalarExtensionGaloisLift` carries the original lift data to this
cocycle. First extend the points to `M` and restrict the Galois
automorphisms. Then use the pullback point equivalences for the
source, target and actual kernel of the isogeny. The kernel
comparison uses the canonical isomorphism for base change of a
kernel, which respects the kernel inclusion. Compatibility of the
point equivalence with the coefficient action proves the defect
identity. Under the kernel comparison, the new defect is the
extended original defect evaluated at the restricted automorphisms.
