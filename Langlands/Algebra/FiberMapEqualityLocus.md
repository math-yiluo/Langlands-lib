# Equality of actual residue-fibre algebra maps

This internal derived construction applies the actual fibre-zero locus to two
algebra maps. It retains the full residue-field tensor algebras, including their
nilpotents. The source and target algebras may have different universes.

`baseChangeMap S f` is the actual tensor algebra map `S ⊗[R] A → S ⊗[R] B`.
`fiberMapEqualityLocus f g` consists of the primes where these maps become equal
after base change to the residue field. Agreement is equivalent to the vanishing
of `1 ⊗ (f(a)-g(a))` for every source element. A generating set of the source
algebra suffices by the algebra-adjoin universal property. A finite generating
set therefore expresses the equality locus as a finite intersection of the
actual fibre-zero loci. It is constructible when the base is noetherian and
both algebras are of finite type.

This does not construct a noetherian coefficient model or prove global kernel
centrality. It is a supporting input for preserving fibrewise equations in such
models.

`fiberMapEqualityLocus_baseChange` identifies the equality locus after every
ring extension with the full inverse image of the original locus. This requires
no finite type or noetherian assumptions. The proof uses the scalar-extension
universal property twice to reduce equality on iterated tensor algebras to the
original source elements, then applies the arbitrary-base-change comparison for
each fibre-zero equation. Thus equality means equality of full algebra maps,
without replacing the fibres by their reductions or their rational points.
