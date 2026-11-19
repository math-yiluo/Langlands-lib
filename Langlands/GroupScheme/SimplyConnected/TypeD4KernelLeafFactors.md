# Actual descended leaf factors of the centrally marked D4 kernel

Let `d : TitsIndexData G` be actual index data over a field `k`, let `G`
be simply connected, and let `p : d.AnisotropicKernelIndex`. The published
kernel and field-extension results give simple connectedness of the
anisotropic kernel and its extension to the original separable closure
`SeparableClosure k`.

For a kernel vertex `a`, `componentField` is the intermediate field fixed
by the stabilizer of the geometric almost-simple factor containing `a`.
`descendedComponentFactor` applies the published factor descent and pinning
comparison to that factor. It gives a `ComponentFactor a` over the finite
separable extension whose underlying type is `componentField`.
`descendedComponentInclusion` is the inclusion supplied by that descent
into the original kernel extended to `componentField`. These constructions
apply to every such `p` and `a`.

For the D4 specialization, take a complete numbering by `CartanMatrix.D 4`
with exactly vertex 1 distinguished. The actual Cartan component of each
kernel vertex then consists of that vertex alone. The geometric factor
stabilizer is the Cartan component stabilizer by the published comparison.
Singleton connectivity and the full star-equivariant kernel-to-ambient
vertex equivalence turn this into the star stabilizer of the corresponding
ambient leaf. Taking fixed fields proves `componentField_eq_starVertexField_D4`
as an equality of intermediate fields of the original separable closure.

The actual factor's vertex equivalence with the singleton component gives
a numbering by `Fin 1`. The Cartan comparison gives the diagonal entry 2,
and the star action on a singleton is trivial. This proves that the selected
factor has an inner A1 index. The published comparison preserves anisotropy
of the original kernel. The anisotropic inner type A theorem for simply
connected groups gives a degree-two central division norm-one presentation
of the selected factor over its component field.

The construction is an internal use of published geometric factor descent,
actual index and star comparison, and inner type A normalization. It works
in every field characteristic and uses the original kernel extended to the
component field as the codomain of the inclusion.
