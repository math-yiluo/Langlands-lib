# Nilpotent surjections after tensor base change

This internal module supplies the nilpotent-surjection part of the affine ring
squares used in infinitesimal line-bundle patching. Let `k` and `S` be arbitrary
commutative rings with a `k`-algebra structure on `S`. A surjective `k`-algebra map
`b : B →ₐ[k] C` induces a surjective map `S ⊗[k] B → S ⊗[k] C`
(`tensor_surjective`). If the kernel of `b` is nilpotent as an ideal, the induced
map also has nilpotent kernel (`tensor_ker_isNilpotent`). These two conclusions
require no flatness hypothesis.

Mathlib's `Algebra.TensorProduct.map_surjective` proves surjectivity. Its
`Algebra.TensorProduct.lTensor_ker` identifies the tensor map's kernel with the
extension of the original kernel along the actual inclusion of the right tensor
factor. Extension of ideals is the ring homomorphism `Ideal.mapHom`; mapping a
nilpotent ideal through this homomorphism preserves nilpotence. This proves the
second conclusion with the actual induced algebra map.

For a categorical pullback square `R → A`, `R → B`, `A → C`, `B → C`, and a flat
`k`-algebra `S`, `tensor_fst_surjective` and
`tensor_fst_ker_isNilpotent` give the same conclusions for the first projection
`S ⊗[k] R → S ⊗[k] A`. The proof reuses the published
`InfinitesimalFlatBaseChange.isPullback_tensor`, then applies the existing
surjective-projection and nilpotent-kernel lemmas for actual ring pullbacks.
In particular this applies to every algebra over any field, in every universe.

`spec_surjective` proves that the actual spectrum arrow of any surjection with
nilpotent kernel is surjective on points: the range is the zero locus of the
kernel, and every prime contains each kernel element because a fixed power of
that ideal is zero. Together with Mathlib's closed-embedding theorem for a
surjection, this constructs `specHomeomorph`. Its forward map is exactly the
actual `Spec.map` arrow, as recorded by `specHomeomorph_apply`. Applying this
construction gives `tensorSpecHomeomorph` for the tensor of the original
surjection, and `tensorFstSpecHomeomorph` for the tensor pullback's first
projection. These are homeomorphisms of underlying spaces, with no claim of an
isomorphism of schemes.

The module is derived from Mathlib's right exactness, spectrum topology and ideal-map laws and the
published internal ring-pullback constructions; it asserts no geometric gluing
or equivalence of Picard groupoids.
