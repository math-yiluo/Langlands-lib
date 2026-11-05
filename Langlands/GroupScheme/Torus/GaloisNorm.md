# The algebraic norm of an affine commutative group scheme

Worker 1435. This is derived internal infrastructure. It combines the existing
actual affine Weil restriction, actual scheme-pullback comparison, tensor Galois
point norm, and affine corepresentation. No external theorem is assumed.

Let `k,L : Type u` be fields in an arbitrary common universe, with `Algebra k L`,
`FiniteDimensional k L` and `IsGalois k L`. Let `T` be a commutative group scheme
over `Spec k` with affine underlying scheme, and put
`T_L := GaloisPointComparison.baseChanged k L T.toGrp`.

`pointNorm` is the composite of `Lie.affineBaseChangeEquiv` on the actual
`T_L(L tensor_k A)` points and `TensorGaloisPoint.norm` into `T(A)`.
`pointNorm_naturality` follows from the naturality of these two maps, for every
commutative `k`-algebra map. `normNat` transports this natural group homomorphism
to the existing affine-coordinate functor using `CocharacterDatum.toFunctor`.

Assume additionally that the underlying scheme of `T_L` is affine and its
structure morphism is locally of finite type, as required by the existing
`AffineWeil.groupScheme`. `norm` reconstructs an actual group-scheme morphism
`AffineWeil.groupScheme k L T_L ⟶ T.toGrp` through
`Corepresented.groupSchemeMap`, then the existing target comparison isomorphism.
`norm_affinePoints` proves that on every commutative `k`-algebra `A`, its action
is exactly `AffineWeil.pointsEquiv`, followed by the actual base-change
comparison and the tensor Galois norm. Its proof uses the affine-point formula
for the reconstructed morphism and the injective target coordinate comparison.

The construction assumes no characteristic, torus, splitness, topology or
smoothness condition. Smoothness and comparison with the existing rational norm
are separate assertions.
