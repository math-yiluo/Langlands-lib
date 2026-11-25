# Actual quotient comparison from affine generator kernels

This internal module converts explicit actual generator-kernel information
into the existing actual affine-point Grassmannian quotient comparison.
It does not prove any geometric kernel identity.

`quotientByKernelEquiv K T hT hK` is the actual linear equivalence from the
quotient by a supplied submodule `K` to the target of a surjective linear
map `T`, given an equality `T.ker = K`. It first identifies the supplied
quotient with the actual kernel quotient and then applies the first
isomorphism theorem. `quotientByKernelEquiv_mkQ` computes the equivalence
on every quotient image: it sends `K.mkQ x` to the original value `T x`.
Thus the comparison retains the original generator map.

For the existing quotient Grassmannian representation `D`, scheme map
`f : X ⟶ D.Gr`, actual module sheaf `N` and prescribed global family `q`,
`hasAffinePointComparison_of_tensor_kernels` asks, on every affine open
`W`, for an actual `Γ(X,W)`-linear tensor map to `Γ(N,W)`. It must be
surjective, its actual kernel must equal the submodule of the classified
point, and its value on `1 ⊗ m` must be the restriction of `q m`. The base
algebra is exactly `algOfHom D (hW.fromSpec ≫ f)` used in the existing
comparison definition. Applying the stated quotient equivalence and its
generator formula produces `HasAffinePointComparison D f N q`.

`finiteLocallyFreeDeterminant_isAmple_of_tensor_kernels` composes this
criterion with the existing actual chosen determinant ampleness theorem
for compact `X` and affine `f`. There is no separate fixed-rank frame
premise. The actual tensor maps, their surjectivity and their classified
kernel equalities remain explicit inputs. The provenance is internal:
ordinary quotient linear algebra and the already established actual
Grassmannian determinant criterion provide the whole argument. No
parabolic orbit or kernel equality is asserted by this module.
