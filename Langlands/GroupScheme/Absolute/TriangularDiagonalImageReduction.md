# Diagonalizable presentations of actual triangular diagonal images

This is an internal reduction for the triangular diagonal splitting proof.
It is derived from the existing Library definitions and keeps two structural
statements as explicit premises: `AffineHomImageStatement` and
`Diagonalizable.ClosedSubgroupPresentationStatement`. It does not prove either
premise or construct a section.

`range_kernelι_comp_mono` proves that postcomposing a group-scheme homomorphism
with a monomorphism on the underlying objects over the base leaves its full
scheme-kernel range unchanged. On every test scheme it uses
`mem_range_kernelι_iff` and cancellation of that monomorphism.
The proof reuses `RelativeRoot.IsFppfQuotient.comp_iso` from the published
`Torus.CentralExtensionSplit` module to transport a represented fppf quotient
along an actual target isomorphism. That theorem preserves flatness,
surjectivity and local finite presentation by composition with the
isomorphism, and preserves the full kernel on every test scheme.

`DiagonalImageReduction.exists_diagonalizable_factorization` takes any map
from an affine group scheme locally of finite type over a field to a split
torus. Assuming the two structural statements, it produces a finitely
generated abelian group `Λ`, a closed immersion `d : D(Λ) ⟶ L` and a map
`q : H ⟶ D(Λ)` with `q ≫ d = f`. The map `q` is an fppf quotient by the full
kernel of the original `f`, on all test schemes.

The proof first applies the affine-image statement. A split-torus
isomorphism identifies the target with `D(I → ℤ)` for a finite type `I`.
The subgroup-presentation statement then identifies the intermediate image
with `D(Λ)`. The proof transports the projection and inclusion along this
isomorphism.

`DiagonalImageReduction.Presentation f` packages the resulting actual maps,
their finitely generated character group and the three proved properties.
`DiagonalImageReduction.presentation` chooses such data for a map to a
split torus under the same two explicit premises. The character-group
addition and finite-generation instances are included in the package.

`DiagonalImageReduction.exists_triangular_diagonalizable_factorization`
specializes this construction to the block-limit diagonal projection with
weights `i ↦ -i`. Their injectivity identifies the block Levi group with
the split torus indexed by `ULift (Fin N)`, using the published
`GeneralLinear.diagonalTorusIso`. It covers every natural `N`, including
zero, and requires no smoothness or connectedness. The character group `Λ`
may have torsion. This image reduction works for an arbitrary triangular
homomorphism, so closedness of that homomorphism is not a premise here.

The provenance is internal categorical assembly of published interfaces;
no independent assertion from the literature is added.
