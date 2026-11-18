# Grassmannian points over the actual affine open section algebra

Let `p : X → Spec R` and let `f` map `X` to a represented
Grassmannian over `Spec R`, respecting the structure map `p`.
For an affine open `U`, `affineOpenPoint` classifies the composite
`Spec Γ(X,U) → X → Gr` using the coefficient algebra on `Γ(X,U)`
induced by `p`. The actual affine chart formula supplies its
compatibility with the structure map. The represented-point
equivalence returns the original composite.

The coefficient algebra extracted by the Grassmannian's `algOfHom`
agrees with the algebra induced by `p`. Both structure ring maps
give the same relative spectrum morphism, and spectrum is faithful.
`hasAffinePointComparison_of_affineOpenTensorKernels` transports the
tensor comparison along this algebra equality. If the actual generator
map is surjective with the classified kernel and the prescribed values
on `1 ⊗ m` on each affine open, it gives the required actual quotient
comparison for the determinant.

This is an internal application of the actual affine chart formula,
Grassmannian representability, and the existing comparison from
tensor kernels. In the parabolic jet argument the description uses
the coefficient algebra already present on the actual jet module
and the tensor of the base complement.
