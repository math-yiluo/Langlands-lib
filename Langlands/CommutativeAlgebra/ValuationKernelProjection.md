# Split kernels over valuation domains

Let `R` be a commutative valuation domain, `M` a finite `R`-module,
and `N` a torsion-free `R`-module. The ring and the two modules may
lie in independent universes. No rank, Noetherian or nonfield condition
is imposed on `R`.

`valuationKernelProjection f` is a chosen `R`-linear endomorphism of
the actual source `M` of `f : M →ₗ[R] N`. Its range is `LinearMap.ker f`,
and it is the identity on that kernel. It is therefore idempotent.
The choice need not be canonical.

The range of `f` is finite, as the image of `M`, and torsion-free, as
a submodule of `N`. The imported valuation-domain freeness theorem
makes this range free. Mathlib's lifting property for projective
modules supplies a section `s` of the surjection `M → range f`.
The implemented projection is `id - s ∘ f.rangeRestrict`. Applying
`f` proves its image lies in the kernel; on the kernel its second
term vanishes. These facts prove the range equality and idempotence.

It follows that the kernel is finite: it is the image of the finite
module `M` under this projection. If `M` is also torsion-free, then
its kernel is finite torsion-free and hence free over `R`.
For every ideal `I` of `R`, the module additionally satisfies

`ker f ⊓ (I • ⊤) = I • ker f`.

For the nontrivial inclusion, apply the projection to a vector in
the left side. The projection fixes that vector, and the image of
`I • ⊤` is `I • ker f`. The reverse inclusion follows from the two
usual inclusions for an ideal multiple of a submodule.

The second construction applies these facts to polynomial vectors.
For any finite variable type `σ` and natural numbers `n` and `d`,
`homogeneousPolynomialVectors R σ n d` is the `R`-submodule of
`Fin n → MvPolynomial σ R` consisting of vectors all of whose
coordinates are homogeneous of degree `d`. It is finite over `R`:
Mathlib proves each coordinate homogeneous submodule finitely
generated, and finite products preserve this property. This particular
finiteness result only assumes that `R` is a commutative ring.

For any polynomial-linear map from `n` polynomial coordinates to
`m` polynomial coordinates, `homogeneousPolynomialKernelPiece f d`
is the actual kernel of its restriction to that finite homogeneous
source, viewed as an `R`-linear map into the full polynomial-vector
target. The target is torsion-free over the valuation domain `R`.
The preceding finite-kernel theorem makes this kernel finite, and
its inherited torsion-freeness makes it free. The matrix itself need
not be homogeneous for these degree-piece assertions.

This is an internal algebraic derivation from the actual splitting
and the imported valuation freeness and Mathlib homogeneous-space
results. It does not assert that the full polynomial kernel is
finitely generated, establish polynomial coherence, or prove the
host task's line-bundle extension statement.
