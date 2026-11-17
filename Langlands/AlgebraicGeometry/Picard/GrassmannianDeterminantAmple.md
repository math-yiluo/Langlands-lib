# Actual determinants classified by a Grassmannian

Let `D` be the represented quotient Grassmannian of rank `k` quotients of a
module `E` over an arbitrary commutative ring `R`, and let `f : X → D.Gr`.
The actual sheaf of modules `N` on `X` has specified global generators
`q : E → Γ(N, top)`. `HasAffinePointComparison` means that on every affine
open `W` of `X`, the quotient classified by the point `hW.fromSpec ≫ f` is
linearly equivalent to the actual module `Γ(N,W)`, carrying each quotient
of `1 ⊗ m` to the restriction of `q m`.

`basis_test_iff_preimage` proves that a tuple of these actual sections is a
basis on an affine open exactly when that open maps into the corresponding
Grassmannian chart. It transports the finite coefficient map through the
specified linear equivalence and applies the chart classification property
of `D`. The range of `hW.fromSpec` is precisely `W`.

For compact `X` and affine `f`, with actual free sheaf charts of constant
rank `k` covering `X`, `finiteLocallyFreeDeterminant_isAmple` proves ampleness
of the standard actual `finiteLocallyFreeDeterminant hN`. The preimages of
Grassmannian charts are affine and cover `X`; the preceding comparison
identifies them by the actual section basis tests. The determinant-section
criterion then proves the assertion using actual determinant sections.

This is an internal result derived from Grassmannian chart representability,
affine morphisms and the actual determinant basis-locus criterion. It requires
no noetherian hypothesis. The supplied module, global generators, comparison
on all affine opens, compactness, affine morphism and constant-rank frames
are explicit hypotheses. Constructing them for parabolic jet modules and
identifying their determinants with powers of the Lie determinant dual remain
separate obligations. No parabolic ampleness theorem is asserted here.
