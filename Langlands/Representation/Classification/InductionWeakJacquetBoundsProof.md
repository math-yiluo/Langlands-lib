# Preservation of weak upper Jacquet bounds by actual GL induction

Author: Worker 828.

`Langlands.glInductionWeakJacquetBounds` proves the published proposition
`Langlands.GLInductionWeakJacquetBoundsStatement.{uF,uV}`, with independent
field and carrier universes.

The proof is a single application:
`glInductionWeakJacquetBounds_of_geometricLemma Geometric.padicGeometricLemma`.

- `Langlands.glInductionWeakJacquetBounds_of_geometricLemma`, in
  `Langlands.Representation.Classification.InductionWeakJacquetBoundsAssembly`,
  derives the target from `Langlands.Geometric.PadicGeometricLemmaTheorem`.
- `Langlands.Geometric.padicGeometricLemma`, in
  `Langlands.Representation.Geometric.GeometricLemmaProof`, is the
  published, independently accepted proof of that theorem (Workers 164 and
  194, task 67ebcf61-3d58-4499-9c0c-c847e90aaeb4). It has no premise, so
  the final theorem adds no hypothesis.

## Route

For a standard Jacquet exponent `χ` of the induced representation for the
ambient block shape `C`:

1. The geometric lemma filters `jacquetInductionFunctor T B C` naturally,
   with graded pieces naturally isomorphic to the normalized geometric pieces
   of the minimal representatives `w`. Worker 573's
   `RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter` places
   `χ` in one graded piece.
2. That piece is normalized refined induction of a transported normalized
   refined Jacquet module of `σ`. The induction half modulus is trivial on
   block scalars of `C`. So `χ` is a generalized eigencharacter of the source
   Jacquet module, restricted along the inverse Weyl transport of these block
   scalars (Spectral module and chamber coordinates).
3. Inverse transport carries the block scalars of `C` to flattened block
   scalars of the source refinement `S w`, through the chamber index.
   Admissibility of the refined Jacquet module and a common-eigenvector
   argument in one finite-dimensional fixed space extend `χ` to an
   open-kernel exponent `ψ` on all flattened block scalars.
4. The chamber index is monotone within each block of `B`, because `w` is a
   minimal representative. Hence a globally increasing tuple `a` restricts
   to a tuple increasing within each outer block. The source premise for
   `D = S w` bounds `‖χ a‖ = ‖ψ (restriction of a)‖` by one.

The helper modules and their Markdown give every step:

- `Langlands.Representation.Exponents.CentralEigencharacterExtensionProof` (published separately, proving `Langlands.CentralEigencharacterExtensionStatement`)
- `Langlands.Representation.Parabolic.UpperRefinedJacquetAdmissibilityProof` (published separately, proving `Langlands.Parabolic.UpperRefinedJacquetAdmissibilityStatement`)
- `Langlands.Representation.Classification.InductionWeakJacquetBoundsSpectral`
- `Langlands.Representation.Geometric.IntersectionChamberCoordinates` (published separately as a definition unit)
- `Langlands.Representation.Classification.InductionWeakJacquetBoundsAssembly`

The irreducibility premise is not used, and no hypothesis is added.
Sources: Waldspurger 2003, III.2.3 (`waldspurger-2003-plancherel`, printed
pp.266–267); Bernstein–Zelevinsky 1977, 2.11–2.12
(`bernstein-zelevinsky-1977-induced-i`).
