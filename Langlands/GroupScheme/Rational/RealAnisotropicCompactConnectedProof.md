# Real points of anisotropic connected reductive groups are compact and connected

This module proves the proposition `Langlands.GroupScheme.RealAnisotropicCompactConnectedStatement`
(module `Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedStatement`):

`Langlands.GroupScheme.realAnisotropicCompactConnected`: for every
`G : GroupScheme (Spec (CommRingCat.of ℝ))` with `[IsAffine G.X.left]`, if
`IsConnectedReductive G` and `IsAnisotropic G`, then `RingPoint ℝ G.X ℝ`, with the Library's
evaluation topology, is a compact space and a connected space.

The declaration is a proved definition: a `def` whose type is the proposition
`RealAnisotropicCompactConnectedStatement`, so that it can be submitted as a definition record.
The `def` form changes nothing about what is proved. Mathlib's `defProp` linter is switched off
for this one declaration. The proposition is not a class, so no instance attribute is involved.

## Proof

The proof works on `G.affinePoints (CommAlgCat.of ℝ ℝ)` with the topology
`G.affinePointsTopologicalSpace`. At the end it transfers both properties to
`RingPoint ℝ G.X ℝ` through the Library's homeomorphism `G.affinePointsRingPointHomeomorph`.

1. **Compactness.** `RealPolar.compactSpace_of_torusBound`
   (`Langlands.GroupScheme.Rational.RealPolarCompactness`) reduces compactness to bounded
   matrices on closed tori. That bound holds for anisotropic `G` by
   `IsAnisotropic.exists_abs_rationalMatrix_le_of_closedTorus`
   (`Langlands.GroupScheme.Rational.RealAnisotropicTorusBound`). The required instances
   `IsAffineHom G.X.hom` and `Smooth G.X.hom` (hence locally of finite type) come from
   `IsConnectedReductive G`.
2. **Local connectedness.** The published `smoothConnectedRelativeDimension` gives a
   relative dimension `n` of the smooth connected scheme `G.X.left`. The published
   `Langlands.AlgebraicGeometry.PointManifold.realSmoothAffineChartedSpace G.X n hn` (module
   `Langlands.AlgebraicGeometry.PointManifold.SmoothAffineManifold`, imported through
   `Langlands.GroupScheme.SmoothAffinePointLieGroup`) makes `RingPoint ℝ G.X ℝ` a charted space
   modelled on `Fin n → ℝ`, and Mathlib's `ChartedSpace.locallyConnectedSpace` makes it locally
   connected. The homeomorphism `G.affinePointsRingPointHomeomorph` transfers this to
   `G.affinePoints` (`Topology.IsOpenEmbedding.locallyConnectedSpace`).
3. **Connectedness.** `RealCompactPoints.connectedSpace_of_compactSpace`
   (`Langlands.GroupScheme.Rational.RealCompactPointsConnected`) gives connectedness from
   compactness and local connectedness.

## Helper modules

This development consists of the following modules, each with its own Markdown file:

- `Langlands.Group.CompactMatrixZariskiClosure`: Chevalley's separation property for compact
  subgroups of `GL_n(ℝ)` (Stone–Weierstrass and Haar averaging).
- `Langlands.GroupScheme.Rational.FiniteIndexPolynomialVanishing`: a matrix polynomial that
  vanishes on a finite-index subgroup of the rational points of a connected reductive group over
  an infinite field vanishes on all rational points (density of rational points).
- `Langlands.GroupScheme.Rational.RealCompactPointsConnected`: compact and locally connected
  real points of a connected reductive group are connected (Borel–Tits 14.3).
- `Langlands.GroupScheme.Rational.RealAdditiveFactorGrowth`: polynomial growth of the matrices
  of integer points of `𝔾ₐ`.
- `Langlands.GroupScheme.Rational.RealPolarEigenvalueBound`: eigenvalues of real points are at
  most `1` when closed tori have bounded matrices.
- `Langlands.GroupScheme.Rational.RealPolarCompactness`: compactness of the real points from
  the polar decomposition.
- `Langlands.GroupScheme.Rational.RealAnisotropicTorusBound`: bounded matrices on the real
  points of closed tori of anisotropic groups.

## Provenance (derived)

The proved proposition is the one stated, with source correspondence, in
`Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedStatement`: Borel–Tits,
*Groupes réductifs*, Publ. Math. IHÉS 27 (1965), registered as
`borel-tits-1965-groupes-reductifs` (SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`), Corollary 9.4 (printed
p.127, compactness, for `k = ℝ`) and 14.3 (printed p.146, connectedness). The proof follows the
route above. Its connectedness step follows the idea of 14.3 (Chevalley's theorem on compact
linear groups). Its compactness step is not Borel–Tits's argument: it uses the Library's polar
decomposition and positive-power factorization.
