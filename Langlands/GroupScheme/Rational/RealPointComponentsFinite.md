# Finitely many components of real points of connected reductive groups

This helper module proves part 2 of `Langlands.GroupScheme.RealPointComponentsStatement`
(Milne, *Algebraic Groups* (2017), Corollary 25.55, printed p.560):

`Langlands.GroupScheme.finite_connectedComponents_of_isConnectedReductive`: for every
`G : GroupScheme (Spec (CommRingCat.of ℝ))` with `[IsAffine G.X.left]` and
`IsConnectedReductive G`, the type `ConnectedComponents (RingPoint ℝ G.X ℝ)` is finite.
`RingPoint ℝ G.X ℝ` has the evaluation topology of
`Langlands.AlgebraicGeometry.PointTopology.AffineScheme`.

This declaration is a proved definition: a `def` whose type is the proposition
`Finite (ConnectedComponents (RingPoint ℝ G.X ℝ))`, so it is submitted as a
definition record. The `def` form changes nothing about what is proved. Mathlib's
`defProp` linter is switched off for this one declaration. Because `Finite` is a class,
the declaration is marked `@[instance_reducible]`. It is not registered as an instance.

The module states nothing beyond this result and the auxiliary lemmas listed below.
It does not prove part 1 (Cartan's theorem) of the target statement.

## Route

Milne derives the result from an exact sequence `e → N → G' × T → G → e` and the
finiteness of `H^1(ℝ, N)`. The 2022 reprint also cites Whitney's theorem on real
algebraic varieties. This module uses neither. It uses the polar (Mostow) decomposition
that the Library already proves for adjoint-stable matrix realizations:

1. **Every point is joined to the unitary part.**
   `connectedReductiveSelfAdjointRealizationStatement` (from
   `Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof`) gives a closed
   matrix representation `ρ : MatrixRepresentation G (Fin d)` whose real image is
   stable under transpose. For a real point `g`,
   `exists_affineUnitary_right_quotient_posDef` (`Langlands.GroupScheme.AffinePolarCompact`)
   gives `a` in the unitary inverse image `K = ρ.affineUnitarySubgroup` such that
   `P = ρ(g a⁻¹)` is positive definite. The image of `ρ` is polynomially defined
   (`affineMatrix_range_isPolynomiallyDefined`), so `positivePower_mem`
   (`Langlands.Group.AlgebraicPolar`) puts every real power `P^t` in it. The map
   `t ↦ P^t ρ(a)` takes values in the image. Since `ρ` is a closed embedding on real
   points (`isClosedEmbedding_affineMatrix`), it lifts to a continuous map `ℝ → G(ℝ)`
   with value `a` at `0` and `g` at `1`. Transported by the identity homeomorphism
   `affinePointsRingPointHomeomorph`, this shows that `g` lies in the connected
   component of `a`. This is `RealPointComponents.exists_unitary_mem_connectedComponent`.
2. **Components are open.** `IsConnectedReductive` gives smoothness and connectedness of
   `G`, so `smoothConnectedRelativeDimension` provides a relative dimension `n`.
   `realSmoothAffineChartedSpace` then gives a charted space modelled on `Fin n → ℝ`
   on the existing evaluation topology instance (no new topology is introduced; compare
   `smoothAffine_topology_eq_evaluation`). Mathlib's `ChartedSpace.locallyConnectedSpace` makes `G(ℝ)` locally connected,
   so `ConnectedComponents G(ℝ)` is discrete.
3. **Conclusion.** `K` is compact (`isCompact_affineUnitarySubgroup`), so its image in
   the discrete space `ConnectedComponents G(ℝ)` is compact and therefore finite. By
   step 1 this image is everything.

## Auxiliary lemmas

- `Langlands.Group.AlgebraicPolar.continuous_positivePower`: for a positive definite
  `g : GL n 𝕜` with `𝕜` an `RCLike` field, `t ↦ positivePower g hg t` is continuous into
  `GL n 𝕜` with the units topology. The proof unfolds `positivePower` as the
  conjugate of the diagonal unit with entries `x_i ^ t` by the eigenvector unitary. It
  checks continuity of the value and of the inverse, whose entries are `(x_i ^ t)⁻¹`
  with `x_i > 0`.
- `Langlands.Group.AlgebraicPolar.positivePower_zero`: `positivePower g hg 0 = 1`,
  from `positivePower_add` with both exponents `0`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`), Corollary 25.55,
printed p. 560 (PDF page 576): "Let G be a reductive algebraic group over R. Then G(R)
has only finitely many components for the real topology."

The proved proposition is part 2 of the Library statement
`Langlands.GroupScheme.RealPointComponentsStatement`, with the same reading as there:

- Milne's reductive group over `ℝ` is `IsConnectedReductive G`, so it is smooth, affine
  and connected (see `Langlands.GroupScheme.Reductive.Basic`).
- The real topology is the Library's evaluation topology on `RingPoint ℝ G.X ℝ`.
- "Finitely many components" is finiteness of `ConnectedComponents`.

The proof follows the route described above, not Milne's.
