# Coordinate-evaluation topology on actual coefficient points

This internal construction topologizes the actual points
`G.affinePoints A = Hom_{Spec R}(Spec A,G)` from `AffinePoints`.
For a point `x` and a global regular function `a` on the underlying
scheme of `G`, `affinePointEvaluation` pulls `a` back along `x` and then
uses `Scheme.ΓSpecIso A` to obtain an element of `A`. The topology is
induced by all these evaluations into the product `A^{Γ(G,⊤)}`.

The source for this topology is Getz–Hahn, *An introduction to
automorphic representations* (2024), §2.2, Theorem 2.2.1 and its proof,
printed pp.51–54, especially the canonical injection (2.8). The Lean
implementation works directly on the published scheme-point carrier.
It uses global sections and the spectrum/global-sections isomorphism
instead of introducing a separate algebra-homomorphism model.

`affinePointEvaluation_injective` uses the affine-target extensionality
theorem and the global-sections isomorphism. Consequently evaluation is a
topological embedding when the underlying scheme is affine, and the
point space is Hausdorff whenever the coefficient space is Hausdorff.
No affineness is required just to define the induced topology.

`continuous_affinePoints_iff` says that a map into this space is
continuous precisely when every regular-function evaluation is
continuous. Pullback of global sections proves continuity for
postcomposition by any morphism over the base, including every
group-scheme homomorphism. In particular, postcomposition by the inverse
morphism gives `affinePointsContinuousInv`. Naturality of `Scheme.ΓSpecIso` proves
`affinePointEvaluation_map`; a continuous coefficient homomorphism
therefore induces a continuous point map.

These are intrinsic properties of the construction. Only a topology on
the coefficient ring is needed for this unit. Finite generation,
finite-coordinate presentations, local compactness, compatibility with
products, continuity of multiplication, the comparison with existing
matrix topologies, and the adelic restricted-product description remain
separate obligations. This unit asserts no reductive reduction or
finite-volume theorem.

The topology instance is indexed directly by the actual morphism carrier
`(algSpec R).obj (op A) ⟶ G.X`, definitionally the shared `G.affinePoints A`.
Its defining coordinate-evaluation map and induced topology are unchanged.
