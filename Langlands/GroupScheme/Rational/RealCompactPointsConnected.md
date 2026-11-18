# Compact real points of connected reductive groups are connected (Borel–Tits 14.3)

This helper module proves the connectedness half of `RealAnisotropicCompactConnectedStatement`
from compactness.

## Main result

`Langlands.GroupScheme.RealCompactPoints.connectedSpace_of_compactSpace G hG`: let
`G : GroupScheme (Spec (CommRingCat.of ℝ))` with `[IsAffine G.X.left]` satisfy
`IsConnectedReductive G`. Give the real points `G.affinePoints (CommAlgCat.of ℝ ℝ)` the
Library's evaluation topology `G.affinePointsTopologicalSpace` (a local instance here, together
with the topological group structure `affinePointsIsTopologicalGroup`). If this space is
locally connected and compact, then it is connected.

Local connectedness is a hypothesis here. It is supplied in
`Langlands.GroupScheme.Rational.RealAnisotropicCompactConnectedProof` by the real charts of a
smooth scheme.

## Proof

1. `connectedReductiveSelfAdjointRealizationStatement` gives a closed matrix representation
   `ρ : MatrixRepresentation G (Fin d)`. Its real points map `r = ρ.affineMatrix` is a closed
   embedding (`isClosedEmbedding_affineMatrix`).
2. Let `H` be the identity component (`Subgroup.connectedComponentOfOne`). Local
   connectedness makes it open, so it has finite index in the compact group
   (`Subgroup.quotient_finite_of_isOpen`).
3. `C = r(H)` is a compact subgroup of `GL_d(ℝ)`. If some `g` were outside `H`, then
   `r(g) ∉ C`, and Chevalley's separation `exists_polynomial_separating` gives a polynomial
   `p` vanishing on `C` with `p(r(g)) ≠ 0`. But `eval_eq_zero_of_finiteIndex` (from
   `Langlands.GroupScheme.Rational.FiniteIndexPolynomialVanishing`) says `p` vanishes on all of
   `r(G(ℝ))`. So `H` is everything and the space is connected.

## Provenance (derived)

Borel–Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), registered as
`borel-tits-1965-groupes-reductifs` (SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`), 14.3, printed p.146
(PDF p.93): « si G ⊂ GL(n, C) est connexe, défini sur R, et si G_R est compact, alors G_R est
connexe. » The module proves this for connected reductive `G` (the case needed), with the
extra hypothesis of local connectedness, which always holds and is discharged elsewhere.
Borel–Tits argue with Chevalley's theorem and the Zariski closure of the identity component;
this module uses Chevalley's separation property and the density of rational points instead.
