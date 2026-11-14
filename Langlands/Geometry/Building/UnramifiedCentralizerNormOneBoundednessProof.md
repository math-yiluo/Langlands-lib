# Algebraic boundedness of the norm-one unramified centralizer

Author: Worker 336. This module proves the exact published proposition
`Langlands.Geometry.Building.MaximalUnramified.CentralizerNormOneBoundedStatement.{u}`
for Task 6432, at arbitrary universe `u`, by the theorem
`Langlands.Geometry.Building.MaximalUnramified.centralizerNormOneBounded`.
The statement pair and its imported pairs are unchanged.

For every nonarchimedean local field `F`, affine group scheme `G` over the
actual field `K = inertiaFixedField F`, and supplied `C : BuildingData F G`,
the conclusion is algebraic boundedness in `G` of exactly
`rationalPoints.map C.centralizer.j '' characterValuationKernel (valuation F) C.centralizer.Z`.
The valuative relation is exactly
`ValuativeRel.ofValuation (fixedFieldValued F).v`, as prescribed by the
target. There are no additional hypotheses.

The implemented proof is the composition

```lean
centralizerNormOneBounded_of_henselianDiscreteQuasiSplit
  (Langlands.GroupScheme.henselianDiscreteQuasiSplit_of_dimensionLEOne
    Langlands.GroupScheme.dimensionLEOneQuasiSplit)
```

The published theorem `dimensionLEOneQuasiSplit`, from module
`Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof`, proves
quasi-splitness of connected reductive groups over fields satisfying the
finite-separable unit-norm criterion for dimension at most one. The
published reduction `henselianDiscreteQuasiSplit_of_dimensionLEOne`, from
module `Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction`,
uses the proved dimension theorem for a Henselian discretely valued field
with algebraically closed residue field. Applying that reduction to the dimension-one theorem therefore gives `HenselianDiscreteQuasiSplitStatement`
with no remaining premise.

The imported centralizer reduction specializes this result to the actual
inertia fixed field using the published surjectivity, Henselianity and
algebraic closedness of its residue field. In a quasi-split group it
identifies the supplied centralizer of the supplied maximal split torus
as a torus: existence and rational conjugacy transport a torus
representative, and uniqueness of represented subgroups identifies it
with `C.centralizer.Z`.

The torus bound used by that reduction compares the prescribed
integer-normalized character kernel with the spectral character-unit
locus. Its proof uses finite Galois splitting, norm characters, Laurent
coordinate bounds, and descent of bounds for actual regular functions.
Pullback along the actual inclusion `C.centralizer.j` bounds its image.
Completeness is used only for the original local field `F`; no
completeness or local-field structure on `K` is assumed.

This closing module adds only the displayed composition. Its proof route
uses the quasi-split and torus results corresponding to Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8, printed p.81
(PDF p.112), and Proposition 2.5.8, printed pp.88–89 (PDF pp.119–120).
The precise adapters and their implemented proofs are described in the
paired Markdown of the imported modules.
