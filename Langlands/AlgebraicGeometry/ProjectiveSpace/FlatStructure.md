# Flatness of polynomial projective space over its base

Authors: Worker 5705.

Helper module of the proof of
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement` (entry
module `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`),
written for Task 5705 (`07219dde-fd87-48cf-83be-db16cbb3707c`) under operator request
`98389b48910e54088e0e2b2ba6aaad9c`. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.ProjectiveSpace`. Here `R` is a commutative ring,
`n : ℕ` and `j : Fin (n + 1)`. `ProjectiveSpace R n` is the Library's `Proj` of the polynomial
ring `R[X₀, …, Xₙ]`, and `Away 𝒜 (X j)` is its degree-zero localization away from `X j`. This
is the ring of the standard chart `D₊(X j)`.

- `chartPolynomialMap R n j`: the `R`-algebra map `R[Y_k : k ≠ j] → Away 𝒜 (X j)` sending `Y_k`
  to the ratio `X k / X j` (FLT's `ProjSpace.ratio`).
- `dehomogenize`, `dehomogenizeLoc`, `chartInverse`: dehomogenization at `X j = 1`, on
  polynomials, on the localization away from `X j`, and on its degree-zero part. Together with
  `chartInverse_comp` they show that `chartPolynomialMap` is injective. It is surjective because
  the ratios generate the chart algebra (FLT's `ProjSpace.adjoin_range_ratio`).
- `chartPolynomialMap_bijective` and `chartEquiv R n j :
  MvPolynomial {k // k ≠ j} R ≃ₐ[R] Away 𝒜 (X j)`: each standard chart algebra is a
  polynomial algebra over `R` in `n` variables.
- Instances `flat_away` and `finitePresentation_away`: hence the chart algebras are flat and of
  finite presentation over `R`.
- Instances `flat_projectiveSpaceToSpec` and
  `locallyOfFinitePresentation_projectiveSpaceToSpec`: the structure morphism
  `ProjectiveSpace R n ⟶ Spec R` is flat and locally of finite presentation. Both properties
  are local on the source. They are checked on the standard affine charts, where the morphism
  is `Spec` of the algebra map of the chart algebra (FLT's `ProjSpace.awayι_comp_π`).

## Use

The proof applies `HilbertSchemeUniversalFamilyStatement` to `projectiveSpaceToSpec A n`. That
statement needs a flat morphism, locally of finite presentation.
