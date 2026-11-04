# Rational-point Lie–Kolchin triangularization

Worker 1485.

`LieKolchinRationalTriangularizationStatement.{u}` is a proposition about every
actual finite matrix representation of a smooth connected affine group scheme
over an algebraically closed field `k : Type u`. Its hypothesis is solvability
of the abstract group of rational points. Its conclusion chooses one actual
`k`-point of the existing general linear group scheme such that the conjugated
representation has zero entries below the diagonal at every rational point.

The representation `ρ : MatrixRepresentation H (Fin N)` is a group-scheme
morphism to the concrete `GeneralLinear.groupScheme`. The rational points of
`H` are the morphisms
`Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X`. The conclusion quantifies over
all these points, both indices `i j : Fin N`, and the condition `j < i`.
It imposes no faithfulness assumption on `ρ`.

This is the rational-point representation consequence of J. S. Milne,
*Algebraic Groups* (2017), Theorem 16.30 and Corollary 16.32, printed
pp.334–335 / one-based PDF pp.350–351. The registered source is
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The source comparisons are as follows.

- Smoothness gives local finite presentation, and affineness gives
  quasi-compactness. Thus the structure map is of finite type, as required
  for the source's affine algebraic groups.
- Proposition 16.34(c)⇔(d), printed p.336 / PDF p.352, identifies solvability
  of the rational-point group with algebraic-group solvability under these
  smoothness, connectedness and algebraic-closure assumptions. This explains
  the hypothesis used here.
- Theorem 16.30 gives trigonalizability. Corollary 16.32 gives a triangular
  basis for any finite-dimensional representation on the rational points of
  the identity component. Connectedness makes that component the whole group.
- `pointMatrix` has coefficients in `Γ(Spec (CommRingCat.of k), ⊤)`. The
  existing `ΓSpecIso` identifies this ring with `k`; the corresponding
  general-linear point equivalence realizes an invertible change of coordinates
  as an actual base point of the general linear group scheme.
- The existing `MatrixRepresentation.conjugate` uses `g A g⁻¹`. A basis
  matrix `P` for the source's convention `P⁻¹ A P` therefore corresponds to
  the inverse matrix for `g`.

There is no characteristic restriction. The dimension `N` may be zero; then
the entry conditions have no indices, and the identity base point is a
coordinate change. The universe parameter `u` is arbitrary.

The complete official errata snapshot of 2026-11-02 was checked. It contains
no correction to Theorem 16.30, Corollary 16.32 or Proposition 16.34. Its
p.324 correction replaces the introductory word “diagonalizable” with
“trigonalizable”, consistently with the results used here.

This module defines the proposition. The theorem
`lieKolchinRationalTriangularization` supplies its proof in the separate
`LieKolchinRationalTriangularization` module. The scheme-theoretic passage
from rational triangularity to a closed embedding is implemented in
`SolvableTriangularEmbeddingReduction`.
