# Integral Hom in finite-dimensional rational subspaces

Module `Langlands.AbelianScheme.HomLocalLatticeProof`.

## Content

`Langlands.AbelianScheme.homLocalLattice : HomLocalLatticeStatement.{u}`.

For every algebraically closed field `k` of characteristic zero, abelian
schemes `A`, `B` over `Spec k`, and finitely generated `ℚ`-submodule `V` of
`Hom0 A B = ℚ ⊗[ℤ] (A ⟶ B)`, the actual integral homomorphisms
`f : A ⟶ B` with `homToHom0 f ∈ V` form a finitely generated `ℤ`-module.
The theorem has no hypotheses beyond those of the statement. It uses
neither `HomFiniteFreeStatement` nor any other unproved statement, and its
axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Proof

`A.X.left` is connected (geometric connectedness over a field), so the
published `smoothConnectedRelativeDimension` gives a relative dimension `g`
for `A`.

- If `g = 0`, the published `hom_eq_zero_of_relativeDimension_zero` shows
  that every `f : A ⟶ B` is zero. Then `A ⟶ B` is a finite, hence Noetherian,
  `ℤ`-module, and every submodule is finitely generated.
- If `g = d + 1`, the published `GroupScheme.fieldAmpleExistence` gives
  ample line bundles `LA` on `A` and `LB` on `B`. Consider the function
  `q = homMixedEuler LA LB (d + 1)`, sending `f` to the actual mixed Euler
  coefficient of `f^* LB` with respect to `LA`.
  `fg_comap_homToHom0_of_homMixedEuler_pos` (module
  `HomPullbackMixedEulerCube`) reduces the conclusion to positivity of `q`
  at nonzero `f`. That module establishes the cube identity of `q` and the
  bound `(d + 1)! · q f ∈ ℤ`. The algebraic lattice lemma
  `CubeQuadratic.fg_comap_of_cubeIdentity` then finishes. Positivity is
  `mixedLineBundleEulerCoefficient_pullback_pos_of_ne_zero` (module
  `HomPullbackMixedEulerPositive`).

## Helper modules of this proof

- `Langlands.Algebra.CubeQuadraticLocalLattice`: a positive `ℚ`-valued
  function that satisfies the cube identity and has bounded denominators
  makes integral points of finitely generated rational subspaces finitely
  generated.
- `Langlands.Algebra.RationalPolynomialNewtonIntegrality`: `d!` clears the
  denominators of Newton polynomials of integer sequences.
- `Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientDenominator`:
  `d!` times an actual mixed Euler coefficient is an integer.
- `Langlands.AbelianScheme.HomPullbackMixedEulerCube`: the cube identity for
  `f ↦ c_{LA}(f^* LB)` and the reduction to positivity.
- `Langlands.AbelianScheme.HomPullbackMixedEulerPositive` (Worker 501):
  positivity of `c_{LA}(f^* LB)` for nonzero `f` and ample `LA`, `LB`.

## Provenance

The statement is the local lattice property underlying the finiteness of
`Hom(A, B)`. Compare J. S. Milne, *Abelian Varieties*, author revision of
the 1986 article (registered as `milne-abelian-varieties-1986-author-2022`),
Theorem 12.5 and its proof. There, `ℚM ∩ End(A)` is shown to be discrete in
`ℚM` using the positive degree polynomial. The implemented route replaces
the degree by the positive quadratic function `c_{LA}(f^* LB)` (see
`HomPullbackMixedEulerCube`). It needs no Tate modules, duals or Rosati
involution. The route is internal to this project.
