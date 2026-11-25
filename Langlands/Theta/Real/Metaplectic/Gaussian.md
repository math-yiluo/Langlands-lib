# The Gaussian vector and the scalar of the metaplectic group

**Outside GKT.** This file belongs to the archimedean theory, which Gan–Kudla–Takeda leave out
(preface, p. iv).
There is no counterpart in the book (over a nonarchimedean field the lattice vectors of GKT §7.2
play the part of the Gaussian). The
declarations are in the name space `Langlands.Theta.Real` (`RealMetaplecticGroup` and its name
space are in `Langlands.Theta`).

The module `Langlands.Theta.Real.Metaplectic.Gaussian` computes the action of
`RealMetaplecticGroup l` on the Gaussian `φ₀ = gaussianVector l = e^{-π‖x‖²}` and the normalizing
scalar `gaussianScalar`.

## Content

For `s = [[A, B], [C, D]] ∈ Sp_{2l}(ℝ)`: `automorphyUpper s = A - iB` is invertible
(`det_automorphyUpper_ne_zero`), and `siegelPoint s = -(C - iD)(A - iB)⁻¹` lies in the Siegel upper half
space (`isSymm_siegelPoint`, `isSiegel_siegelPoint`). `holomorphicPart s = ((A + D) + i(C - B)) / 2`.

For `g` over `s` and `c = gaussianScalar g = (weilSchwartz g φ₀)(0)`:

1. `weilSchwartz g φ₀ x = c · e^{πi xᵀ siegelPoint(s) x}` (`weilSchwartz_gaussianVector_apply`).
   `φ₀` is a vacuum vector of `1`, so `weilSchwartz g φ₀` is a vacuum vector of `s`
   (`weilSchwartz_schrodingerDeriv`); a vacuum vector of `s` satisfies `∂ₐ f = 2πi (τ x)ₐ f` with
   `τ = siegelPoint s` (internal `fderiv_eq_of_annihilated`), and the solutions of this system are the
   multiples of `e^{πi xᵀ τ x}` (internal `schwartz_eq_gaussian_of_fderiv_eq_mulVec`).
2. `c² · det (A - iB) = 1` (`gaussianScalar_sq_mul_det`): the normalization in the definition of the
   group, applied to `φ₀`. Thus `g ↦ gaussianScalar g` is a square root of `det (A - iB)⁻¹` over the
   group; that the two square roots are not separated globally (non-splitting of the cover) is not
   proved.
3. `⟪φ₀, weil g φ₀⟫² · det (holomorphicPart s) = ⟪φ₀, φ₀⟫²` (`inner_gaussianVector_weil_sq`): the
   vacuum matrix coefficient, from the Gaussian integral over the Siegel upper half space
   (`siegelGaussian_pair_standardGaussian`) and `(1 - iτ)(A - iB) = 2 · holomorphicPart s`.
4. For orthogonal `s` (the maximal compact subgroup `Sp ∩ O ≅ U(l)`): the Gaussian of `siegelPoint s`
   is the standard Gaussian, `holomorphicPart s = A - iB` is the unitary matrix of `s`, `φ₀` is an eigenvector with eigenvalue
   `c`, and `c² · det (holomorphicPart s) = 1` (`weilSchwartz_gaussianVector_of_orthogonal`): on the
   preimage of `U(l)`, `g ↦ c` is a square root of `det⁻¹`.

Also `continuous_weilSchwartz_uncurry`: `(g, f) ↦ weilSchwartz g f` is jointly continuous for the
Schwartz topology (the seminorms are controlled through the Weyl algebra by `L²` norms, on which the
action is jointly continuous). Lion–Vergne, *The Weil representation, Maslov index and theta series*,
part I; Folland, *Harmonic analysis in phase space*, chapter 4 (page references to be added).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`: `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticGaussianNormalised.lean`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticCoverWeilRepresentation.lean`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FderivEqMulVecOfSchrodingerAnnihilated.lean`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzEqGaussianOfFderivEqMulVec.lean`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrthogonalSymplecticFixesSiegelPointI.lean`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VacuumMatrixCoefficientSq.lean`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMetaplecticSchwartzActionProd.lean` (all whole), the last two bullets of
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MetaplecticRepresentationHolds.lean` (lines 79–108), and `holPart` of
`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean` (lines 87–88). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The source states its Gaussian lemmas with matrices `P`, `Q` fixed by hypotheses
  `∀ a b, P a b = …`; the public theorems here are stated with `automorphyUpper`, `siegelPoint` and
  the new definition `gaussianScalar`; the source forms are internal.
- `metaplecticGaussianNormalised` and `metaplectic_euclidean_gaussian` were existential statements
  about some group; their contents are `gaussianScalar_sq_mul_det` and
  `weilSchwartz_gaussianVector_apply` about `RealMetaplecticGroup`. The proofs used a second copy of the
  real block (`CompanionTheory.ThKR`); they use the one copy of the Library.
- `continuous_omS_prod`, stated for an abstract quadruple `(G, pr, om, omS)`, is
  `RealMetaplecticGroup.continuous_weilSchwartz_uncurry`.
- `holPart` → `holomorphicPart`; `vacuum_coef_sq` → `inner_gaussianVector_weil_sq` (inner products of
  `L²(EuclideanSpace ℝ l)` in place of integrals over `l → ℝ`);
  `holPart_eq_and_gaussian_of_orthogonal_symplectic` → `weilSchwartz_gaussianVector_of_orthogonal`.
- The twelve wrappers `GlobalTheory.T.*` and their `…Statement.lean` files are not taken.
- The Gaussian is the Library's `gaussianVector` (from `radialGaussian`), not the source's
  `gaussianSchwartz`.

## Declarations

Public declarations of the file (internal ones are in the namespace `Langlands.Theta.Real.Internal` or
`Langlands.HeisenbergGroup.Internal` and are not listed):

- def `Langlands.Theta.Real.holomorphicPart`
- def `Langlands.Theta.Real.siegelPoint`
- theorem `Langlands.Theta.Real.det_automorphyUpper_ne_zero`
- theorem `Langlands.Theta.Real.isSymm_siegelPoint`
- theorem `Langlands.Theta.Real.isSiegel_siegelPoint`
- theorem `Langlands.Theta.RealMetaplecticGroup.continuous_weilSchwartz_uncurry`
- def `Langlands.Theta.RealMetaplecticGroup.gaussianScalar`
- theorem `Langlands.Theta.RealMetaplecticGroup.gaussianScalar_sq_mul_det`
- theorem `Langlands.Theta.RealMetaplecticGroup.weilSchwartz_gaussianVector_apply`
- theorem `Langlands.Theta.RealMetaplecticGroup.inner_gaussianVector_weil_sq`
- theorem `Langlands.Theta.RealMetaplecticGroup.weilSchwartz_gaussianVector_of_orthogonal`

## Dependencies

`Langlands.Theta.Real.Metaplectic.Smooth`, `Langlands.Analysis.SiegelGaussianIntegral`.
