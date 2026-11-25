# Complete normed models of finite algebras over Noetherian Banach algebras

Lean module: `Langlands.Geometry.Analytic.FiniteAlgebraNormedModel`
(namespace `Langlands.Analytic.FiniteNormedModel`). Support module for the proof of `AffineAnalytificationFiniteGermComparisonStatement`.

## Content

Let `K` be a nontrivially normed field, let `R` be a complete, ultrametric, Noetherian normed
`K`-algebra, and let `E` be a commutative `R`-algebra that is finite as an `R`-module. The module
puts on a copy `Model K R E` of `E` a norm that makes it a complete, ultrametric normed
`K`-algebra, with a bounded structure map from `R`.

* `rank`, `gen`, `coeff`: chosen generators `gen i` of `E` and the surjective `R`-linear map
  `coeff : Rⁿ → E`, `w ↦ ∑ i, w i • gen i`.
* `Quot`, `gam`: the quotient of `Rⁿ` (sup norm) by `ker coeff`, with the quotient norm, and the
  `R`-linear identification `gam : E ≃ Quot`.
* `structConst`, `bound`: chosen coefficients of the products `gen i * gen j`, and a constant
  `bound ≥ 1` bounding them.
* `Model K R E` is `E` with the norm `‖x‖ := bound * ‖gam x‖` (`norm_def`). Instances:
  `NormedCommRing`, `NormedAlgebra K`, `IsUltrametricDist`, `CompleteSpace`.
* `ofModel : Model K R E ≃ₐ[R] E` is the identity. `baseHom : BoundedAlgHom K R (Model K R E)` is
  the structure map, with `ofModel_baseHom`.

## Proofs

* Submultiplicativity: `norm_gam_mul_le` gives `‖gam (x y)‖ ≤ bound * ‖gam x‖ * ‖gam y‖`. For
  representatives `u`, `w`, the product is `coeff` of `∑ i j, (u i * w j) • structConst i j`
  (`coeff_mul`). The ultrametric inequality bounds this sum by `bound * ‖u‖ * ‖w‖`. Scaling the norm by `bound` turns this into `‖x y‖ ≤ ‖x‖ ‖y‖`.
* `K` and `R` act boundedly on `Quot`: `norm_smul_quot_le` and `norm_scalar_smul_quot_le`.
* Ultrametric: quotients of ultrametric normed groups are ultrametric
  (`isUltrametricDist_submoduleQuotient`).
* Completeness: `ker coeff` is closed in `Rⁿ` by the Library's
  `isClosed_submodule_pi_of_noetherian_banach` (submodules of `Rⁿ` over a Noetherian Banach
  algebra are closed). So `Quot` is complete, and `gam` is bi-Lipschitz onto it.

## Provenance

Internal Library infrastructure. It adapts the quotient-norm construction in the Library's
`StrictTestDomain.FiniteRationalTensorComparisonProof` and
`GeneralizedAffinoid.FiniteTensorComparison.Proof` to an arbitrary finite algebra, and it reuses
`isUltrametricDist_submoduleQuotient` from the former. The
underlying fact is standard: a finite algebra over a Noetherian Banach algebra carries a complete
quotient norm. `FinitePieceLocalProof` uses the model to build test algebras out of finite
`R`-algebras.
