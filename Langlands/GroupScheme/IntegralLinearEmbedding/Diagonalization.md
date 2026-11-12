# Diagonalization of cocharacters of the general linear group over a principal ideal domain

Author: Worker 4686.

This internal helper module extends the published field case
`GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter`
(`Dynamic/GeneralLinearCocharacterDiagonal.lean`) from fields to principal
ideal domains: every cocharacter of `GL_n` over a principal ideal domain `k`
becomes a diagonal cocharacter after conjugation by an invertible matrix over
`k`. The proof reuses the published coefficient-column API of that file
(`coefficientColumn`, `matrixAt`, `coefficientColumn_weight`,
`span_coefficientColumn`, `rationalMatrixPoint`, `diagonalMatrix`).

The module sets `backward.isDefEq.respectTransparency false` and raises
`maxHeartbeats` to 800000 for the whole file.

## Weight decomposition (namespace `GeneralLinear.CocharacterDiagonal`)

Let `R` be a commutative ring (a principal ideal domain where stated), `I` a
finite type, and `ρ : MatrixRepresentation (splitTorus (Spec R) I) n` a
representation of the split torus with character lattice `I → ℤ`.

* `weightColumns I ρ m` is the span of the published universal coefficient
  columns `coefficientColumn I ρ m j` of exponent `m`.
* `weight_of_mem_weightColumns`: every `v` in `weightColumns I ρ m` is a
  weight vector of weight `m` after every coefficient extension `R → A`: for
  every `t : I → Aˣ`, `matrixAt I ρ t *ᵥ v = t^m • v`, where `t^m` is the
  published `splitTorus.exponentValue`. Induction on the span from the
  published `coefficientColumn_weight`.
* `universalUnits I` is the family of monomial units `X_i` in the group algebra
  `AddMonoidAlgebra R (I → ℤ)`; `exponentValue_universalUnits` evaluates
  `t^m` at it to the monomial of exponent `m`.
* `translateVec I ρ v` is the matrix of `ρ` at `universalUnits I` applied to
  `v`; it is additive and `R`-linear (`translateVec_add`, `translateVec_smul`).
* `weightProjection I ρ m` is the `R`-linear map taking `v` to the coefficient
  of the monomial of exponent `m` in `translateVec I ρ v`.
  `weightProjection_of_mem`: on `weightColumns I ρ m'` it is the identity if
  `m' = m` and zero otherwise.
* `iSupIndep_weightColumns`: the submodules `weightColumns I ρ m` are
  independent, because `weightProjection I ρ m` is the identity on the `m`-th
  one and kills all others.
* `iSup_weightColumns`: they span `n → R`, by the published
  `span_coefficientColumn`.
* `isInternal_weightColumns`: hence `n → R` is their internal direct sum.

## Diagonalization over a principal ideal domain

* `exists_weightBasis`: over a principal ideal domain there are a basis
  `b : Basis n R (n → R)` and weights `w : n → (I → ℤ)` with
  `b j ∈ weightColumns I ρ (w j)`. Each submodule of the free module `n → R`
  is free (`Submodule.basisOfPid`), and the collected basis of the internal
  direct sum is reindexed by `n` (`Basis.indexEquiv`).
* `exists_diagonalizingMatrix_of_isPrincipalIdealRing`: there are
  `B : GL n R` and `w` such that for every `R`-algebra `A` and every
  `t : I → Aˣ`, `B⁻¹ * matrixAt I ρ t * B` is the diagonal matrix with entries
  `t^(w j)`. The matrix `B` has the vectors `b j` as columns.
* `GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing`:
  for a principal ideal domain `k` and a cocharacter
  `χ : Gm ⟶ GeneralLinear.groupScheme n (CommRingCat.of k)`, there are
  `B : GL n k` and `e : n → ℤ` such that `χ` followed by the inner
  automorphism of conjugation by the point `rationalMatrixPoint B` is the
  published `diagonalCocharacter n _ e`. The proof transports `χ` to the rank
  one split torus through `splitTorus.gmIso`, applies the previous theorem to
  get `B` and `w`, and takes `B⁻¹` and `e j = w j PUnit.unit`. Equality of the
  two cocharacters is checked at the universal point of `Gm`, over the Laurent
  polynomial ring (`Gm.hom_ext_universalPoint`), as in the published field
  case.

## Provenance

The module is derived internally. It is the integral version of the published
field case, with the same universal-point technique; the only new input is
that submodules of a finite free module over a principal ideal domain are
free. Over the discrete valuation ring `𝒪[F]` this is the step "a basis
adapted to the grading makes `ρ ∘ χ` diagonal" of the intended proof recorded
in `IntegralModel/IwasawaCellLinear.md`.
