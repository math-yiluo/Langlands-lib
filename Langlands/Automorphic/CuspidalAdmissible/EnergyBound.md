# The energy bound for vectors killed by Casimir polynomials

Module: `Langlands.Automorphic.CuspidalAdmissible.EnergyBound`.
Provenance: internal. Third algebraic step of the proof of joint admissibility of unitary
cuspidal realizations: a Gårding-type bound of the first-order "energy" of a vector by its
norm, for vectors on which the Casimir and the compact Casimir satisfy fixed polynomial
equations. It uses `Ω_full = Ω + 2 Ω_K`, where `Ω_full` is the sum of squares of an
orthonormal real basis for the Cartan-positive form.

All declarations are in `Langlands.Automorphic.CuspidalAdmissible`.

## Abstract inner-product algebra (section `Core`)

`V` is a complex vector space with a Hermitian form given as an
`InnerProductSpace.Core ℂ V` named `c`.

- `IsCoreSkew c D`: `c(D f, g) = -c(f, D g)`; `IsCoreSymm c T`: `c(T f, g) = c(f, T g)`.
- `inner_zero_left_core`, `inner_zero_right_core`: `c(0, y) = c(y, 0) = 0`.
- `IsCoreSymm.add`, `.neg`, `.sub`, `.zero`; `IsCoreSkew.mul_self`: `D` skew implies `D²`
  symmetric; `isCoreSymm_sum_sq`: a finite sum of squares of skew operators is symmetric.
- `energy_eq_core`: for skew `D_i`,
  `∑_{i ∈ s} re c(D_i e, D_i e) = -re c((∑_{i ∈ s} D_i²) e, e)` (induction on `s`, using
  `c(D_i² e, e) = -c(D_i e, D_i e)`).
- `norm_inner_le_of_aeval_core`: the Rayleigh bound
  `‖c(T x, x)‖ ≤ rootBound q · re c(x, x)` for `c`-symmetric `T`, nonzero `q` and
  `q(T) x = 0`. It equips `V` with the normed and inner-product structures of `c`
  (`InnerProductSpace.Core.toNormedAddCommGroup`, `InnerProductSpace.ofCore`) and applies
  `norm_inner_self_le_of_aeval` of `PolynomialRayleigh`.
- `energy_le_core` (**abstract energy bound**): if `D_i` are skew,
  `∑_{i ∈ s} D_i² = A + 2 B` with `A`, `B` symmetric, and nonzero `q`, `p` satisfy
  `q(A) e = 0`, `p(B) e = 0`, then
  `∑_{i ∈ s} re c(D_i e, D_i e) ≤ (rootBound q + 2 rootBound p) · re c(e, e)`.
  Proof: the left side is `-re c(A e, e) - 2 re c(B e, e)`, and `-re z ≤ ‖z‖`.

## The realization

For `S : OperatorRealization F n`:

- `realOperator S X := S.envelopingAction (realEnvelopingGenerator F n X)`, the real Lie
  operator `D_X`; `squareSumOperator S s X := ∑_{i ∈ s} D_{X_i}²`;
  `envelopingAction_sum_sq`: it is the action of `∑ X_i X_i` in the enveloping algebra.
- `casimirOperator_eq`: `Ω = ∑ D_{Z_j}² - ∑ D_{Y_i}²` over the normalized complementary
  and compact Cartan bases (from `matrixCasimir_eq_complementary_sub_compact`).
- `compactCasimirOperator_eq_squareSum`: `Ω_K = ∑ D_{Y_i}²`.
- `cartanSquareSum_eq`: `∑_i D_{X_i}² = Ω + 2 Ω_K` for the normalized adapted basis
  `cartanAdaptedBasis F n` (from `cartanSquareSum_eq_casimir_add_twice_compact`).

For a unitary form `b : S.UnitaryForm` (Library structure: one positive definite Hermitian
form invariant under finite and compact translations, with every real Lie operator skew):

- `isCoreSkew_realOperator b X`: `D_X` is skew for `b` (`b.real_skew`).
- `isCoreSymm_casimirOperator b`, `isCoreSymm_compactCasimirOperator b`: `Ω` and `Ω_K` are
  `b`-symmetric.
- `energy b e := ∑_i re b(D_{X_i} e, D_{X_i} e)` over the adapted basis `X_i`.
- `energy_le b hq hp hqe hpe` (**energy bound**): if `q ≠ 0`, `p ≠ 0`, `q(Ω) e = 0` and
  `p(Ω_K) e = 0`, then `energy b e ≤ (rootBound q + 2 rootBound p) · re b(e, e)`.
