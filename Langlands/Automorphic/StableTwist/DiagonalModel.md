# Diagonal Weil–Deligne models

Author: Worker 389.

This supporting module constructs the diagonal Weil–Deligne pair attached to characters
`η_1, …, η_n`: the action `g · v = (η_1(g) v_1, …, η_n(g) v_n)` on a universe-lifted copy of
`ℂ^n`, with zero monodromy. For quasi-characters `μ_1, …, μ_(r+1)` of `K^×` and a reciprocity
candidate `e`, the pair `localDiagonal K e μ` with characters `μ_i ∘ e` is the parameter
`⊕_i (μ_i ∘ e)` matched with the principal series `i(μ_1, …, μ_(r+1))`. These are the
"diagonal parameters" `X₀`, `Y₀` of the proof of Henniart (1986), Lemma 4.2: their
determinants are `(∏ μ_i) ∘ e`, and they satisfy the hypotheses of
`PrincipalSeriesPairGammaMatchStatement` (continuous, zero monodromy, upper triangular in a
basis with diagonal characters `μ_(σ i) ∘ e`, here with `σ = 1` and the matrix diagonal). The
module adds no axiom.

## Declarations

Namespace `Langlands.Automorphic.StableTwist`.

General group `G`:

- `diagonalOperator n`: the linear map `c ↦ (v ↦ (c_i v_i)_i)` from `ℂ^n` to the endomorphisms
  of `ULift (Fin n → ℂ)`; `diagonalOperator_apply_down` is its coordinate formula.
- `diagonalRepresentation η`: the representation `g ↦ diagonalOperator n (η_i(g))_i`.
- `diagonalBasis n`: the standard basis of `ULift (Fin n → ℂ)`, with `diagonalBasis_repr`
  and `diagonalBasis_apply_down`; `diagonalBasis_repr_apply`: the `(i, j)` matrix coefficient
  of `g` in this basis is `η_i(g)` if `i = j` and `0` otherwise.
- `diagonalFinite η`: the finite-dimensional representation; `diagonalFinite_rank`: its rank
  is `n`; `diagonalFinite_determinantCharacter`: its determinant character is `∏ η_i` (the
  matrix in the standard basis is `diag(η_i(g))`, and `Matrix.det_diagonal`).
- `diagonalFinite_isContinuous`: for continuous `η_i : G →ₜ* ℂˣ` the representation is
  continuous, i.e. `g ↦ ρ(g)` is continuous into `End(V)` with the module topology; this is
  `diagonalOperator` (continuous as a linear map between finite-dimensional spaces with
  module topologies, `IsModuleTopology.continuous_of_linearMap`) composed with the
  continuous map `g ↦ (η_i(g))_i`.
- `diagonalWD ν η`: the Weil–Deligne pair with this representation and zero monodromy
  (`WeilDeligneRepresentation.zeroMonodromy`), for any norm character `ν`.
- `twistDiagonalWDEquiv` and `twistClass_diagonalWD`: if `η'_i = χ η_i` for all `i`, the
  identity map of the carrier is an equivalence of Weil–Deligne pairs from the twist of
  `diagonalWD ν η` by `χ` to `diagonalWD ν η'`; hence their classes agree.

Local field `K`, reciprocity candidate `e`:

- `weilCharacter_mul`, `weilCharacter_prod`: `weilCharacter K e` (pullback of a
  quasi-character along `e`) is multiplicative and commutes with finite products.
- `localDiagonal K e μ`: `diagonalWD` for the local norm character of `K` and the characters
  `weilCharacter K e (μ i)`.
- `localDiagonal_spec`: for `μ : Fin (r + 1) → QuasiCharacter K`, the pair `localDiagonal K e μ`
  has rank `r + 1`, monodromy `0`, a continuous Weil action, determinant character
  `weilCharacter K e (∏ μ_i)`, and in the basis `diagonalBasis` with the identity permutation
  every Weil element acts by a matrix with zero entries below the diagonal and diagonal
  entries `μ_i ∘ e`.
- `twistClass_localDiagonal`: twisting the class of `localDiagonal K e μ` by
  `weilCharacter K e χ` gives the class of `localDiagonal K e (fun i => μ i * χ)`.

## Sources and provenance

Internal construction. The diagonal parameters attached to principal series are the
parameters `⊕ μ_i ∘ e` of Henniart, *On the local Langlands conjecture for GL(n): the
cyclic case*, Ann. of Math. 123 (1986) (`henniart-1986-cyclic`), proof of Lemma 4.2, printed
p.158. The Weil–Deligne pair, twist and class conventions are those of
`Langlands/WeilDeligne/Basic.lean` and `Langlands/WeilDeligne/Twist.lean`.
