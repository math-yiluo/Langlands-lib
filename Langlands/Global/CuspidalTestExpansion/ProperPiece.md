# Bruhat pieces with a proper target parabolic have zero cusp-form pairings

Module `Langlands.Global.CuspidalTestExpansion.ProperPiece`
(namespace `Langlands.Global.StandardParabolicFamily.NestedLeviParabolic`).

Let `t : NestedLeviParabolic fam J₁ J`: `P_{J₁} ⊆ P_J` (`t.inclusion`), a projection
`t.projection : P_J → M_J` with section `fam.l J`, and the parabolic `P' = t.P` of `M_J` with Levi
`t.M` and radical `t.U`, such that `P_{J₁}` is the preimage of `P'` (`t.pullback_eq`) and the
radical of `P'` lies in that of `P_{J₁}` (`t.radical_le`). Write `ι : M_J(𝔸) → G(𝔸)` for
`map (fam.l J ≫ fam.p J)`. This is the situation of Bernstein–Lapid, *Meromorphic continuation
of Eisenstein series* (2024), §6.10: the terms of the constant term formula (6.17) whose target
`P_{J₁}` is a proper subgroup of `P_J` are Eisenstein-type sums on `M_J` along the proper
parabolic `P'`, and so are orthogonal to cusp forms on `M_J`.

## Declarations

- `section_projection_hom`, `rational_comp`: bookkeeping for points.
- `leviRational_mem_iff`: for a rational point `q` of `M_J`, `ι(q) ∈ P_{J₁}(F)` iff
  `q ∈ P'(F)`.
- `exists_mul_leviRational`: every `b ∈ P_J(F)` is `a · ι(q)` with `a ∈ P_{J₁}(F)` and `q` a
  rational point of `M_J` (take `q` the projection of `b`).
- `radical_map_mem`: `ι` maps `t.U(𝔸)` into the adelic points of the radical of `P_{J₁}`.
- `tsum_ambientCosets_eq`: for `f` left invariant under `P_{J₁}(F)`, the sum of `f(γ y)` over
  `P_{J₁}(F) \ P_J(F)` equals the sum of `f(ι(γ) y)` over `P'(F) \ M_J(F)` (norm-one
  rational points), by `CosetTransfer.tsum_cosetEquiv` with the two lemmas above.
- `properPiece_pairing`: assume `J₁ < J`, `0 < N`, and let `Pint : G(𝔸) → ℂ` be continuous, left
  invariant under `P_{J₁}(F)` and under the adelic points of the radical of `P_{J₁}`, with
  `∑_{γ ∈ P_{J₁}(F) \ P_J(F)} ‖Pint(γ y)‖ₑ ≤ C · H(y)^D` for all `y`, where `C, D ≥ 0` and `H`
  is the adelic height of `rho`. Let `ψ` be a cusp form on `M_J`
  (`fam.IsLeviCuspForm Kinf rho J ψ`) and `B₀` a real number such that every class of the norm-one quotient
  `M_J(F) \ M_J(𝔸)¹` has a representative `m` with `H(ι m)^D ‖ψ(m)‖ ≤ B₀`. Then for
  `S(y) = ∑_{γ ∈ P_{J₁}(F) \ P_J(F)} Pint(γ y)` and every `g`, the pairing integrand
  `fam.leviPairingIntegrand J S g ψ` is integrable on the norm-one quotient and
  `fam.leviPairing J S g ψ = 0`.

## Proof of `properPiece_pairing`

Apply `properEisensteinTestVanishing` to the ambient group `M_J`, the parabolic `t.p` with Levi
`t.l` and radical `t.iU`, the function `f(z) = Pint(ι(z) g)` and the test `ψ`:

- the instances for `t.P`, `t.M`, `t.U` (affine, locally of finite type, closed immersions) come
  from the closed immersions `t.p`, `t.l`, `t.iU`;
- the norm-one quotients of `M_J` and `t.M` have finite volume
  (`connectedReductiveFiniteVolume`), and that of `t.P` by `normOneRationalQuotientFiniteVolume`
  (it is smooth and connected, `IsRationalLeviSubgroup.connectedSpace`);
- `f` is left invariant under `P'(F)` (`leviRational_mem_iff`) and under the adelic points of
  the radical of `P'` (`radical_map_mem`); `ψ` is left `M_J(F)`-invariant and has zero constant
  term along the radical of `P'` because `P' ≠ M_J` (`t.proper`, `IsLeviCuspidal`);
- the sum over `P'(F) \ M_J(F)` in `properEisensteinTestSum` is the coset sum `S` at `ι(m) g`
  (`tsum_ambientCosets_eq`), so the integrand of the conclusion is the pairing integrand;
- the absolute sum at the chosen representative `m` is bounded by
  `C · H(ι(m) g)^D ‖ψ(m)‖ ≤ C · H(g)^D · H(ι m)^D ‖ψ(m)‖ ≤ C · H(g)^D · B₀`
  (`adelicHeight_mul_le`, `one_le_adelicHeight`).
