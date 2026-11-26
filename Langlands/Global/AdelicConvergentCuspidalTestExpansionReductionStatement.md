# The convergent cuspidal test expansion from three named inputs

Module `Langlands.Global.AdelicConvergentCuspidalTestExpansionReductionStatement` states the
proposition `Langlands.Global.ConvergentCuspidalTestExpansionReductionStatement` (universe `u`)
and proves nothing.

## Statement

`ConvergentCuspidalTestExpansionReductionStatement` is the implication

`ConstantTermAutomorphyStatement → AutomorphicExponentDecompositionStatement →
LeviCuspFormRapidDecayStatement → ConvergentCuspidalTestExpansionStatement`,

all at universe `u`. The conclusion is the scalar form of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), §6.10, (6.20), in the convergence region (module
`AdelicConvergentCuspidalTestExpansionStatement`). The three premises are the Library
propositions:

- `ConstantTermAutomorphyStatement` (module `AdelicConstantTermAutomorphyStatement`): for standard
  `Q ≤ P`, the constant term along `Q` of an automorphic function on `U_P(𝔸) M_P(F) \ G(𝔸)` is
  automorphic on `U_Q(𝔸) M_Q(F) \ G(𝔸)` (Mœglin–Waldspurger, *Spectral Decomposition and
  Eisenstein Series* (1995), I.2.6, I.2.17);
- `AutomorphicExponentDecompositionStatement` (module
  `AdelicAutomorphicExponentDecompositionStatement`): an automorphic function on
  `U_Q(𝔸) M_Q(F) \ G(𝔸)` is a finite sum of automorphic functions with generalized unnormalized
  exponents (Mœglin–Waldspurger I.3.1–I.3.2; Bernstein–Lapid (6.10));
- `LeviCuspFormRapidDecayStatement` (module `AdelicLeviCuspFormRapidDecayStatement`): a cusp form on
  a standard Levi `M_J` and any exponent `e ≥ 0` admit a bound `B` such that every class of
  `M_J(F) \ M_J(𝔸)¹` has a representative `m` with `H(ι m)^e |ψ(m)| ≤ B`, where `H` is the adelic
  height of `rho` and `ι` the Levi inclusion into `G(𝔸)` (Mœglin–Waldspurger I.2.12, I.2.18).

## How the conclusion follows from the premises

Fix the data of `ConvergentCuspidalTestExpansionStatement`: the standard indices `I`, `Q`, the
rational point `n` with `w = [n]` carrying `I` to `Q`, the compact `K`, the embedding `rho`, an
automorphic `φ` on `U_I(𝔸) M_I(F) \ G(𝔸)`, a standard `J`, a cusp form `ψ` on `M_J` and a point `g`.

1. In the convergence region, the constant term along `P_J` of `E(φ, λ)` is the sum, over the
   minimal representatives `v` of `W_J \ W / W_I`, of the series
   `S_v(y) = ∑_{γ ∈ P_{J_v}(F) \ P_J(F)} M_v(γ y)`. Here `M_v` is the intertwining integral for
   `v` of the twist of the constant term `C_{I_v} φ`, and `P_{J_v} ⊆ P_J` is the target of `v`
   (Bernstein–Lapid, Lemma 6.10, (6.17), p. 208). In the Library this is
   `eisensteinConstantTerm_of_convergence_of_unfolding`, used with `eisensteinAbsoluteConvergence`
   and `geometricLemmaUnfolding`.
2. If `P_{J_v} ⊊ P_J`, then `S_v` is an Eisenstein-type sum on `M_J` along a proper parabolic, and
   its pairing with `ψ` is zero. This is the vanishing of the cuspidal part of Eisenstein series
   induced from proper parabolics, Bernstein–Lapid (6.16), by which (6.17) gives (6.18); in the
   Library it is `properEisensteinTestVanishing`. The invariance of `M_v` under the
   radical of `P_{J_v}` comes from the automorphy of `C_{I_v} φ`
   (`ConstantTermAutomorphyStatement`). The absolute convergence of the unfolded pairing uses the
   decay of `ψ` (`LeviCuspFormRapidDecayStatement`).
3. If `P_{J_v} = P_J`, then `S_v = M_v`. The representative `w` has this property exactly when
   `J ≤ Q`, and then `M_w` is the constant term along `J` of `M(n) φ_λ`, the subtracted term
   (which is `0` when `J ≰ Q`). For each other such `v`,
   `C_{I_v} φ` is automorphic (`ConstantTermAutomorphyStatement`) and is a finite sum of
   generalized eigenfunctions with exponents `ν` (`AutomorphicExponentDecompositionStatement`).
   The intertwining integral carries a component with exponent `ν` to a function with
   unnormalized exponent `v(ν + λ) + offset` along `J`. These are the competing terms. Their
   Weyl element is `v ≠ w`, which maps the roots in `I` to positive roots by minimality.
4. `LeviCuspFormRapidDecayStatement` with `weightedLeviPairingIntegrability` makes all pairings with
   `ψ` over `M_J(F) \ M_J(𝔸)¹` absolutely convergent. The pairing is therefore additive over the
   finite decomposition, which gives the identity of (6.20) (p. 209), in its tested form.

## Provenance

This is an internal decomposition of the proof of Bernstein–Lapid (6.20). It records which
analytic inputs that proof uses beyond results already in the Library (the constant term formula
(6.17) and its convergence, the geometric lemma, and the vanishing of proper Eisenstein-type sums
against cusp forms). The implication itself is not stated in the cited sources. The three
premises are results of Mœglin–Waldspurger I.2.6, I.2.12, I.2.17, I.2.18 and I.3.1–I.3.2, cited
in their own modules.
