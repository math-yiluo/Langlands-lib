# General linear derivatives as mirabolic derivatives of the restriction

Author: Worker 745. Helper module of the proof of Ze80 Proposition 1.11(a),
first conjunct (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`).

For `0 < k ≤ N + 1`, the published derivative
`Derivative.generalLinearDerivative T ψ (N+1) k hk : GL_(N+1) ⥤ GL_(N+1-k)`
equals, as a functor, restriction to the mirabolic subgroup `P_(N+1)`
(`generalLinearRestriction T N`) followed by the published mirabolic
derivative of order `k`, `mirabolicDerivativeOfOrder T ψ N k hk'`. This is the
definition `π^(k) = Ψ⁻ (Φ⁻)^(k-1) (π|_P)` of BZ77 §3.5 and §4.3 (Bernstein and
Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i`, printed pp.452 and
454). Both Library functors implement that definition, but they place the
rank transports differently. This module proves that they agree.

## Declarations

Namespace `Langlands.Derivative`.

- `restriction_derivative_cast` (private): after `subst` on the rank equation,
  the two orders of rank transport and restriction agree by `rfl`.
- `generalLinearDerivative_eq_restriction_comp T ψ N k hk hk'`: the functor
  equality above. The case `k = 0` is excluded by `hk'`. For `k = j + 1`, both
  sides unfold (`generalLinearDerivative` is `generalLinearRankCast` followed
  by `generalLinearDerivativePositive`, and `mirabolicDerivativeOfOrder` is
  `mirabolicRankCast` followed by `mirabolicDerivative`). The private lemma
  applies with the published rank equations `rank_eq_of_succ_le` and
  `mirabolic_rank_eq_of_order`.
- `generalLinearDerivative_obj_eq_restriction`: the same equality on objects.

The universes `uF` (field) and `uV` (carrier) are independent. `T.topology` is
installed in every statement.

## Provenance and dependency audit

Internal: a definitional comparison of two published functors, original to
this module. The only direct import is
`Langlands.Representation.Derivative.Homogeneity`. Its closure consists of the
published derivative-definition modules (`Derivative.MirabolicCharacter`,
`MirabolicMinus`, `Iteration`, `Homogeneity`) and their group,
smooth-representation and Jacquet-coinvariant prerequisites. It contains no
classification or segment module. No derivative theorem (exactness,
detection, pairing, Leibniz rule or supercuspidal derivatives) is used.
