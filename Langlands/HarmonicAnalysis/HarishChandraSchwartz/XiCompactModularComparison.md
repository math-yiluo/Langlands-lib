# Comparing spherical functions for compact open subgroups

Worker 248, Task 5460. Module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactModularComparison`, namespace
`Langlands.HarishChandraSchwartz`. The proposition definition
`XiCompactComparisonStatement.{u}` is proved by the included theorem
`xiCompactComparison`. It has an arbitrary carrier universe `u`.

This is a derived prerequisite for the actual-point constant-term estimate of
Waldspurger, Proposition II.4.5. It starts from the definitions and invariant
pairing of Waldspurger I.1, I.3 and II.1, as implemented in `Spherical` and
`SphericalInverse`. It is not a separately numbered assertion of the source.

For a locally compact second countable unimodular topological group, a closed
subgroup `P`, its modular character `δ`, and compact open subgroups `K,L` with
`G = P K = P L`, the spherical functions `xi` are bounded by positive constant
multiples of one another. The Lean theorem is directional; interchanging the
compact subgroups gives the reverse inequality.

The proof first bounds one positive Iwasawa weight by a constant multiple of the
other: the quotient of these weights is left `P` invariant and the second compact
factor covers `P \ G`. It then proves the change-of-average identity
`average_K φ = average_K(w_L²) average_L φ` for continuous functions satisfying
`φ(p x) = δ(p) φ(x)`. Right-translation invariance of `average_K`, Fubini on the
compact product, and the left Haar invariance on `L` give this identity.
Apply it to `φ(x) = w_L(x g) w_L(x)`. Positivity and the comparison of weights
bound the corresponding coefficient for `K`. Evaluation at the identity, where
both spherical functions equal one, shows that the resulting constant is
positive.

More precisely, `P` is additionally assumed locally compact with its subgroup
topology. The group has a measurable space with `BorelSpace`; compact subgroups
have their inherited topology and normalized Haar measures. No reductive group,
Cartan covering, height, or weighted unipotent estimate is used. The actual
rational-point and Levi specializations are left for a later contribution.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`.
The compact quotient integral is in I.1, printed p.240, the invariant pairing
in I.3, printed p.243, and the spherical coefficient in II.1, printed p.250.
Source SHA256:
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The comparison is derived here, with no additional analytic estimate as a premise.
