# Admissibility and finite length of actual refined cuspidal induction

Author: Worker 435.

`Langlands.CuspidalSupport.RefinedCuspidalInductionFiniteLengthStatement`
defines a closed proposition. This file supplies a statement, not its proof.
The field universe `uF` and inducing-carrier universe `uV` are independent.

The proposition quantifies every prime, actual finite p-adic extension,
compatible topological realization `T`, natural rank `n`, block shape `B`,
and refinement `S`. Its input `ω` is an actual complex representation of the
flattened product Levi `(B.flatten S).Levi F.Carrier`. The two premises are
irreducibility of `ω.ρ` and `IsLeviCuspidal (B.flatten S) ω.ρ`. The latter
already includes admissibility, hence smoothness, and vanishing of proper
refined Jacquet modules.

The action is transported to the actual refined subgroup by composing with
`(flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`. Write `σ` for this
transported representation and `I` for
`Rep.of (T.normalizedRefinedInduced B S σ)`. Thus `I` uses the existing
smooth-function carrier, in universe `max uF uV`, for induction inside the
product Levi `B.Levi F.Carrier`. Its covariance uses the actual refined
parabolic projection and the positive half modulus; the ambient action is
right translation. `T.topology` and `T.leviTopologicalGroup B` provide the
topologies required by these constructions.

The three conclusions concern this same `I`:

- `IsAdmissible I.ρ`;
- finite length of `I.ρ.asModule` over the actual complex group algebra of
  `B.Levi F.Carrier`;
- existence of a natural number `m` and an actual composition series of `I`
  of length `m`, using `HasCompositionSeriesLength`.

The last predicate uses the existing invariant-subspace filtration and its
actual irreducible quotient representations. A series and its length are
conclusions. There is no supplied tensor decomposition of `ω`, finite-length
premise, chosen series, finite-generation hypothesis, finite complex dimension,
unitarity, twist parameter, support map, or comparison map. Every natural rank
is included, as are empty and one-block products and equality refinements.

The provenance is internal. This is the product-Levi extension of the
cuspidal-induction finite-length route, with admissibility retained for the
same actual induced object. An intended separate proof can combine admissible
irreducible product factorization, blockwise cuspidal induction, comparison
of refined induction with external tensor products, and the existing
finite-length/composition-series infrastructure. These ingredients are proof
obligations, not assumptions of this proposition or proofs supplied here.
In particular, this statement does not assert a factorial bound or establish
nonvanishing.

Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
Proposition 5.9, printed p.102, motivates the need for finite length of the
fine inner induction in a relative cosocle comparison. The exact product-Levi
telescope above and its separate admissibility conclusion are internal
interfaces, not a literal transcription of that proposition. This statement
does not prove the relative comparison or use the unrestricted wording of
Lemma 5.3. The registered source is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
PDF SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
