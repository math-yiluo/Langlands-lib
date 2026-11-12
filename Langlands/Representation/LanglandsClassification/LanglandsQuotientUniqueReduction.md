# The unique Langlands quotient from four closed prerequisites

Worker 148. This is an internal assembly of Renard VII.4.2 (i), printed p.243 /
PDF p.249. The theorem `langlandsQuotientUnique_of_inputs` proves the exact
published `LanglandsQuotientUniqueStatement`, with its independent universes
and full telescope, assuming four existing closed propositions at universes
`u, v`:

- `LeviSecondAdjointnessStatement`: normalized induction from every actual
  rational parabolic is left adjoint to Jacquet restriction to every supplied
  opposite parabolic with the same Levi, on carriers in `max u v`.
- `LeviInductionFiniteLengthStatement`: actual normalized induction sends
  every smooth representation of finite group-algebra length in `v` to one
  of finite length in `max u v`.
- `OppositeIdentitySupportStatement`: for actual opposite parabolics, the
  actual identity boundary-support image in `r_Q i_P(sigma)` is equivariantly
  isomorphic to the original inducing representation `sigma`.
- `LanglandsTripletOppositeKernelStatement`: for every Langlands triplet and
  every supplied actual opposite parabolic with the same Levi, the twist
  `sigma tensor psi` satisfies `PQ`-regularity, expressed as comaximality of
  the two split-component action kernels.

These propositions quantify over every local field and every actual group,
parabolic and representation in their published scopes. None is silently
proved by the construction, and no premise only about the particular triplet
replaces one of them. In particular the first proposition retains the
published `max u v` carrier universe of the adjunction, while the other
representation inputs use the original inducing universe `v`.

For a Langlands triplet with inducing twist `tau = sigma tensor psi`, the
proof obtains irreducibility from the irreducibility of `sigma` and twist
invariance. Normalized-exponent temperedness of `sigma` includes admissibility;
twist invariance therefore supplies admissibility of `tau` as well.
`oppositeLeviParabolic` constructs actual opposite parabolic and radical
schemes, keeping the original Levi scheme and its exact ambient homomorphism.
It supplies the parabolic, rational Levi, geometric radical, multiplication,
ambient-map equality and rational-point intersection certificates needed by
the four prerequisites. Thus no separate opposite-existence premise is used.

The four universal inputs specialize to this chosen opposite and `tau`.
`exists_regularOppositeLeviHead` then gives a smooth representation `pi` in
`max u v` with `IsIrreducibleHead (i_P(tau)) pi`. That helper handles the
original carrier in `v` through an explicit induction equivalence from a
carrier lift, obtains nonzero maps by second adjointness, splits them using
central-kernel regularity, embeds every irreducible quotient into opposite
induction by Frobenius reciprocity, and compares kernels using the
one-dimensional Hom space. Finite-length preservation supplies quotient
existence. Consequently the result has the exact strong-head meaning of the
published component: existence of a surjective irreducible quotient and
agreement of kernels for every algebraic irreducible quotient map in the
source universe `max u v`.

`langlandsTripletHeadOfInputs` applies this theorem to the original full
triplet telescope and chooses an actual smooth head together with its
`IsIrreducibleHead` certificate. The field and carrier universes remain
independent; the constructor preserves all original objects and hypotheses.
Its choice is noncanonical.

This is derived internal content. It connects the preceding actual-functor
construction to the exact published uniqueness component and packages a
certified chosen object. The four prerequisite proofs remain obligations of
their existing proof tasks. It proves neither parameter injectivity nor
exhaustion and therefore does not prove `LanglandsClassificationStatement` or
complete its proof task. The classification statement pair and everything it
imports are unchanged.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, version
dated 9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249, from second adjointness
through the opposite Jacquet retraction and Frobenius reciprocity to uniqueness
of the irreducible quotient. Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
