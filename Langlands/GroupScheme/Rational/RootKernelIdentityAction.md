# The descended action on a root-kernel centralizer's identity component

This internal construction uses the actual torus lift into an identity
component and the published fpqc descent of automorphic actions. The field
`k : Type u` and universe `u` are arbitrary. It supplies an action needed for
rank-one arguments and proves no reductivity or normalizer-existence result.

Let `i : T.toGrp ⟶ G`, let `hT : IsSplitTorus T.toGrp`, and let `a` be an
actual character of `T`. Let `j : C ⟶ G` represent the all-test centralizer of
the full scheme-theoretic kernel of `a`. Assume that `C` is smooth and
affine. `kernelCentralizerIdentityAction` is conjugation by the actual lift
`kernelCentralizerIdentityTorus i hT a j hj`, acting on `identityComponent C`.

The general `AutomorphicAction.conjugation_act_comp` proves naturality of
conjugation under any group-scheme homomorphism on every test scheme, by the
homomorphism laws for multiplication and inversion. The ambient action
compatibility follows from the torus lift's composite equation. Cancelling
the monomorphic representative inclusion `j` then identifies the component
action with the published `centralizerAction` after inclusion into `C`.
That action kills the full character kernel; cancellation of the component
inclusion proves `kernelCentralizerIdentityAction_kernelActsTrivially`.
No reduction of the kernel, restriction to rational points, or smoothness
assumption on the kernel occurs.

Under quasi-compactness, flatness and surjectivity of the actual character
map, `kernelCentralizerIdentityQuotientAction` descends that action to an
automorphic action of `Gm` on the same identity component. Its restriction
along the character is exactly the constructed torus action. The inclusion
`identityComponent C ⟶ C` intertwines this descended action with the existing
`quotientAction i a j hj` on every test scheme. To prove the latter equation,
the implementation uses the fpqc local-lift equality criterion for the
acting point, checks the equation after a local lift through the character,
and applies the torus-action compatibility. A global lift of that point is
not assumed.

`existsUnique_kernelCentralizerIdentityQuotientAction` removes the separate
fpqc hypotheses when `a ≠ 0`: the published `characterFpqc` theorem supplies
them for every nonzero character of the split torus. The proof uses the
constructed action, its restriction theorem, and uniqueness of fpqc action
descent. The character may be divisible, so its kernel may be nonreduced.

The provenance is internal composition of `Rational.RootKernelIdentityTorus`,
`Rational.RootSubgroup`, `RepresentedAction`, `ActionDescent`, and
`Rational.CharacterFpqcProof`. The identity-component construction of
Workers 947 and 967 and the fpqc action-descent construction of Worker 1335
are reused unchanged. Smoothness, affineness and representability of `C`
remain explicit assumptions. This file does not assert that the identity
component is reductive, that the action has nontrivial weights, or that any
normalizing point moves a root.
