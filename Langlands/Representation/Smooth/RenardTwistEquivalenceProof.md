# Character twisting as an equivalence and two adjunctions

Author: Worker 139. The theorem `Langlands.Renard.Smooth.twistEquivalence`
proves exactly `TwistEquivalenceStatement`, preserving its independent universes
and both specified open-kernel hypotheses.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, III.1.15, Remark 3, printed p.68 / PDF p.74 (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
It identifies twisting by a character and its inverse as mutually inverse
functors and asserts both adjunctions. This proof covers these four claims;
it does not restate the later preservation and exactness consequences.

The internal `CharacterTwist` constructions work over an arbitrary commutative
coefficient ring. The published identities `twist_inv_twist` and
`twist_twist_inv` identify the composite actions with the original action.
`equivOfRepresentationEq` makes each equality an equivariant identity linear
map, and `SmoothRep.mkIso` bundles it as an isomorphism. These isomorphisms are
natural because twisting preserves the underlying maps. They give `cancel`
and `cancel'`, natural isomorphisms from the two composite functors to the
identity.

Mathlib's `Equivalence.mk` converts these data into an equivalence with exactly
the specified forward and inverse twist functors. Its `toAdjunction` and the
same construction for the symmetric equivalence give the two requested
adjunctions. No size restriction, admissibility, continuity beyond the given
open kernels, or extra smoothness hypothesis is introduced. The statement
module and all its imports are unchanged.
