# The coroot formula for the actual relative Weyl action

This is an internal linear algebra consequence of the integral reflection data
and the Weyl invariant positive definite form used in Renard, *Représentations
des groupes réductifs p-adiques* (9 July 2026), V.3.7 and V.3.13–V.3.18.
It supports the proof of Langlands' combinatorial lemma for the actual torus
character space; it assumes no additional group structure results.

The Lean proof extends the integral reflection identity to real tensors by
tensor induction. The coroot pairs to two with its root, so the reflection
negates that root and the real root vector is nonzero. Applying invariance
of the bilinear form to a general vector and the root gives
`pair(x, coroot) * B(root, root) = 2 * B(x, root)`.
Positive definiteness permits division by the root length and makes vanishing,
positivity, and nonnegativity of the two evaluations equivalent. The coroot
annihilator of a set of actual roots is therefore the orthogonal complement of
their real span. `realCorootFunctional` names the real coroot evaluation used
in these comparisons.

Restrictions of rational characters are fixed by the actual Weyl action:
this follows by tensor induction from the group character conjugation
identity. Invariance then implies that they are orthogonal to every root,
and hence to the whole real relative root span, and annihilate every supplied
coroot.
