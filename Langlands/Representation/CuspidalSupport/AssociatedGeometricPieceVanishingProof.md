# Vanishing of nonconjugating associated geometric pieces

Author: Worker 178.

This proof targets the published `AssociatedGeometricPieceVanishingTheorem`.
The finite permutation group acts on ambient subgroups by conjugation. In a
finite group orbit of a partial order, comparable elements are equal: translate
the comparison to a subgroup compared with its own translate, apply Mathlib's
`smul_eq_of_smul_le`, then translate back. This gives the required
associated-containment implication without block-size classification.

A full source refined parabolic has full refined Levi by the published
`refinedLevi_eq_top_of_refinedParabolic_eq_top`. The intersection equality
therefore places every conjugated source-Levi element in the target Levi.
Association forces equality by the preceding finite-orbit argument, contradicting
nonconjugacy. The source refinement is thus proper. The published
`geometricPieceFunctor_subsingleton_of_proper_source` now gives vanishing of
the actual normalized geometric piece on the smooth quasicuspidal input.

The final theorem keeps every parameter of the published component, including
independent field and carrier universes; it also covers rank zero. The subgroup
argument does not need minimality, smoothness or representation hypotheses.
The final conclusion uses the exact existing geometric functor and all given
intersection refinements. No geometric filtration, finite length or exclusion
of the zero input is assumed. This is the first component only: it does not
prove the piece equivalence or preservation of quasicuspidality under transport.

The source motivation is the nonconjugating-piece reduction in BZ77 Corollary
2.13(c), as documented in the unchanged statement Markdown. The implemented
containment argument is an internal finite-group alternative to its described
block-partition route; it imports the published vanishing and subgroup helpers.
