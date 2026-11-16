# Descending an invariant atlas cocharacter through an actual solution

This internal construction descends a normalized cocharacter through a supplied
actual solution of group-scheme descent along any surjective étale map. Neither
the base nor the cover is assumed affine or quasi-compact.

`Descent.gmBaseChange_overlap` identifies the canonical multiplicative-group
overlap with the normalized multiplicative-group identifications on the two
projections. Its proof applies the previously established multiplicative-group
pullback tower equality twice to the common composite to the base and cancels
the direct-pullback comparison.

`compatible_of_cocharacter_invariant` turns the normalized equality

```
baseChangeCocharacter fst χ ≫ D.overlap.hom = baseChangeCocharacter snd χ
```

into `Descent.Compatible` for the relative homomorphism obtained by
precomposing χ with `Gm.baseChangeIso p`. The overlap equality above translates
between these normalized and relative formulations.

Given an actual solution `s` of `D`,
`Descent.Solution.cocharacterOfEtale` applies actual étale homomorphism descent
from the canonical solution on the multiplicative group to `s`. Its normalized
pullback composed with `s.iso.hom` is exactly χ
(`cocharacterOfEtale_recovers`). The uniqueness of étale homomorphism descent,
after cancelling the multiplicative-group identification, proves
`cocharacterOfEtale_unique`.

`AffinePinnedAtlas.descendedCocharacter` specializes this construction to the
canonical positive-coroot cocharacter of an affine pinned atlas, using its
proved overlap invariance. `descendedCocharacter_recovers` gives the exact
recovery equation through the supplied solution comparison.

All content is derived internally from actual multiplicative-group pullback
coherence, published étale homomorphism descent, and the assembled atlas
cocharacter's overlap invariance. The natural pinning comparison and an actual
solution of its corrected datum remain supplied. No existence of either,
subgroup geometry, or unconditional quasi-split inner-form theorem is proved
in this module.
