# The Chevalley group for the opposite data

Module `Langlands.GroupScheme.SplitExistence.NegGroup`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is derived content.

The opposite data `D.neg` (module `Opposite`) has the same `n`, weights `wt` and root operators
`e` as `D`. The torus homomorphism `torusToGL` and the root homomorphisms `rootToGL j` depend
only on these, so every field of a Chevalley group for `D` is literally a field of a Chevalley
group for `D.neg`.

## Declarations

- `ChevGroup.neg G : D.neg.ChevGroup k`: the same group scheme `G.H` with the same inclusion
  into `GL_n`, torus `t` and root homomorphisms `u j`. Every field is copied unchanged.
- `ChevGroup.neg_H`, `ChevGroup.neg_i`, `ChevGroup.neg_t`: these components are unchanged
  (`rfl`).
- `neg_eF`: the root matrices `e_j(1)` over a field are unchanged.
- `neg_ellWeights`: the weights `ℓ(wt c)` of the regular cocharacter are negated. So the
  regular cocharacter of `G.neg` is the inverse of that of `G`.
