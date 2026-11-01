# Exact finite-length K0 in actual flattened Levi coordinates

Author: Worker 320.

This is an internal specialization of exact continuous-group K0 pullback to
the published actual coordinate equivalence `flattenedLeviEquivContinuous`.
For a topological field `F`, any block shape `B : BlockShape n`, and any
refinement `S : BlockRefinement B`, it defines

```text
flattenedLeviK0 : K0(refinedLevi F B S) ≃ₗ[ℤ] K0((B.flatten S).Levi F).
```

The forward change of acting group is the existing continuous multiplicative
equivalence from the flattened product Levi to the refined subgroup of the
coarse Levi. Thus an actual representation `ρ` of that subgroup becomes the
representation `ρ.comp (flattenedLeviEquiv F B S).toMonoidHom` of the flattened
product. No group equivalence, decomposition certificate, or comparison
hypothesis is added: the coordinate map is the actual published one.

`flattenedLeviK0_toLinearMap` records its definitional forward-map formula.
`flattenedLeviK0_finiteLengthClass` computes the class of the literal bundled
smooth pullback. `flattenedLeviK0_symm_finiteLengthClass` gives the analogous
formula in the other direction, using the inverse continuous coordinate map.
Each formula accepts any finite-length proof for its displayed output; the
generic pullback preservation theorem always supplies such a proof. The
generic linear equivalence supplies the two inverse laws on every virtual
class, with no additional hypotheses.

Both groups use actual smooth complex representations with finite length over
their group algebras and relations from all actual short exact sequences.
This includes nonsplit relations. The field universe `uF` and carrier
parameter `uV` remain independent, with carriers in `Type (max uF uV)`.
All ranks, including zero and the empty products, are included.

The provenance is the internal construction just described. The coordinate
equivalence and its actual matrix embedding and continuity properties are
proved in `Geometric.FlattenedLevi`. The generic exact K0 equivalence proves
finite-length and short-exact preservation and both inverse laws. No new
original-literature theorem is transcribed. This module imposes no
admissibility or finite complex dimension premise and asserts no induction,
Jacquet, geometric-piece, or Aubert compatibility.
