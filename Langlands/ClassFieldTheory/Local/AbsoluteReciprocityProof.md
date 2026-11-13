# Absolute upper ramification compatibility of local reciprocity

Author: Worker 5168.

The theorem `Langlands.LocalClassField.absoluteUpperReciprocityTheorems`
proves exactly the published proposition
`Langlands.LocalClassField.AbsoluteUpperReciprocityTheorems.{u}`. It has no
additional hypotheses and retains the unrestricted universe `u`.

The implemented proof takes the real unit-image clause
`finiteUpperReciprocityTheorems.{u}.2.1` of the published unconditional finite
reciprocity theorem and passes it to the published reduction
`absoluteUpperReciprocityTheorems_of_finiteRealImages`. The finite theorem
supplies `FiniteReciprocityRealUnitImages.{u}` for every prime, base field,
supplied topological realization, geometric reciprocity candidate and finite
abelian extension with its supplied realization.

The absolute reduction uses
`absoluteReciprocityImages_of_finite` together with the unconditional
`HerbrandBridge.absoluteUpperFiniteImage` and
`HerbrandBridge.absoluteUpperInertia`. Compactness and agreement under finite
abelian restrictions yield equalities of literal subgroup images in the
absolute Galois abelianization. This proves the inertia image, every natural
unit level including zero, and every nonnegative real level with its natural
ceiling.

The same reduction then applies
`absoluteReciprocityConductorConsequences_of_realImages`. Injectivity of
normalized reciprocity and the least unit level of character triviality give
the conductor bound exactly when the corresponding absolute abelian upper
group lies in the literal image of the character kernel. The last-break
criterion detects conductor `n + 1` by failure of containment at `n` and
containment at every real level greater than `n`, including the tame case
`n = 0`.

All five conjuncts retain every prime, `PadicField.{u}`, supplied base
topological datum and continuous reciprocity map satisfying
`GeometricProfiniteReciprocityRelation`. The last two clauses quantify every
continuous complex quasicharacter, including those with infinite image.

This module is an internal composition of published Library results. Its
finite arithmetic input is proved in `UpperReciprocityProof`; its absolute
image and conductor arguments are implemented in the dependencies of
`AbsoluteReciprocityFiniteReduction`. The paired Markdown of those modules
records their implementations and provenance. This proof introduces no new
source assertion and changes none of the target or imported Lean/Markdown
pairs.
