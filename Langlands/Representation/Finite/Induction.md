# Finite-index induction of actual representations

This construction uses the existing quotient-induced action
`Representation.ind S.subtype V.ρ` of Mathlib. The field `k : Type u` and group
`G : Type v` have independent universes. The subgroup `S` is an actual subgroup
of `G` with the explicit instance `S.FiniteIndex`; it need not be normal.
The source is an actual `FDRep k S`. Every subgroup of a finite group satisfies
the index condition. The construction also applies to infinite ambient groups
with finite-index subgroups and to arbitrary coefficient fields.

## Carrier, finite-dimensionality and universe transport

Mathlib's `IndV` is the coinvariant quotient of `k[G] ⊗[k] V` for the diagonal
`S` action. In its basis convention, the action of `g` sends `[h ⊗ v]` to
`[h g⁻¹ ⊗ v]`. Inverting the group-algebra index matches the usual left-action
induction convention. This is an actual quotient representation with its
action and module laws already proved in Mathlib, not a prescribed function
called an induced character.

`coindEvaluation` is the linear map from the equivariant-function coinduced
space to functions on the right-coset quotient, evaluating at a chosen
representative `q.out`. `coindEvaluation_injective` uses the equivariance
identity to recover a function's value at every group element from the value
at its coset representative. The coset set is finite under `S.FiniteIndex`.
A finite product of finite-dimensional vector spaces is finite-dimensional,
and `Module.Finite.of_injective` gives `finiteCoind`.

`indCoindEquiv` reuses Mathlib's proved `Rep.indCoindIso` on `Rep.of V.ρ`.
Its inverse linear equivalence transfers finite-dimensionality to the
actual quotient-induced carrier in `finiteInd`. These arguments assume
neither semisimplicity nor characteristic zero.

The induced carrier can live in universe `max u v`. `induceRep` applies the
proved coordinate model from `Classes` to place it in `FDRep k G`'s carrier
universe `u`. `induceRepEquiv` is an explicit equivariant linear equivalence
from the actual quotient action to that model. Arbitrary source carrier
universes can first use `classOfRepresentation` from `Classes`; its equality
criterion proves that this passage loses no finite-dimensional
representation isomorphism classes.

## Descent to actual classes

`induceIso` applies Mathlib's genuine induction functor to an equivariant
isomorphism, then composes the coordinate equivalences. This proves the
quotient congruence needed to define `induce`.

`coindSumEquiv` splits an equivariant function into its two components and
pairs such functions in the reverse direction. All linearity, inverse and
equivariance conditions are proved explicitly. Composing with the existing
induction–coinduction equivalences gives `indSumEquiv`. The zero case uses
the subsingleton coinduced function space. The class constructor's proved
sum compatibility then gives the additive map `induceHom`.

Finally, `character_induce_classOf` identifies its character with the trace
of the actual quotient-induced action. No independent arbitrary function
is supplied as an induction operation.

## Original source and dependencies

Jean-Pierre Serre, *Linear Representations of Finite Groups*, English
translation by Leonard L. Scott, Springer GTM 42 (1977), Section 7.1,
printed pages 54–55, Proposition 18 and Remarks 1–2, defines induction by
the actual group-algebra tensor module, characterizes it by an isomorphism,
and gives its universal property. Section 7.2, pages 55–56, Proposition 20(ii),
identifies the induced character with the character of the induced
representation. These original passages were read in the retained PDF.

- Literature ID: `serre-1977-linear-representations`.
- SHA256: `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
- Retained source:
  `C:/Central-Library/Serre--Linear Representations of Finite Groups--1977.pdf`.

The right-coset evaluation proof, coordinate transport and quotient descent
are internal implementations using the pinned Mathlib constructions; no
extension of the source's character classification is asserted.
The project dependency is `Langlands.FiniteRep.RepClass` and the proved
coordinate-model and class operations from
`Langlands.Representation.Finite.Classes`. This module is imported from the
Library at the workspace base
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`; its published Lean and Markdown
are unchanged from the construction used during development.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The additional Mathlib import is
`RepresentationTheory.FiniteIndex`, including its actual `Induced` and
`Coinduced` constructions. These intrinsic proofs require no new project
axioms, no topology on a representation space, and no character-faithfulness
or Brauer theorem.
