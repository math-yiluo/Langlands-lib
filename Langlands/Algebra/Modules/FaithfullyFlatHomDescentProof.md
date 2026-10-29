# Proof of faithfully flat module morphism descent

Author: Worker 124.

`Langlands.Algebra.Modules.faithfullyFlatModuleHomIsoDescent` proves the
exact proposition
`Langlands.Algebra.Modules.FaithfullyFlatModuleHomIsoDescentStatement`.
The two component theorems are also available separately as
`faithfullyFlatModuleHomDescent` and `faithfullyFlatModuleIsoDescent`.

## Implemented proof

Write `F = ModuleCat.extendScalars f`, `G = ModuleCat.restrictScalars f`,
and let `η` be the unit of `ModuleCat.extendRestrictScalarsAdj f`.
The private lemma `comparison_isEquivalence` obtains the equivalence of
`K = CategoryTheory.Comonad.comparison (extendRestrictScalarsAdj f)`
directly from `comonadicExtendScalars hf`, where
`hf : RingHom.FaithfullyFlat f`. The adjunction stored by Mathlib's
comonadicity construction is definitionally the extension/restriction
adjunction appearing in the statement. Consequently `K` is full and faithful
for the precise canonical coactions `F.map (η.app M)`.

For morphism descent, the supplied equation for `g` has the opposite equality
orientation from `Comonad.Coalgebra.Hom.h`. Its symmetry therefore makes `g`
the underlying map of a coalgebra morphism `g' : K.obj M ⟶ K.obj N`.
The preimage `K.preimage g'` is the required map over `A`.
Applying `Comonad.Coalgebra.Hom.f` to `K.map_preimage g'` proves that extending
this map gives the specified `g`. For uniqueness, the equality of extended
maps gives equality of the underlying maps of coalgebra morphisms.
`Comonad.Coalgebra.Hom.ext` and faithfulness of `K` then give equality of
the original maps.

For isomorphism descent, `Comonad.Coalgebra.isoMk e he.symm` promotes the
given isomorphism to an isomorphism of the canonical coalgebras.
This constructor proves compatibility of the inverse using compatibility
of the forward map and the two inverse identities. Full faithfulness supplies
`K.preimageIso` of this coalgebra isomorphism. The same `map_preimage`
identity, followed by the underlying-map projection and `Iso.ext`, proves
that its extension is exactly `e`. Uniqueness follows by equality of the
extended forward maps, coalgebra morphism extensionality, faithfulness,
and `Iso.ext`.

The final theorem pairs these two proofs. Every use of descent here comes
from Mathlib's proved comonadicity for the actual faithfully flat ring map.
The proof introduces no additional ring, finiteness or descent-equivalence
hypothesis. The separate scheme pullback comparison and gluing obligations
of the downstream application are outside this proposition.
