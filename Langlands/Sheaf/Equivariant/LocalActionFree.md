# Free module sheaves on discrete presheaves

This internal lemma uses the existing definitions of discrete sections and
finite equivariant refinements. Let `S` be a local action system on a category
`T` for a topological group `G`, and let `R : Type w` be a commutative ring.
For a presheaf `F : Tᵒᵖ ⥤ Type w`, a section with an open fixing subgroup
gives a generator with the same fixing subgroup in `F ⋙ ModuleCat.free R`.
This is `IsDiscreteSection.freeMk`; the proof uses the free functor's
restriction formula on generators.

`LocalActionSystem.IsDiscrete.free` states that a discrete type-valued
presheaf has a discrete free module presheaf. The proof uses finite-support
induction: zero is discrete, sums use intersection of two open fixing
subgroups, and a singleton with coefficient `r` is `r` times its discrete
generator.

Assume module sheafification for a topology `J` and
`S.HasFiniteEquivariantRefinements J`. The theorem
`LocalActionSystem.IsDiscrete.freeSheaf` applies the existing
`isDiscrete_sheafify` to conclude discreteness of the actual
`SiteCech.freeSheafFunctor J R` applied to `F`.

The provenance is internal. These lemmas use finite support and published
sheafification preservation, with no new geometric existence or continuity
claim.
