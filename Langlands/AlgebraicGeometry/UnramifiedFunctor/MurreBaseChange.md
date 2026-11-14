# Murre's conditions are stable under base change

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChange` proves

- `murreBaseChange : MurreBaseChangeStatement.{u, v}`.

The statement `MurreBaseChangeStatement` is in
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`. It says that,
for every morphism of schemes `g : S' ⟶ S` and every presheaf
`F : (Over S)ᵒᵖ ⥤ Type v` satisfying the ten conditions `MurreConditions F` of
Murre's criterion, the base change `baseChange g F = (Over.map g).op ⋙ F`
satisfies them too. This is the remark at the start of Section 2 of Murre,
Bourbaki exp. 294 (printed p. 247). Murre does not prove it there.

## Proof

Split `MurreConditions F` into its ten parts and prove each one for
`baseChange g F` with a lemma from one of two modules:

- `MurreBaseChangeBasic` covers `SmallValues`, `ZariskiSheaf` (F1a),
  `FaithfullyFlatSheaf` (F1b), `AdicLimits` (F3), `ArtinianLifting` (F4′),
  `NilpotentInjective` (F5), `ValuativeSeparation` (F6),
  `OneDimensionalLifting` (F7) and `GenericNonLifting` (F8). Each condition for
  the base change follows from the same condition for `F`.
- `MurreBaseChangeColimits` covers `FilteredColimits` (F2). Here
  `BaseChange.filteredColimits` uses both (F1a) and (F2) for `F`. (F2) only
  speaks about affine opens `Spec R ⟶ S'`, but `Spec R ⟶ S' ⟶ S` need not be an
  open immersion. The (F1a) sheaf property is what extends (F2) to arbitrary
  morphisms `Spec R ⟶ S`.
