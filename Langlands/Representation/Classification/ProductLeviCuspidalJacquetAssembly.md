# Assembly of the product-Levi opposite cuspidal Jacquet counts

Module `Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly`.
The helpers live in namespace `Langlands.ProductLeviCuspidalJacquetAssembly`. The
conditional main theorem is `Langlands.productLeviCuspidalJacquetMultiplicity_of_upstream`.

## Purpose and provenance

This is an internal helper for the product-Levi cuspidal Jacquet multiplicity
theorem `Langlands.ProductLeviCuspidalJacquetMultiplicityStatement` (module
`Classification/ProductLeviCuspidalJacquetMultiplicityStatement`). That statement
is a derived product-Levi specialization of Silberger 1979, Theorem 5.4.1.1, and
BZ77, Corollary 2.13(c) and §2.15(3). Here it is assembled from three upstream
statements of the Library, which appear as **hypotheses**:

* `Parabolic.RefinedInductionTensorTheorem` (`Parabolic/RefinedInductionTensorStatement`):
  normalized refined induction of an external tensor product of factors is the
  external tensor product of the blockwise normalized inductions;
* `AssociatedJacquetFiltrationTheorem F T n` for every `p`-adic field and every
  `0 < n` (`CuspidalSupport/JacquetInductionStatement`): the general-linear
  geometric-lemma filtration of the upper Jacquet module of a parabolic induction;
* `GLOppositeCuspidalJacquetFiltrationFromUpperStatement`
  (`Classification/OppositeCuspidalJacquetFiltrationStatement`): the matching
  filtration of the general-linear opposite Jacquet module.

This module proves no literature statement unconditionally. It proves that the
three hypotheses imply the target statement. The final proof of the target only
has to apply this theorem to the published proofs of the three statements. The
remaining ingredients are published Library results:

* the cuspidal factorization `CuspidalSupport.padicLeviCuspidalFactorization`, the
  regrouping `FiniteTensor.flattenedTensorRegroupEquiv`, and
  `CuspidalSupport.glCuspidalTensor`;
* the refined opposite Jacquet tensor comparison
  `RefinedOppositeJacquetTensor.oppositeJacquetEquiv` and
  `normalizedRefinedOppositeJacquetCongr` (`Parabolic/RefinedOppositeJacquetTensor`);
* the finite external tensor filtration `FiniteTensorFiltration.exists_external`
  and the equivalence constructors `compCongr`, `compSymmComp`, `externalCongr`
  (`Tensor/ProductFiltration`);
* the pullback and transport of filtrations `ObjectRepFiltration.comp`,
  `compGradedEquiv`, `equivTransportGradedEquiv` (`Filtration/ObjectTransport`) and
  `LengthTwo.transport`;
* the block-diagonal assembly of minimal self-conjugating permutations
  `ProductLeviMinimalIndex.assemble`/`assembleEquiv` and the conjugation
  compatibility `flattenedLeviProductEquiv_leviConjugation_symm`
  (`Classification/ProductLeviMinimalIndex`);
* the counting theorem `finiteFamilyFiltrationMultiplicity`
  (`Filtration/FiniteFamilyMultiplicityProof`).

All comparisons are actual `Representation.Equiv`s.

## Declarations

Throughout, `T : F.TopologicalData` for a `p`-adic field `F`, `B : BlockShape n`,
`S : BlockRefinement B` and `C = B.flatten S`. The topology `T.topology` is used on
`F.Carrier`.

* `normalizedRefinedInducedCongr T B S E`: an equivalence `E : σ.Equiv τ` of
  representations of the refined Levi induces an equivalence of
  `T.normalizedRefinedInduced B S σ` with `T.normalizedRefinedInduced B S τ`. Its
  two directions are the published `normalizedRefinedInducedMap` of `E` and of
  `E.symm`. They are inverse pointwise on functions.

* `supercuspidalProperty_cast T h X`: for an equality of ranks `h : a = b` and a
  supercuspidal representation `X` of `GL a`, the smooth representation
  `h ▸ X.obj` of `GL b` still satisfies `supercuspidalProperty`. Proof: `subst h`.

* `exists_factors T B S hn σ hσ hc`: assume `0 < n`, `σ` is a representation of
  `C.Levi F.Carrier` on a complex vector space `V` in universe `uV`,
  `hσ : σ.IsIrreducible` and `hc : IsLeviCuspidal C σ`. Then there are factors
  `A : Parabolic.RefinedInductionTensor.Factors F T B S`, one smooth
  representation `A i` of `(S i).Levi F.Carrier` for each coarse block `i`. Every
  `A i` is irreducible and Levi-cuspidal for `S i`, and there is an equivalence

  ```
  σ ≃ (FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom
  ```

  Proof. `IsLeviCuspidal` contains admissibility, so `σ` is a smooth object.
  `padicLeviCuspidalFactorization` writes `σ` as `C.blockTensor` of supercuspidal
  representations `X k`. Each `X (flattenBlockEquiv ⟨i, j⟩)` is transported to rank
  `(S i).size j` along `flatten_size_flattenBlockEquiv`, giving `Y i j`. Put
  `A i := FiniteTensor.externalSmoothObject (fun j => (Y i j).obj)`.
  `glCuspidalTensor` (rank `B.size i`, positive by `B.positive i`) gives
  irreducibility and Levi-cuspidality. The equivalence composes the factorization
  with `flattenedTensorRegroupEquiv`.

* `flattenedLeviProductEquiv_flattenedLeviEquiv_symm`: for `m` in the refined Levi,
  `flattenedLeviProductEquiv ((flattenedLeviEquiv).symm m) = (refinedLeviEquiv).symm m`.
  This holds because `flattenedLeviEquiv` is by definition the composite of
  `flattenedLeviProductEquiv` and `refinedLeviEquiv`.

* `inducingEquiv T B S E`: from an equivalence `E` as in `exists_factors`, an
  equivalence of `σ.comp (flattenedLeviEquiv F.Carrier B S).symm` with
  `Parabolic.RefinedInductionTensor.inducingRepresentation F T B S A`. It has the
  same linear map as `E`. The intertwining identity at `m` is that of `E` at
  `(flattenedLeviEquiv).symm m`, by the previous lemma.

* `external_transport`: for minimal self-conjugating permutations `v i` of the
  inner Levis, the external tensor product of the transports
  `transport (S i) (S i) (v i) (A i).representation` at `y` is the external tensor
  product of the `A i` at `fun i => (leviConjugation (S i) (S i) (v i)).symm (y i)`.
  Both sides agree on pure tensors.

* `gradedEquiv T B S E v`: for `E` as above and `v` as above, an equivalence from

  ```
  (FiniteTensor.external fun i => transport (S i) (S i) (v i) (A i).representation).comp
    (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom
  ```

  to `(transport C C w σ).comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`.
  Here `w = ProductLeviMinimalIndex.assemble B S v` is the block-diagonal
  permutation `blockPermOf B v`. The linear map is `E.symm`. The intertwining
  identity is that of `E.symm` at `(leviConjugation C C w).symm ((flattenedLeviEquiv).symm m)`.
  It is rewritten with `external_transport` and with
  `ProductLeviMinimalIndex.flattenedLeviProductEquiv_leviConjugation_symm`. The
  latter says that `flattenedLeviProductEquiv` turns the inverse conjugation by
  `w` into the blockwise inverse conjugations by the `v i`.

* `nonempty_comp_equiv_iff ρ τ φ`: for a group isomorphism `φ : H ≃* G`, the
  pullbacks `ρ.comp φ` and `τ.comp φ` are equivalent exactly when `ρ` and `τ` are.
  The forward direction pulls back once more along `φ.symm` (`compCongr`) and
  cancels with `compSymmComp`.

### Main result

`productLeviCuspidalJacquetMultiplicity_of_upstream hRIT hAJF hOpp` proves
`ProductLeviCuspidalJacquetMultiplicityStatement.{uF, uV, uW}` from

* `hRIT : Parabolic.RefinedInductionTensorTheorem.{uF, uV}`,
* `hAJF : ∀ p [Fact p.Prime] (F : PadicField.{uF} p) T n, 0 < n → AssociatedJacquetFiltrationTheorem.{uF, uV} F T n`,
* `hOpp : GLOppositeCuspidalJacquetFiltrationFromUpperStatement.{uF, uV}`.

Proof. Fix `σ` irreducible and Levi-cuspidal on `C.Levi`. Let `e = flattenedLeviEquiv F.Carrier B S`.
The target's `I` is the normalized refined induction of `σ.comp e.symm`, and `J`
is the normalized refined opposite Jacquet module of `I`.

1. `exists_factors` gives factors `A i` and an equivalence `E`. `hRIT` gives an
   equivalence of the normalized refined induction of `inducingRepresentation A`
   with the external tensor product of the blockwise normalized inductions
   `Ai i := CuspidalJacquetMultiplicity.induced T (S i) (A i)`. Composing it with
   `normalizedRefinedInducedCongr` of `inducingEquiv E` gives `X : I ≃ ⨂ Ai i`.
2. `normalizedRefinedOppositeJacquetCongr X` followed by `oppositeJacquetEquiv`
   gives `K : J ≃ (⨂ Jo i).comp (refinedLeviEquiv).symm`. Here
   `Jo i := CuspidalJacquetMultiplicity.oppositeJacquet T (S i) (Ai i)` is the
   general-linear opposite Jacquet module of block `i`.
3. For each `i`, `hOpp` (with `hAJF` at rank `B.size i` and `LevisAssociated.refl (S i)`)
   gives a filtration `s i` of `Jo i`. It has length `r i` and is indexed by
   `eI i : Fin (r i) ≃ MinimalConjugatingPermutations (S i) (S i)`. The graded piece
   at `j` is equivalent to `transport (S i) (S i) (eI i j) (A i)`. The quasicuspidality
   hypothesis comes from the Levi-cuspidality of `A i`.
4. `FiniteTensorFiltration.exists_external` gives a filtration `f` of `⨂ Jo i`
   of some length `N`, with an index equivalence `Eidx : Fin N ≃ ∀ i, Fin (r i)`.
   Its graded pieces are equivalent to the external tensor products of the graded
   pieces of the `s i`. Pulling `f` back along `(refinedLeviEquiv).symm` and
   transporting it along `K.symm` gives a filtration `sJ` of `J`.
5. Index the family by `CoarseMinimalPermutations B S`, the minimal
   self-conjugating permutations `w` of `C` lying in `blockWeyl B`. Put
   `family w := Rep.of ((transport C C w σ).comp e.symm)`. Each member is
   irreducible (`JacquetLength.isIrreducible_transport` and
   `JacquetLength.isIrreducible_comp`). The index equivalence is
   `idx := Eidx` followed by `Equiv.piCongrRight eI` and `assembleEquiv B S`.
6. The graded piece of `sJ` at `j` is equivalent to `family (idx j)`. The chain
   of equivalences is: `equivTransportGradedEquiv` (inverse), `compGradedEquiv`,
   the pullback of the `exists_external` equivalence, the pullback of the external
   tensor product of the equivalences from step 3, and finally `gradedEquiv E`.
7. `finiteFamilyFiltrationMultiplicity` gives the length `Nat.card (CoarseMinimalPermutations B S)`,
   which is the first claim. For an irreducible `τ` on `C.Levi`, it also says that
   the multiplicity of `Rep.of (τ.comp e.symm)` in `J` is the number of `w` with
   `family w` equivalent to `τ.comp e.symm`. By `nonempty_comp_equiv_iff` these are
   the `w` with `transport C C w σ` equivalent to `τ`. Regrouping the two subtype
   conditions (`Nat.card_congr`) gives the number of associating permutations of
   `σ` and `τ` lying in `blockWeyl B`. This is the second claim.
