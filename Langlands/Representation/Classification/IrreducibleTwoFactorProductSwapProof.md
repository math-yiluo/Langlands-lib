# Proof: swapping the factors of an irreducible equal-rank product

Author: Worker 1023.

This module proves

```lean
theorem Langlands.Classification.irreducibleTwoFactorProductSwap :
    IrreducibleTwoFactorProductSwap.{uF, uV} F T
```

for every prime `p`, every `F : PadicField.{uF} p` and every
`T : F.TopologicalData`, with independent universes `uF, uV` and no further
hypotheses. The proposition is the published statement in
`Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement`.
Under `T.topology`, for `k > 0` and irreducible smooth representations `α, β`
of `GL_k(F)`, if the upper normalized product
`X = α × β = (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj (twoBlockFactors hk hk α β)`
is irreducible, then `X` is isomorphic, as a smooth representation of
`GL_{2k}(F)`, to `Y = β × α` (the same functor applied to
`twoBlockFactors hk hk β α`).

## Mathematical source

The statement is the irreducible equal-rank case of Zelevinsky 1980,
Theorem 1.9, printed p.174 (PDF p.11) (literature
`zelevinsky-1980-induced-ii`). Zelevinsky proves that `π₁ × π₂` and `π₂ × π₁`
have the same composition factors, using the Gelfand–Kazhdan involution. The
Lean proof uses the same involution `θ(g) = ᵗg⁻¹`. It does not use
composition factors, and it never dualizes twice.

## Implemented proof

Write `θ` for `GeneralLinear.inverseTranspose` and `Z ∘ θ` for the pullback of a
smooth representation `Z` along `θ` on the same carrier. In the module this
pullback is the private abbreviation `itPullback F T Z`. It is smooth by
`isSmooth_comp`, because inverse transpose is continuous
(`GeneralLinear.continuous_inverseTranspose`). All topologies on `F` and on
the groups `GL_r(F)` are the ones selected by `T`
(`T.topology`, `T.generalLinearTopologicalGroup r`).

Private helpers:

- `itPullbackIso`: an isomorphism `Z ≅ Z'` gives `Z ∘ θ ≅ Z' ∘ θ`, with the
  same linear map.
- `itPullbackTwiceIso`: `(Z ∘ θ) ∘ θ ≅ Z` through the identity map, because
  `θ` is an involution (`GeneralLinear.inverseTranspose_involutive`).
- `gelfandKazhdanEquiv`, `gelfandKazhdanIso`: for `N > 0`, an irreducible
  admissible representation `Z` of `GL_N(F)` satisfies `Z ∘ θ ≅ Z^∨`, where
  `Z^∨` is the smooth contragredient (`SmoothRep.contragredient`). The
  published `Langlands.gelfandKazhdanContragredient` (module
  `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`) is
  stated for `GL_{n+1}` under the topology of `F.canonicalNormedField`. The
  helper writes `N = n + 1` and generalizes over a topology `t` on `F` equal to
  the canonical one. It applies the theorem after `subst`, and then
  instantiates `t := T.topology` using
  `PadicField.TopologicalData.topology_eq_canonicalNormTopology`. The group
  topology instance on `GL_{n+1}(F)` is left as an arbitrary instance argument,
  so no comparison of group topologies is needed.
- `productSmoothDualEquiv`: for a block shape `B` and admissible blocks `A i`,
  the smooth dual of the normalized product of the `A i` is equivalent to the
  normalized product of the smooth duals `(A i)^∨`. This composes the natural
  normalized induction duality
  `Langlands.Parabolic.naturalNormalizedInductionDuality` (the dual of the
  normalized induction of an admissible Levi representation `σ` is the
  normalized induction of `σ^∨`) with the external tensor comparison.
  `FiniteTensor.smoothDualTensorMap` is bijective, by
  `FiniteTensor.smoothDualTensorInjectivity` and
  `FiniteTensor.smoothDualTensorMap_surjective`, the latter using admissibility
  and cofinal compact open subgroups (`GeneralLinear.compactOpen_cofinal`).
  This bijection gives the equivalence on the Levi
  representation, which is transported through
  `T.normalizedParabolicInducedEquiv`. Admissibility of the Levi tensor product
  is `FiniteTensor.isAdmissible_external`.
- `itPullbackProductIso`: for `n > 0`, a block shape `B` of `n` and blocks
  `A i`,
  `((T.normalizedProductInductionFunctor B).obj A) ∘ θ ≅ (T.normalizedProductInductionFunctor B.reverse).obj (fun i => A i.rev ∘ θ)`.
  This is the published `Langlands.Parabolic.normalizedProductInverseTranspose`
  (module `Langlands.Representation.Parabolic.InverseTransposeProductProof`),
  restated for bundled smooth representations. The equivalence is given an
  explicit type with the block family `fun i => (A i.rev ∘ θ).representation`,
  and both endpoints of `SmoothRep.mkIso` are named explicitly. Without them
  the definitional unfolding times out.
- `productFunctor_obj_congr`: equal block shapes with heterogeneously equal
  block families give isomorphic products (by `subst`).
- `twoBlocks_reverse`: `(Shahidi.twoBlocks k k hk hk).reverse = Shahidi.twoBlocks k k hk hk`.
  Both block sizes are `k`, so reversing changes nothing. This is checked
  entry by entry on `Fin 2`.

Main theorem. Let `B = Shahidi.twoBlocks k k hk hk`, so `X = B(α, β)` and
`Y = B(β, α)`.

1. Admissibility. `α`, `β` and `X` are irreducible, so they are admissible by
   the first conjunct of `Langlands.CuspidalSupport.cuspidalEmbedding`
   (ranks `k` and `k + k`).
2. `Y ∘ θ` is isomorphic to the product over `B.reverse` of the family
   `i ↦ fba(i.rev) ∘ θ`, where `fba = twoBlockFactors hk hk β α`. Its first
   block is `α ∘ θ` and its second is `β ∘ θ`
   (`itPullbackProductIso` with `n = k + k > 0`).
3. That product is isomorphic to `B(α ∘ θ, β ∘ θ)`: the reversed shape is `B`
   (`twoBlocks_reverse`), and the reversed family is heterogeneously equal to
   `(α ∘ θ, β ∘ θ)` (checked on both indices of `Fin 2`), so
   `productFunctor_obj_congr` applies.
4. `B(α ∘ θ, β ∘ θ) ≅ B(α^∨, β^∨)`: Gelfand–Kazhdan on each block
   (`gelfandKazhdanIso` for `α` and `β`), mapped through the functor
   `T.normalizedProductInductionFunctor B` with `Pi.isoMk`.
5. `B(α^∨, β^∨) ≅ X^∨` by `productSmoothDualEquiv` (inverted).
6. `X ∘ θ ≅ X^∨`: Gelfand–Kazhdan for the irreducible admissible `X`
   (rank `k + k > 0`).
7. Composing 2–5 with the inverse of 6 gives `Y ∘ θ ≅ X ∘ θ`. Then
   `X ≅ (X ∘ θ) ∘ θ ≅ (Y ∘ θ) ∘ θ ≅ Y`, by `itPullbackTwiceIso` and
   `itPullbackIso`.

The proof uses the irreducibility of `X` only in step 6 and to get the
admissibility of `X` in step 1. Irreducibility of `α, β` is used for their
admissibility and in step 4.

## Lean details

- The module sets `linter.style.haveILetI false`, because the proofs of
  propositions use `letI` to install `T.topology` and the group topologies,
  as the statement does.
- `itPullback` is an `abbrev`, so its representation unfolds reducibly to
  `Z.representation.comp θ.toMonoidHom`. This is needed for step 2.
- No `sorry`, `admit`, new axioms or theorem-valued hypotheses occur.
  All helpers are private to this module.

## Independence audit

Imports of this module: the statement module
`Classification.IrreducibleTwoFactorProductSwapStatement`,
`Smooth.Contragredient.GelfandKazhdanProof`,
`Parabolic.InverseTransposeProductProof`,
`Parabolic.NaturalInductionDualityProof`,
`Tensor.SmoothDualInjectivityProof`, `Tensor.SmoothDualSurjectivityProof`,
`Tensor.FiniteProperties`, `Induction.BlockEquivalence`,
`Induction.Equivalences`, `CuspidalSupport.CuspidalEmbeddingProof`,
`Category.Contragredient` (all under `Langlands.Representation`) and
`Langlands.LocalField.Normalization.Proof`.

The transitive closure of these imports in the Library (commit `64f062d4`)
has 276 `Langlands` modules besides this one. I checked every module in it.
None declares or mentions any of the following:

- `SegmentSpecialEssentialSquareIntegrability`
- `SquareIntegrableLanglandsClassification`
- `GenericSegmentProductUniqueness`
- `OrderedMultisegmentSocleExistence`
- `MultisegmentSocleExhaustion`
- `SegmentSocleProductIrreducibility`
- `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
  `SegmentSocleJacquetFormula`
- `SegmentSpecialJacquetExponentNormFormula`
- `TwoSupercuspidalAdjacentProductReducible`

No module in the closure contains `StrongHead`, `QuotientCoverage`,
`OrderedConversion`, `TemperedUniqueness`, `SquareIntegrab` or `Derivative`.
The word `Exhaustion` occurs only in
`Parabolic.GeometricPrerequisitesStatement` (`UnipotentExhaustionClause`, a
nested compact open exhaustion of a unipotent radical). Judging by these names
and by module names, no module in the
closure belongs to any of the tasks on the contract's list:

- special-head/reverse-socle existence and segment-socle/reverse-head
  existence;
- analytic segment classification and forward special square-integrability;
- multisegment special-head exhaustion, ordered strong-head existence,
  quotient coverage and ordered conversion;
- tempered uniqueness, the square-integrable Langlands classification,
  square-integrable exhaustion and regular exhaustion;
- special-head product irreducibility and adjacent socle commutation;
- the segment Jacquet formulas;
- adjacent reducibility.

The only `Classification` modules in the closure are the statement module
itself, `TwoSupercuspidalProductStructureStatement` (the definitions of
`twoBlockFactors` used by the statement), `Segments` (definitions of segments,
linkedness and transport lemmas for heads and socles along equivalences),
`ConstituentRelations`, and the supercuspidal definition and contragredient
modules `Supercuspidal`, `SupercuspidalSupport`, `SupercuspidalTwist`,
`SupercuspidalContragredientStatement` and `SupercuspidalContragredientAux`.
None of them proves any of the results above.

Mathematical dependencies:

- Gelfand–Kazhdan (`Langlands.gelfandKazhdanContragredient`)
- inverse-transpose reversal of normalized products
  (`Langlands.Parabolic.normalizedProductInverseTranspose`)
- natural normalized induction duality
  (`Langlands.Parabolic.naturalNormalizedInductionDuality`)
- the smooth dual of a finite external tensor product of admissible
  representations
- admissibility of irreducible representations
  (`Langlands.CuspidalSupport.cuspidalEmbedding`, built on Jacquet-module
  theory and quasicuspidal embeddings)

None of these is a derivative formula (Ze80 §3.5, §9.6, BZ77), a segment
product irreducibility criterion (Ze80 4.2, 9.7), an analytic or
square-integrability result (Ze80 9.3), or a classification or exhaustion
theorem. The proof does not use the adjacent reducibility task
`0988a3e0-a086-474d-b2d2-7e53902b43cb` or its target.
