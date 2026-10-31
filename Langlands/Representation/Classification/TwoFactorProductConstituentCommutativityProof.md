# Proof of constituent commutativity for two irreducible GL factors

Author: Worker 763.

This module proves the irreducible two-factor case of Zelevinsky (1980),
Theorem 1.9. The target is the published proposition
`Langlands.Classification.TwoFactorProductConstituentCommutativity.{uF,uV} F T`
in `Representation/Classification/TwoFactorProductConstituentCommutativityStatement`.

The theorem `Langlands.Classification.twoFactorProductConstituentCommutativity`
has exactly the type
`Langlands.Classification.TwoFactorProductConstituentCommutativity.{uF,uV} F T`.
It binds only `p`, `Fact p.Prime`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`. Its universe parameters are `uF` and `uV`, the same as
the target, and its axioms are `propext`, `Classical.choice` and `Quot.sound`.
It has no other hypotheses.

It is assembled from two theorems.

- `Langlands.Classification.twoFactorProductConstituentCommutativity_of_finiteLength`,
  proved in this module, derives the target from the published proposition
  `Classification.IrreducibleProductFiniteLength.{uF,uV} F T` of
  `Representation/Classification/NormalizedProductFiniteLengthStatement`. That
  proposition says that a normalized product of irreducible smooth factors in
  positive rank has finite length. The argument uses it only to obtain a
  composition series of `π₂ × π₁`.
- The published `Langlands.Classification.irreducibleProductFiniteLength.{uF,uV} F T`
  of `Representation/Classification/IrreducibleProductFiniteLengthProof` proves
  that proposition with the same `F`, `T` and universes.

## Notation

Write `θ = GeneralLinear.inverseTranspose n F.Carrier`, the automorphism
`g ↦ (gᵗ)⁻¹` of `GL_n(F)`, and write `ρ ∘ θ` for the pullback of a
representation `ρ` along `θ`. For a smooth representation `ρ`, write `ρ~` for
its smooth contragredient `smoothContragredient ρ`. Put `π₁ = A 0`,
`π₂ = A 1`, `X = π₁ × π₂` for the actual normalized product over `B`, and
`Y = π₂ × π₁` for the actual normalized product over `B.reverse` of the factors
`A i.rev`. The topology on `F` is always `T.topology`.

## Implemented argument

The proof follows Zelevinsky's route, described under Source correspondence.
It does not use reflexivity of the smooth dual, and it does not take the smooth
dual of `X`. The steps below name the Lean declarations that carry them out.

1. **Reduction to `B.reverse`.** For a shape of length two,
   `adjacentSwap_zero_eq_revPerm` shows that `B.adjacentSwap 0 _` equals
   `Fin.revPerm`. After this substitution the right-hand product of the target
   is the product over `B.permute Fin.revPerm` of `A (Fin.revPerm i)`. That
   product is definitionally `Y`, the product over `B.reverse` of `A i.rev`;
   the proof uses `Representation.Equiv.refl` as the bridge. Lean is not asked
   to unify the two functor forms directly, since that unification does not
   finish in reasonable time. The rank satisfies `0 < n` because both blocks
   have positive size.

2. **Admissibility of the factors.** `isAdmissible_of_isIrreducible` shows that
   every irreducible smooth representation of `GL_m(F)` is admissible. It takes
   the admissibility part of the published `CuspidalSupport.cuspidalEmbedding`.

3. **Gelfand–Kazhdan for `T.topology`.** The published
   `gelfandKazhdanContragredient` gives `τ ∘ θ ≅ τ~` for an irreducible
   admissible `τ` of `GL_(k+1)(F)` in the canonical normed-field topology.
   `gelfandKazhdan_inverseTranspose` restates it for any positive rank `m` and
   the topology `T.topology`. It rewrites the topology with the published
   `PadicField.TopologicalData.topology_eq_canonicalNormTopology`.

4. **The pullback of `X` is the smooth dual of `Y`.** The isomorphism
   `E : X ∘ θ ≅ Y~` is the composite of three equivalences.
   - The published `Parabolic.normalizedProductInverseTranspose` gives
     `X ∘ θ ≅` the product over `B.reverse` of `A i.rev ∘ θ`. This is
     Zelevinsky's Lemma (a) with the plain inverse transpose; see the source
     note below.
   - Steps 2 and 3 give `A i.rev ∘ θ ≅ (A i.rev)~` blockwise.
     `T.normalizedProductInducedEquiv` induces these blockwise equivalences.
   - `productSmoothDual` identifies the product over `B.reverse` of the
     `(A i.rev)~` with `Y~`. It is the published
     `Parabolic.naturalNormalizedInductionDuality` applied to the external
     tensor product of the factors. The comparison of the smooth dual of a
     finite external tensor product with the tensor product of smooth duals is
     bijective by the published `FiniteTensor.smoothDualTensorInjectivity` and
     `FiniteTensor.smoothDualTensorMap_surjective`. The latter uses
     admissibility of the factors and cofinality of compact open subgroups.
     The tensor product of the factors is admissible by
     `FiniteTensor.isAdmissible_external`.

5. **A composition series of `Y`.** The hypothesis
   `IrreducibleProductFiniteLength` of the conditional theorem, applied to
   `B.reverse` and the factors `A i.rev`, says that `Y` has finite length as a module over the group
   algebra. Mathlib's `isFiniteLength_iff_exists_compositionSeries` and the
   published `LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
   turn this into an actual `ObjectRepFiltration` `t` of `Y` with simple
   graded pieces.

6. **`Y~` and `Y ∘ θ` have the same composition factors.** This is
   `haveSameJordanHolderFactors_dual_comp`, Zelevinsky's Lemma (b) for `Y`.
   - `annihilator S` is the invariant subspace of smooth functionals vanishing
     on `S`. `dualSeries t` is the series of annihilators of `t`, taken in
     reverse order. It is an `ObjectRepFiltration` of `Y~`.
   - `dualSeries_graded` identifies piece `j` of `dualSeries t` with the smooth
     dual of piece `j.rev` of `t`. Restricting a functional that vanishes on
     `S` to `T` gives a smooth functional on `T / S`
     (`annihilatorRestrict`). Its kernel is the annihilator of `T`, so the
     first isomorphism theorem `quotientRepEquiv` applies once the map is
     surjective. Surjectivity says that a smooth functional on `T / S` extends
     to a smooth functional on `Y`. It is the published exactness result
     `contragredientMap_surjective_of_injective_of_compact_cofinal` of
     `Smooth/Contragredient/ExactProof`, applied to the inclusion of `T`.
   - Each graded piece of `t` is irreducible and smooth, hence admissible by
     step 2. By step 3 its smooth dual is its pullback by `θ`. The published
     `ObjectRepFiltration.comp` and `compGradedEquiv` show that the pullback
     `t.comp θ` is a series of `Y ∘ θ` whose pieces are the pulled-back
     pieces of `t`. Irreducibility passes through pullback by the surjective
     `θ` (`CuspidalSupport.isIrreducible_comp_iff`) and through equivalences
     (`isIrreducible_iff_of_equiv`).
   - The two series have the same length and are matched by `Fin.revPerm`.

7. **Conclusion.** Transport along `E` (published
   `haveSameJordanHolderFactors_transport`) turns step 6 into
   `X ∘ θ` and `Y ∘ θ` having the same composition factors.
   `haveSameJordanHolderFactors_of_comp` removes the pullback. It pulls both
   series back once more along `θ⁻¹` (`haveSameJordanHolderFactors_comp`) and
   identifies `(ρ ∘ θ) ∘ θ⁻¹` with `ρ` (`compSymmEquiv`). The result is
   `X` and `Y` having the same composition factors. Step 1 identifies `Y` with
   the target's right-hand product.

8. **Discharging the hypothesis.** `twoFactorProductConstituentCommutativity`
   applies the conditional theorem to the published
   `irreducibleProductFiniteLength F T`.

Matching composition factors includes finite length of `X`. The proof does
not apply the finite-length hypothesis to `X`; it obtains a composition series
of `X` by pulling back the annihilator series of `Y~` along `E` and then `θ⁻¹`.

## Helper declarations

The helpers live in `Langlands.Classification.TwoFactorCommutativity`. The
first group is generic: `quotientRepEquiv`, `annihilator`, `mem_annihilator`,
`annihilator_antitone`, `annihilator_bot`, `annihilator_top`,
`subrepInclusion`, `quotientProjection`, `isSmooth_toRepresentation`,
`isSmooth_quotientRep`, `annihilatorRestrict`, `annihilatorRestrict_apply_mk`,
`annihilatorRestrict_eq_zero_iff`, `annihilatorRestrict_surjective`,
`annihilatorQuotientEquiv`, `dualSeries`, `dualSeries_graded`, `equivComp`,
`compSymmEquiv`, `haveSameJordanHolderFactors_comp` and
`haveSameJordanHolderFactors_of_comp`. They work for an arbitrary topological
group or monoid, with independent carrier universes.

The second group is specific to `GL_n(F)`: `canonicalTopology`,
`gelfandKazhdan_inverseTranspose` (with the private
`gelfandKazhdanOfTopology`), `isAdmissible_of_isIrreducible`,
`productSmoothDual` and `haveSameJordanHolderFactors_dual_comp`.
`Langlands.Classification.adjacentSwap_zero_eq_revPerm` is the shape identity
of step 1.

`HaveSameJordanHolderFactors` compares graded quotients with algebraic
`Representation.IsIrreducible`. The quotient `gradedRepresentation` of a
filtration is definitionally the `quotientRep` of `LengthCriterionProof`,
which the helpers use.

## Source correspondence

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210. Source `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Theorem 1.9
and its proof are on printed p.174 (PDF p.11).

Zelevinsky uses the automorphism `s(g) = s_n (gᵗ)⁻¹ s_n⁻¹` and two lemmas:
(a) `s(π₁ × π₂) ≅ s(π₂) × s(π₁)`, and (b) for finite-length `π`,
`JH⁰(s(π)) = JH⁰(π~)`, which for irreducible `π` is the Gelfand–Kazhdan
theorem. His chain is

```text
JH⁰(π₁ × π₂) = JH⁰((s(π₁ × π₂))~) = JH⁰((s(π₂) × s(π₁))~)
             = JH⁰((s(π₂))~ × (s(π₁))~) = JH⁰(π₂ × π₁),
```

using (b), (a), §1.1(d) (normalized induction commutes with smooth duals) and
(b) again.

The Lean proof uses the same ingredients in a different order.

- Lemma (a) is the published `normalizedProductInverseTranspose` with
  `θ(g) = (gᵗ)⁻¹`. Zelevinsky's conjugation by `s_n` is an inner automorphism
  and does not change isomorphism classes, so it is omitted.
- §1.1(d) for this product is `productSmoothDual`.
- Lemma (b) is used for the irreducible factors `π₁`, `π₂` (step 4) and for
  the graded pieces of a composition series of `Y` (step 6). It is never
  applied to `X` or to `Y` as a whole. Zelevinsky's two uses of (b) become
  step 6 for `Y` plus one pullback along `θ⁻¹` (step 7).
- The proof computes `X ∘ θ ≅ Y~` and does not dualize `X`. It therefore needs
  no reflexivity of the smooth dual and no finite length of `X~`.

Finite length of the products is Zelevinsky's Proposition 1.4, printed p.171
(PDF p.8). Here it is the published `irreducibleProductFiniteLength`, which
embeds the product into a product of supercuspidal inductions and uses finite
length of cuspidal induction.
Admissibility of irreducible representations is his §1.5 (printed p.171),
citing Bernstein–Zelevinsky (1977), 2.5. Here it comes from the published
`cuspidalEmbedding`. The Gelfand–Kazhdan theorem is his reference [8] and
Bernstein–Zelevinsky (1976), 7.3. Here it is the published
`gelfandKazhdanContragredient`.

The cited passages were read in the retained original, and its hash was
checked.

## Imports and independence

The direct imports are the target statement,
`Classification.NormalizedProductFiniteLengthStatement`,
`Classification.IrreducibleProductFiniteLengthProof`,
`Classification.SupercuspidalContragredientAux`,
`CuspidalSupport.AssociationReduction`, `CuspidalSupport.CuspidalEmbeddingProof`,
`Category.Contragredient`, `Smooth.Contragredient.ExactProof`,
`Smooth.Contragredient.GelfandKazhdanProof`, `Filtration.LengthCriterionProof`,
`Filtration.JordanHolderComparisonProof`, `Filtration.JordanHolderTransportProof`,
`Filtration.ObjectTransport`, `Induction.BlockEquivalence`,
`Induction.Equivalences`, `Parabolic.InverseTransposeProductProof`,
`Parabolic.NaturalInductionDualityProof`, `Tensor.SmoothDualInjectivityProof`,
`Tensor.SmoothDualSurjectivityProof` and `LocalField.Normalization.Proof`
(all under `Langlands.Representation` except the last, which is under
`Langlands`).

The recursive project import closure has 554 Library modules besides this
one. Most of them enter through `IrreducibleProductFiniteLengthProof`: the
cuspidal-support, Jacquet-module, geometric-lemma, parabolic and Hecke-algebra
modules behind cuspidal embedding and finite length of cuspidal induction.

It contains no segment, multisegment, socle, gluing, tempered,
square-integrable, regular, analytic or segment-exhaustion results. Its
`Classification` modules are the target statement,
`NormalizedProductFiniteLengthStatement`, `IrreducibleProductFiniteLengthProof`,
`IrreducibleProductEmbedding` and its statement, `Supercuspidal`,
`SupercuspidalSupport`, `SupercuspidalTwist`,
`SupercuspidalContragredientStatement`, `SupercuspidalContragredientAux`,
`ConstituentRelations` and `Segments`. `ConstituentRelations` only defines
the relations of irreducible quotient, subrepresentation, head and socle.
`Segments` supplies segment definitions and transport lemmas for irreducible
quotients, heads and socles. It enters through `SupercuspidalSupport` and
contains no classification conclusion. Other modules in the closure that
mention "exhaustion" concern compact-open exhaustions of groups and compact
isotypic parts, not exhaustion of irreducible representations.

The closure contains none of the tasks excluded by the target statement's
Independence section, nor their proof successors. It contains no
finite-length form of Theorem 1.9 and no adjacent block-swap result.


The generic `equivComp`, `haveSameJordanHolderFactors_comp` and
`haveSameJordanHolderFactors_of_comp` interfaces reuse the existing finite-tensor
pullback helpers, now shared in
[`FactorMatchingPullback`](../Filtration/FactorMatchingPullback.md). Their
declaration types are unchanged. The helper module imports only the published
Jordan–Hölder transport and cuspidal-support association infrastructure.
