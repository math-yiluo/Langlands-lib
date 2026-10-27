# Refined opposite Jacquet modules of finite external tensor products

Module `Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor`,
namespace `Langlands.RefinedOppositeJacquetTensor`.

## Purpose and provenance

This is an internal helper for the product-Levi cuspidal Jacquet multiplicity
theorem (`Langlands.ProductLeviCuspidalJacquetMultiplicityStatement`). That
theorem is about the normalized refined opposite Jacquet module
`T.normalizedRefinedOppositeJacquet B S` of a representation of the coarse Levi
`B.Levi F.Carrier`, which is literally the product `∀ i, GL (B.size i)`. The
intended proof works one coarse block at a time. It needs to know that this
functor, applied to an external tensor product of representations of the blocks
`GL (B.size i)`, is the external tensor product of the general-linear opposite
Jacquet modules `CuspidalJacquetMultiplicity.oppositeJacquet T (S i)` of the
factors. This module proves that comparison.

The mathematics is standard: coinvariants of an external tensor product by a
product subgroup are the tensor product of the factor coinvariants, and the
modulus character of a product parabolic is the product of the factor moduli. No
statement of the literature is formalized here; the content is internal. The
proof uses only published Library results: the character-localized comparison
`FiniteTensor.characterLocalizationEquiv` of `Tensor/CharacterLocalization`
(used with trivial characters), the definitions of
`Parabolic/OppositeRefinementFunctors` and `Geometric/RefinementDefinitions`, and
the general-linear opposite Jacquet module of
`Classification/CuspidalJacquetMultiplicityStatement`.

All comparisons are actual linear equivalences or actual
`Representation.Equiv`s. No smoothness, admissibility or irreducibility is
assumed.

## Declarations

### Untwisted coinvariants (section `Coinvariants`)

Here `R` is a commutative ring, `ι` a finite index type, `H i` groups, `V i`
`R`-modules, `ρ i : Representation R (H i) (V i)` and `U i : Subgroup (H i)`.

* `productCharacter_one U`: the product character
  `FiniteTensor.productCharacter U (fun _ => 1)` of trivial characters is trivial.
* `coinvariantsEquiv ρ U` is a linear equivalence from
  `Jacquet.Coinvariants (FiniteTensor.external ρ) (Subgroup.pi Set.univ U)` to
  `PiTensorProduct R (fun i => Jacquet.Coinvariants (ρ i) (U i))`. It is the
  composite of three linear equivalences. The first identifies the untwisted
  relations with the relations of the trivial product character
  (`productCharacter_one` and `Jacquet.Localization.relations_one`). The second is
  `FiniteTensor.characterLocalizationEquiv ρ U (fun _ => 1)`. The third identifies
  each factor's trivial-character relations with its untwisted relations.
* `coinvariantsEquiv_mk_tprod`: it sends the class of `tprod v` to
  `tprod (fun i => Jacquet.mk (ρ i) (U i) (v i))`. Proof: unfold the composite
  and apply `characterLocalizationEquiv_mk_tprod` and `PiTensorProduct.congr_tprod`.

### The refined opposite Jacquet module (section `Opposite`)

Here `T : F.TopologicalData` for a `p`-adic field `F`, `B : BlockShape n`,
`S : BlockRefinement B`, and `A i : Rep ℂ (GeneralLinear (B.size i) F.Carrier)`
for each coarse block `i`.

* The imported `PadicField.TopologicalData.oppositeJacquetMk T C A` from
  [OppositeJacquetMap](OppositeJacquetMap.md) is the quotient map
  `Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier)`, typed with the carrier
  of `CuspidalJacquetMultiplicity.oppositeJacquet T C A` as target.
* `oppositeJacquet_mk`: for `x : C.Levi F.Carrier`, the action of `x` on the
  general-linear opposite Jacquet module sends `oppositeJacquetMk T C A w` to
  `√(T.leviModulus C x) • oppositeJacquetMk T C A (A.ρ (C.leviEmbedding x) w)`.
  The scalar is the positive square root of the upper modulus, coerced to `ℂ`. It
  comes from `Jacquet.normalizedActionOfModulus_mk` applied to the inverse
  character `δ⁻¹` used in the definition.
* `normalizedRefinedOppositeJacquetCongr T B S e`: an equivalence
  `e : ρ.Equiv τ` of representations of `B.Levi F.Carrier` descends to an
  equivalence of `T.normalizedRefinedOppositeJacquet B S ρ` with
  `T.normalizedRefinedOppositeJacquet B S τ`. The two directions are the
  published `normalizedRefinedOppositeJacquetMap` of `e` and of `e.symm`. They are
  inverse because every quotient class has a representative
  (`refinedOppositeJacquetMk_surjective`). The lemma
  `normalizedRefinedOppositeJacquetCongr_mk` says that it sends the class of `v`
  to the class of `e v`.
* `refinedLeviHalfModulus_eq_prod`: for `m` in the refined Levi,
  `T.refinedLeviHalfModulus B S m` (as a complex number) is the product over the
  coarse blocks `i` of `√(T.leviModulus (S i) (refinedLeviBlock B S i m))`. The
  proof unfolds the product modulus `refinedLeviModulus` and uses that the
  square root on `ℝ≥0` is multiplicative (`NNReal.sqrtHom`).
* `refinedCoinvariantsEquiv T B S A` is `coinvariantsEquiv` for the family
  `(A i).ρ` and the subgroups `(S i).oppositeUnipotentSubgroup F.Carrier`. Its
  source is `RefinedOppositeJacquetModule B S (FiniteTensor.external fun i => (A i).ρ)`,
  because the refined opposite unipotent subgroup is by definition the subgroup
  product of these factor subgroups. Its target is
  `PiTensorProduct ℂ (fun i => oppositeJacquet T (S i) (A i))`.
  `refinedCoinvariantsEquiv_mk_tprod` is the formula on `tprod v`, written with
  `oppositeJacquetMk`.
* `leviEmbedding_refinedLeviEquiv_symm`: for `m` in the refined Levi, the `i`-th
  block coordinate `(refinedLeviEquiv B S).symm m i` embeds back by
  `(S i).leviEmbedding` to the actual `i`-th block `m.val i`.
* `refinedCoinvariantsEquiv_comm`: on the class of `tprod v`,
  `refinedCoinvariantsEquiv` intertwines the action of `m` on the normalized refined
  opposite Jacquet module with the action of `(refinedLeviEquiv B S).symm m` on
  the external tensor product of the factor opposite Jacquet modules. Proof: on
  the left, `normalizedRefinedOppositeJacquet_mk` gives the scalar
  `T.refinedLeviHalfModulus B S m` times the class of `tprod (fun i => (A i).ρ (m.val i) (v i))`.
  On the right, `FiniteTensor.external_tprod` and `oppositeJacquet_mk` give a
  `tprod` of scalar multiples. Pull the scalars out with
  `MultilinearMap.map_smul_univ`. Then `refinedLeviHalfModulus_eq_prod` and
  `leviEmbedding_refinedLeviEquiv_symm` match the two sides.

### Main result

`oppositeJacquetEquiv T B S A` is an actual `Representation.Equiv` from

```
T.normalizedRefinedOppositeJacquet B S (FiniteTensor.external fun i => (A i).ρ)
```

to

```
(FiniteTensor.external fun i => (oppositeJacquet T (S i) (A i)).ρ).comp
  (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom
```

on the linear equivalence `refinedCoinvariantsEquiv T B S A`. In words: the
normalized refined opposite Jacquet module of the external tensor product of the
`A i` is the external tensor product of their general-linear opposite Jacquet
modules (each normalized by the positive half of its own upper modulus). The
refined Levi acts through its block coordinates `refinedLeviEquiv.symm`.

Proof: the intertwining identity is checked on each vector. Write the vector as
the class of some `y` (`refinedOppositeJacquetMk_surjective`) and induct on `y`
with `PiTensorProduct.induction_on`. Sums follow from additivity. A scalar
multiple of `tprod v` follows from `refinedCoinvariantsEquiv_comm`.
