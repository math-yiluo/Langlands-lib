# Proof of the unipotent Iwahori double-coset bijections

This unit proves the published target
`Langlands.Geometry.Building.UnipotentIwahoriDoubleCosetStatement` of
`Langlands/Geometry/Building/IwahoriWeylStatement.lean`. The theorem
`Langlands.Geometry.Building.unipotentIwahoriDoubleCoset` is stated at an arbitrary universe `u`.
Its type is exactly `UnipotentIwahoriDoubleCosetStatement.{u}`, so no hypothesis is changed or
added.

## What is proved

The target is the added KP Theorem 7.8.1(4) of the authors' 2024 corrections. It quantifies
over every nonarchimedean local field `F` and every affine group scheme `G` over `F`. For every
`P : ParahoricBuildingData G` it assumes that `𝒪[F]` is Henselian, that `𝓀[F]` is perfect, and
that `P.apartment.SatisfiesApartmentAxioms P.centralizer` holds. Then, for every chamber `C`
of `P.affineRoots` and every generic cocharacter `ν`, it gives
`P.UnipotentIwahoriDoubleCosetBijection C ν`. Write `U = standardUnipotentPoints P.i ν ∅`,
`I = P.parahoric C`, and `Z₀` for the image of `P.centralizerZero` in `G(F)`. The conclusion has
two parts.

1. An equivalence `e : P.IwahoriWeylGroup ≃ DoubleCoset.Quotient U I` with
   `e (QuotientGroup.mk n) = DoubleCoset.mk U I n` for every `n ∈ N(F)`.
2. An equivalence `e : P.IwahoriWeylGroup ≃ DoubleCoset.Quotient (U * Z₀) I`, where `U * Z₀`
   is the literal pointwise product set, with `e (QuotientGroup.mk n) = Quotient.mk'' n` for
   every `n ∈ N(F)`.

`P.IwahoriWeylGroup` is the full quotient `N(F) ⧸ P.normalizerZero`, which keeps all
components.

## Structure of the proof

The proof applies the published per-data assembly
`ParahoricBuildingData.unipotentIwahoriDoubleCosetBijection_of_iwasawa_coset` (module
`UnipotentIwahoriQuotientReduction`) to two facts about the given `P`, `C` and `ν`.

* **Iwasawa** (`P.IwasawaDecomposition C ν`, KP Theorem 5.3.3): `G(F) = U · N(F) · I`. This is
  the published theorem `iwasawaDecomposition`, applied to the target's hypotheses.
* **Corrected normalizer-coset criterion** (`P.UnipotentNormalizerCoset C ν`, the replaced KP
  Lemma 5.3.5): for `n, n' ∈ N(F)`, `n ∈ U n' I` holds if and only if `n' n⁻¹ ∈ Z(F)^0`. It
  comes from the published `unipotentNormalizerCoset_of_chamberIwahori`, which needs three
  inputs, supplied as follows.
  - The instance `[P.normalizerZero.Normal]`, normality of `Z(F)^0` in `N(F)`. This is
    `ParahoricBuildingData.normal_normalizerZero` from the companion module
    `ZeroSubgroupCommutatorNormality` (described below).
  - The chamber Iwahori decomposition `P.ChamberIwahoriDecompositionStatement`. This is the
    published `chamberIwahoriDecomposition_of_rankOneFactorization`, applied to three published
    proofs: rank-one factorization `rootRankOneFactorization` for the actual maximal split
    torus, the cover comparison `P.zeroDatum.coverImageCentralizerNormKernel`, and
    `RelativeRoot.dynamicRootOrderedProduct`.
  - The retained apartment axioms, chamber and genericity hypotheses.

How the published assembly turns these two facts into the two equivalences:

* **Descent to the quotient.** The representative map `n ↦ U n I` is constant on cosets of
  `Z(F)^0`. If `n' n⁻¹ ∈ Z(F)^0`, the criterion gives `n ∈ U n' I`. Hence the map descends to
  `P.IwahoriWeylGroup` (`normalizerDoubleCosetMap`), and its value on each class `mk n` is the
  double coset of `n` by construction.
* **Injectivity.** By quotient induction, two classes `mk n` and `mk n'` with the same double
  coset satisfy `n ∈ U n' I`. The criterion then gives `n' n⁻¹ ∈ Z(F)^0`, so `mk n = mk n'`.
* **Surjectivity.** Each `g ∈ G(F)` is `u n p` by Iwasawa, so the double coset of `g` is that
  of the representative `n`.
* **The two left-coset conventions.** Every centralizer point normalizes `U`, so the carrier of
  the subgroup `U ⊔ Z₀` is exactly the pointwise product `U * Z₀`. A relation
  `n' = (u z) n p` with `u ∈ U`, `z ∈ Z₀` and `p ∈ I` becomes `n' = u n ((n⁻¹ z n) p)`.
  Normality of `Z(F)^0` in `N(F)` puts `n⁻¹ z n` into `Z₀ ⊆ I`. The assembly re-derives this
  normality from the criterion (`normalizerZero_normal_of_unipotentNormalizerCoset`). The
  relation is therefore again of the first kind, and the same criterion decides it. Conversely, a relation with left factor in `U` has left factor in
  `U ⊔ Z₀`. Iwasawa again gives surjectivity. The equivalence for the subgroup `U ⊔ Z₀` is
  transported along the carrier equality to the literal set quotient by `U * Z₀`, including the
  representative equation `e (mk n) = Quotient.mk'' n`.

## Normality of `Z(F)^0` in `N(F)`

The target forces this normality: the second equivalence implies `n⁻¹ Z(F)^0 n ⊆ Z(F)^0` for
`n ∈ N(F)`. The Library previously had it only conditionally, from KP Lemma 2.6.24. The
companion modules prove it outright.

* `Langlands.GroupScheme.SimplyConnected.CommutatorCoverImage` proves that every commutator of
  points of a connected reductive group lifts to the simply connected cover of its derived
  subgroup. It applies the published commutator descent to the central product
  `R × G_sc → G`, where `R` is a central torus.
* `Langlands.Geometry.Building.ZeroSubgroupCommutatorNormality` deduces that `G(F)^0`, which
  contains `G(F)^♮`, contains all commutators and is therefore normal. The published
  `normalizerZero_normal_of_zeroSubgroup_normal`, together with the cover comparison, then
  gives normality of `Z(F)^0` in `N(F)`.

## Hypotheses and scope

The theorem keeps the Henselian and perfect-residue-field hypotheses unchanged. This route does
not use them. The apartment axioms are used by Iwasawa and by the coset criterion. The proof
adds no Iwasawa, normalizer-coset, bijection or building-validity premise: both geometric facts
are derived from published proofs. The result is conditional on actual `ParahoricBuildingData`
satisfying the fixed-apartment axioms. It does not construct such data, and it does not prove
the component exact sequence of KP Theorem 7.8.1(1).

## Provenance

The statement is KP Theorem 7.8.1(4), added in the authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, PDF pp. 35–36). There it is derived from Theorem 5.3.3 and
the replaced Lemma 5.3.5 (corrections PDF p. 30). The implemented proof follows that structure,
with descent, injectivity and surjectivity as in the published quotient assembly. The normality
of `Z(F)^0` comes from the commutator route described above, not from the independence argument
of KP Lemma 2.6.24 (book printed p. 104, PDF p. 135).
