# Closed equality loci for actual maps into a chosen dual

This is an internal construction from published Library results, with no new literature assertion. The input is an arbitrary scheme `S : Scheme.{u}`, an abelian scheme `B : Langlands.AbelianScheme S`, its existing datum `hB : HasDualScheme B`, and two actual morphisms `f g : B.X ⟶ dualScheme B hB` in `Over S`. The morphisms need not preserve a group law or the origin.

The public definition `Langlands.AbelianScheme.DualMapEquality.locus B hB f g` chooses an object of `Over S` before any test is supplied. Its structure morphism is a closed immersion, by `locus_isClosedImmersion`. For every `T : Over S`, `locus_nonempty_iff` proves exactly

```text
Nonempty (T ⟶ locus B hB f g) ↔
  (Over.pullback T.hom).map f = (Over.pullback T.hom).map g.
```

There are no noetherian, quasi-separated, reducedness, projectivity or Hom representability hypotheses. All pullbacks and all equalities are those of actual morphisms of schemes. In particular, the universal property includes nonreduced test schemes. This file handles one pair; a finite intersection extension can use its chosen closed locus.

The construction and its implemented proof are as follows. All the helper names below are in `Langlands.AbelianScheme.DualMapEquality`.

1. `square B` equips the actual fibre product `B ×_S B` with the abelian scheme structure coming from the cartesian product of the group objects. Smoothness, properness and geometric connectedness follow from base change and composition. `axis B` is the map `x ↦ (x,0)`. The lemma `origin_eq` computes the unit of the product as the original unit followed by this axis, using the two group projections.
2. A rigidified family over parameter `B.X` is a line bundle on this self-product rigidified along `axis B`. The definition `atOrigin` restricts that trivialization along the unit section to rigidify the same underlying line bundle at the product origin. This does not require the corresponding parameter map to send zero to zero. The definition `identityFamily` pulls this bundle to the relative self-product over the identity test `Over.mk (𝟙 S)`.
3. `identityFamily_class` computes the ordinary Picard class of this encoding after any test pullback as the pullback of the original underlying line-bundle class along `T ×_S (B ×_S B) → B ×_S B`. The helper `pullback_injective_of_iso` follows from contravariant Picard functoriality and the inverse isomorphism.
4. `parameter B T` is `T ×_S B` regarded over `S`, with projection `parameterMap B T` to `B.X`. The isomorphism `associate B T` is Mathlib's actual pullback associator from `(T ×_S B) ×_S B` to `T ×_S (B ×_S B)`. `associate_snd` checks its two coordinates. These calculations and `RigidifiedLineBundle.forgetClasses_injective` prove `identityFamily_eq_iff`: equality of the origin encodings is precisely equality of the original family classes pulled back along `parameterMap`.
5. `mapFamily B hB f` is the actual rigidified pullback of `poincareFamily B hB` along `f`. The lemma `poincare_classifying_injective` uses the published Picard-zero pullback stability theorem and the uniqueness part of `poincareFamily_universal`. Classifying-map functoriality then makes `encoding_eq_iff` identify equality of the encodings with equality of the parameter maps after pullback. The helper `baseChange_eq_iff` proves this is the required equality in `Over T`, explicitly using pullback symmetry and both pullback projections.
6. `exists_closed_locus` applies the published theorem `rigidifiedClassesEqualizerClosed` to the two encoded classes on `square B`, with parameter the identity test. It converts its factorization property into `Nonempty (T ⟶ Z)` and uses `encoding_eq_iff`. The definition `locus` chooses this closed object; the instance and final theorem expose its two properties.

The provenance is internal: this unit combines `rigidifiedClassesEqualizerClosed`, the existing actual Poincaré family and its universal property, `picardZeroPullback`, split-section injectivity of forgetting rigidification, ordinary Picard pullback functoriality, and Mathlib's pullback identities. It does not strengthen `HasDualScheme`, supply a Hom representative, or use a polarization inverse. It changes no existing imported pair or Harris representability target and does not discharge the separate arithmetic or Picard infrastructure obligations.
