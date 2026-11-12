# Henniart's relative globalization from Harris's Proposition 4.8 and five open inputs

Author: Worker 5134. This is an internal supporting unit of the proof task
`1b87b965-a232-4c02-a51f-e287f630c549`. That task's exact target is
`Langlands.Global.HenniartGlobalizationStatement`
(`Langlands/Global/Arithmetic/HenniartGlobalizationStatement.lean`). The module
`Langlands.Global.Arithmetic.HenniartGlobalizationReduction` defines the proposition
`Langlands.Global.HenniartGlobalizationReductionStatement` and proves it as
`henniartGlobalization_reduction`. It keeps five published, still unproved
propositions as antecedents. It does not prove the unconditional target, and publishing
it does not complete the host task.

## The reduction statement

`HenniartGlobalizationReductionStatement.{uK, uQ, uW, uP}` is the implication

```
LocalClassField.CommonClosureReciprocityExistence.{uK} →
  LocalInducedRestrictionStatement.{uW, 0} →
    AssociatedCentralCharacterStatement.{0, uW, uP} →
      AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
        LocalTransferReciprocityStatement.{0} →
          HenniartGlobalizationStatement.{uK, uQ, uW, uP}
```

The antecedents and the conclusion are the published propositions, with unchanged
quantifiers. The universe parameters of the target are kept. The antecedents are used
at the universe levels the proof needs: the class families, number fields and local
fields of the target are in universe `0`, the p-adic field `K` is in `uK`, Weil-group
carriers are in `uW` and presentation carriers in `uP`.

- `Langlands.LocalClassField.CommonClosureReciprocityExistence.{uK}`
  (`Langlands/ClassFieldTheory/Local/ReciprocitySystemStatement.lean`): every p-adic field
  has a geometrically normalized coherent family of local reciprocity maps on its finite
  extensions. It supplies the family `e` on `K` in Harris's Proposition 4.8. Proof task
  `26fda979-9fe9-4e34-b341-a68f57de7f89`. The Library reduces it to
  `FiniteCupArtinCharacterComparison`
  (`commonClosureReciprocityExistence_of_finiteCupComparison`).
- `Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement.{uW, 0}`
  (`Langlands/VirtualRepresentation/Global/RelativeWeilLocalRestrictionStatement.lean`):
  Tate (1979), (2.3.5) with (1.6.1), the local restriction formula for representations
  induced from relative Weil groups. Proof task `cfea3159-7908-43b1-a677-75834c3859bd`.
- `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement.{0, uW, uP}`
  (`Langlands/Automorphic/AssociatedCentralCharacterStatement.lean`): Henniart (2000),
  §2.2, `det S = ω_Π ∘ τ_F`. Proof task `35beef68-9782-4d26-93f1-cb2bae2dec95`.
- `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`
  (`Langlands/Automorphic/AssociatedFactorStatement.lean`): Henniart (2000),
  Théorème 2.4. Proof task `65c9a94c-af88-4876-baa4-43d78ccd5531`.
- `Langlands.ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement.{0}`
  (`Langlands/ClassField/Global/LocalRelativeWeilTransferStatement.lean`): Tate (1979),
  (1.6.1), the transfer of a local map is inverse geometric local reciprocity. Proof task
  `960e8dac-1593-4e9e-a96e-20cc689cb4aa`.

Harris's Proposition 4.8 is not an antecedent of the reduction. It is the hypothesis of
`HenniartGlobalizationStatement` itself. The other inputs of the argument are already
proved in the Library and are used through their proofs:
`localRelativeWeilMapExistence`, `cuspidalAllLocalIrreduciblePresentationExistence`,
`geometricWeilReciprocityExistenceUniqueness`, `weakInductionAssociation_of_local`,
`cuspidalDeterminantMultiple`, `presentedDeterminantMultipleAssociation`,
`henniartCommonBaseRealization` and `harrisDatumCharacterRealization`.

## Supporting results in this module

- `finite_extension_le K M`: a finite extension `M` of a p-adic field `K` has finitely
  many subextensions `F'` (as `Extension K` with `F' ≤ M`). Proof: `K` has
  characteristic `0`, so `M/K` has a primitive element
  (`Field.exists_primitive_element`) and finitely many intermediate fields
  (`Field.finite_intermediateField_of_exists_primitive_element`).
  `IntermediateField.restrict` embeds the subextensions into them, injectively by
  `IntermediateField.lift_restrict`.
- `norm_eq_one_of_trivial_on_finiteIndex N η hη a`: a character `η` of a subgroup `H`
  that is trivial on `H ∩ N`, for `N` normal of finite index, has values of modulus `1`.
  Proof: `a^m ∈ N` for `m` the index of `N ∩ H` in `H` (`Subgroup.pow_index_mem`), so
  `|η(a)|^m = 1` with `m ≠ 0`.
- `exists_weilImage_realizeExact_generator hHarris hccre hlir hacc hasi htransfer hc K v₀
  ι₀ hι₀ hι₀s h F' … hconf hPv hPiso L hL η hη`: the generator step at the common place
  `v₀`. Let `ι₀ : F₀_{v₀} ≅ K` be continuous in both directions. Take a paired-place
  configuration for `F'` with `P.v = v₀` (`hPv`) whose isomorphism `P.iso` agrees with `ι₀`
  on `F₀` (`hPiso`). Let `f := completionAlgEquivOfContinuous v₀ K h ι₀ hι₀s`, `L` an
  extension of `F₀_{v₀}` with `T y ∈ W_L ↔ y ∈ W_{F'}`, and `η` a modulus-one character of
  `W_L`. Then `Ind_{W_L}[η]` is the realization of an element of
  `weilImage F₀ 𝔼 c v₀`. Proof: substitute `hPv`. `P.iso` is continuous by the
  configuration. `completion_ringHom_ext` (density of `F₀` in `F₀_{v₀}`) gives
  `P.iso = ι₀`, so `f⁻¹ = P.iso`. Then apply `exists_weilImage_realizeExact_continuousInduce`
  (module `HenniartGeneratorRealization`) with the Library proofs
  `localRelativeWeilMapExistence` and `cuspidalAllLocalIrreduciblePresentationExistence`.
- `henniartGlobalization_of_inputs hccre hlir hacc hasi htransfer`: the main theorem
  below, with the five antecedents as hypotheses.
- `henniartGlobalization_reduction`: the reduction statement, by
  `henniartGlobalization_of_inputs`.

## Proof of `henniartGlobalization_of_inputs`

Fix Harris's Proposition 4.8, an arithmetic class family `c`, a p-adic field `K` and
`q : Gal(K̄/K) → Q` with `Q` finite.

1. *A finite Galois level.* Let `N_q := factoringKernelClosure K q`, the closure in `W_K`
   of the kernel of `q ∘ proj`. It is open, normal and of finite index (published module
   `Langlands.LocalFactor.CommonClosureFactoringBrauer`). `exists_open_normal_le` gives an
   open normal subgroup `U` of `Gal(K̄/K)` with `proj⁻¹(U) ⊆ N_q`. Let `M` be the fixed
   field of `U`. It is finite over `K` (`InfiniteGalois.fixingSubgroup_fixedField`,
   `InfiniteGalois.isOpen_iff_finite`).
2. *The common base.* `henniartCommonBaseRealization p K M` (Henniart 2000, §3.3) gives a
   CM number field `F₀`, a place `v₀`, a bicontinuous isomorphism `ι₀ : F₀_{v₀} ≅ K`, and
   for every subextension `F'` of `M` a paired-place configuration with `P.v = v₀` and
   `P.iso = ι₀` on `F₀`. These are chosen once for all `F'` (`choose`). The configuration
   of `M` puts `p` in `v₀`, so `residuePrime v₀ = p` (`residuePrime_eq_of_natCast_mem`);
   it is substituted. Let `f := completionAlgEquivOfContinuous v₀ K rfl ι₀ hι₀s`.
3. *The Galois extension.* There are finitely many `F'` (`finite_extension_le`).
   `familyGaloisOverfield` gives a number field `𝔼`, Galois over `F₀`, with embeddings of
   all the fields `E'` of the configurations over `F₀`. The witnesses of
   `RelativeGaloisGlobalization` are `F := F₀`, `E := 𝔼`, `v := v₀`, `h := rfl` and `f`.
4. *Brauer induction.* Let `x` be a unitary virtual class of `W_K` supported on classes
   that factor through `q`, and let `T := completionWeilTransportEquiv v₀ rfl K f`. Its
   underlying map is `completionWeilTransport v₀ rfl K f`. The published
   `realizeExact_includeUnitary_mem_map_span` writes the realization of `x` as the
   restriction along `T` of an element `z` of the `ℤ`-span of `inducedCharacterClassesAbove`
   for `T(N_q)`. These are the classes `Ind_{W_L}[η]` with `T(N_q) ⊆ W_L` and `η`
   trivial on `T(N_q)`.
5. *Each generator lies in the Weil image.* For such `L` and `η`, the subgroup
   `T⁻¹(W_L)` contains `proj⁻¹(U)`. By `exists_extension_eq` it is `W_{F'}` for a
   subextension `F'` of `M`, which gives `hL`. `η` has modulus `1` by
   `norm_eq_one_of_trivial_on_finiteIndex` applied to `T(N_q)`, which has finite index.
   `exists_weilImage_realizeExact_generator`, with the configuration of `F'` and the
   embedding `E' → 𝔼` from step 3, gives `y` in `weilImage F₀ 𝔼 c v₀` realizing
   `Ind_{W_L}[η]`.
6. *Conclusion.* By step 5 the span from step 4 lies in the image of `weilImage` under
   `realizeExact ∘ includeUnitary` (`Submodule.span_le`). So `z` is the realization of some
   `y ∈ weilImage F₀ 𝔼 c v₀`, and the restriction of the realization of `y` along
   `completionWeilTransport` is the realization of `x`.

## Helper modules

The proof uses four further new modules of this unit, each with its own Markdown:

- `Langlands.Global.Arithmetic.HenniartWitnessedGenerator`: witnessed generators from
  irreducible unitary representations weakly associated with cuspidal classes, and
  their unramified twists.
- `Langlands.Global.Arithmetic.HenniartInducedGenerator`: the projection formula for
  induction along open embeddings, and witnessed generators from Harris's automorphic
  induction.
- `Langlands.Global.Arithmetic.HenniartLocalCharacter`: matching a local component with a
  prescribed Weil character up to an unramified twist.
- `Langlands.Global.Arithmetic.HenniartGeneratorRealization`: one Brauer generator
  `Ind_{W_L} η` lies in the Weil image.

## Provenance

Internal. The implication is Henniart (2000), §§3.3–3.7, the proof of Théorème 3.1 from
Harris (1998), Proposition 4.8, with the local inputs isolated as the published
propositions above. The Brauer induction step is Henniart's reduction to induced
characters (Brauer's theorem). The common base and the Harris datum are §3.3. Applying
Harris's proposition and computing the local component are §3.4, through Tate's local
restriction formula (Tate 1979, (2.3.5)) and Henniart's Théorème 2.4. No source
statement is translated here. The proposition only chains published statements.
