# Witnessed generators from Harris's automorphic induction

Author: Worker 5134. Module `Langlands.Global.Arithmetic.HenniartInducedGenerator`. It is
a helper for the reduction `HenniartGlobalizationReductionStatement`
(`Langlands.Global.Arithmetic.HenniartGlobalizationReduction`) of
`HenniartGlobalizationStatement` (Henniart 2000, §3.4). It contains no definitions.

## Projection formula

`ExactGrothendieckGroup.continuousTwist_continuousInduceAlong φ hφ η x`: for an open
embedding `φ : H → G` of topological groups with image of finite index, a continuous
character `η` of `G` and a class `x` of continuous representations of `H`,

`η ⊗ Ind_φ x = Ind_φ ((η ∘ φ) ⊗ x)`.

Proof: unfold `continuousInduceAlong` as restriction along the inverse
`range φ ≅ H` followed by induction from `range φ`. Twisting commutes with restriction
(`continuousRestrict_continuousTwist`) and satisfies the projection formula for induction
from a subgroup (`continuousInduce_continuousTwist`). The two characters of `range φ`
agree because `φ (rangeInverse s) = s` (`InductionAlong.apply_rangeInverse`).

## Generators from Harris's induction

`RelativeGlobal.exists_witnessedGenerator_inducedReciprocity hlrm hlir hcalip hacc hasi
htransfer hc ξ hreg hconj π hπ v u eu heu z hz`.

Setting: `c` an arithmetic class family; `F ⊆ E' ⊆ L` number fields with `L/F` Galois,
`F` totally complex, `E'` a CM field, compact adele quotient of `F`; `ξ` a Hecke character
of `E'` that is `E'/F`-regular (`Harris.IsRelativelyRegular F ξ`) and conjugate-inverse
(`ξ⁻¹ = ξ ∘ c`, `Harris.IsConjugateInverse ξ`); `π` a cuspidal class of `GL_r` over `F`
that is a weak automorphic induction of `ξ` (Harris 1998, Definition 1.3(b)); `v` a
finite place of `F` with exactly one place `u` of `E'` above it; `eu` a geometric Weil
reciprocity candidate of `E'_u`; `|z| = 1`.

Conclusion: some witnessed generator `d` at `v` for `W_{L/F}` satisfies

`realizeExact (includeUnitary d.weilElement) =
  z_unr ⊗ Ind_{completionWeilMap v u} [weilCharacter eu (ξ_u)]`,

where `z_unr = localUnramifiedCharacter (padicField v) z` and the induction is along the
local Weil map `W_{E'_u} → W_{F_v}`.

Hypotheses: the published propositions `LocalRelativeWeilMapExistenceStatement` (`hlrm`),
`LocalInducedRestrictionStatement` (`hlir`, Tate 1979 (2.3.5)),
`CuspidalAllLocalIrreduciblePresentationExistenceStatement` (`hcalip`),
`AssociatedCentralCharacterStatement` (`hacc`), `AssociatedSupercuspidalInductionStatement`
(`hasi`) and `LocalTransferReciprocityStatement` (`htransfer`). `hlrm` and `hcalip` are
now proved in the Library; the reduction module supplies those proofs.

Proof.

1. `weakInductionAssociation_of_local` (with the published
   `geometricWeilReciprocityExistenceUniqueness`, `hlrm`, `hlir`) shows that the induced
   reciprocity representation `S := Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ)` is weakly associated
   with `π`.
2. `S` is irreducible (`inducedReciprocityRepresentation_isIrreducible`, from regularity)
   and unitary (`inducedReciprocityRepresentation_isUnitary_of_isConjugateInverse`).
3. Choose a place `w` of `L` above `v`, a geometric reciprocity candidate of `L_w`, and
   by `hlrm` a local relative Weil map `ι : W_{F_v} → W_{L/F}`.
   `exists_witnessedGenerator_realizeExact` (module `HenniartWitnessedGenerator`) gives a
   witnessed generator `d` whose Weil element realizes the restriction of `S` along `ι`.
4. `continuousRestrict_inducedReciprocityRepresentation_class` (published module
   `Langlands.Automorphic.InducedReciprocityLocalClass`, using `hlir` and uniqueness of
   `u`) identifies this restriction with
   `Ind_{completionWeilMap v u} [weilCharacter eu (ξ_u)]`.
   `ExactGrothendieckGroup.restrict_ofRepresentation` matches the two forms of the
   restriction class.
5. `exists_witnessedGenerator_unramifiedTwist` twists `d` by `z_unr`.

## Provenance

Internal helper for Henniart (2000), §3.4: Harris's automorphic induction of `ξ`
(Harris 1998, Proposition 4.8 provides `π`) gives the Weil-group representation
`Ind (ξ ∘ τ)`, whose restriction at `v` is computed by Tate's local restriction formula.
The projection formula is the standard identity `η ⊗ Ind x = Ind (Res η ⊗ x)`.
