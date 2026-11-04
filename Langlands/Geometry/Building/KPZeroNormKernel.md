# The actual zero subgroup and the rational norm kernel

This derived adapter constructs the canonical homomorphism
`ZeroSubgroupDatum.centralizerZeroNormKernelHom` from the existing actual
centralizer-zero subgroup to its rational-character norm kernel. Its underlying
map is inclusion. The module also proves that the entire actual zero subgroup
lies in the rational-character norm kernel of the ambient group.

All groups and maps are the published group-scheme rational-point constructions.
The local results hold at arbitrary universe `u` for every nonarchimedean local
field `F`, with the existing `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. They impose no characteristic or
positive-rank condition and no new premise on the supplied zero-subgroup data.

## Sources and provenance

The source objects are those of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, with these original passages read
directly:

- Lemma 2.5.6 and Proposition 2.5.8, printed pp.88–89 / PDF pp.119–120:
  extension of the valuation and the character description of the maximal
  bounded torus subgroup.
- Definition 2.5.13 and Lemma 2.5.14, printed p.90 / PDF p.121:
  the torus Iwahori is the norm image of the bounded subgroup over a finite
  Galois splitting extension, and it lies in the character kernel.
- Definition 2.6.20 and Definition 2.6.23, printed p.104 / PDF p.135:
  the simply connected derived-cover image, the zero subgroup over the maximal
  unramified extension, its descent for groups anisotropic modulo center, and
  the general construction using a minimal Levi.
- Lemma 2.6.29, printed p.106 / PDF p.137:
  the source's stronger finite-index assertion for `G(F)^0` in `G(F)^1`.
  This module proves its containment component only.

The 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, PDF pp.24–25, were read directly. They remove
the minus signs in the character-valuation maps of Sections 2.5(b) and 2.6(d),
add the Henselian and perfect-residue-field hypotheses before Definition 2.6.20,
and specify a reductive group over the given field in Definition 2.6.23.
The sign changes preserve the kernels. The local-field instances and the
existing prescribed valuations are unchanged. No project errata file for these
sources was present in the workspace.

The contribution derives new comparisons from the already published
`KPZeroSubgroups`, `GaloisPointRational`, rational-character evaluation,
scheme-theoretic derived-subgroup annihilation, and normalized local-field norm
APIs. It does not redefine any of those source objects. The generic norm
inclusion is proved for every affine commutative group scheme under its stated
valuation-extension and invariance assumptions; it does not require that group
scheme to be a torus or that the extension split it.

## Implemented proof

Over an arbitrary field, `map_characterValuationKernel_le` pulls each character
back along the actual group-scheme morphism. The theorem
`rationalCharacterEval_simplyConnectedImage` applies
`IsDerivedSubgroup.characterRestrict_eq_zero` to the actual derived inclusion.
Consequently every point in the simply connected derived-cover image has
character value one and lies in every character-valuation kernel. This uses
scheme-theoretic derived-subgroup annihilation; it needs no identification with
the abstract commutator subgroup of rational points.

The four lemmas in `GaloisPointComparison` compare rational-character evaluation
with coefficient-point evaluation at the base field and after base change.
Naturality of the coefficient-point maps and the existing multiplicative-group
unit comparisons show that evaluation commutes with scalar extension and with
Galois conjugation for a character defined over the base field.

For valuations `vk` and `vL` with `vk.HasExtension vL`, the theorem
`torusNormIwahori_le_characterValuationKernel` additionally assumes that every
base-field automorphism of the finite Galois extension preserves `vL`. After
extending the norm value, `rationalExtend_norm` expresses it as the product of
Galois conjugates. Every factor has valuation one, so their product does too.
`Valuation.HasExtension.val_map_eq_one_iff` then descends this equality.
The companion `comap_characterValuationKernel_le` descends a unit-character
condition on an extended point by applying the same equivalence to each
base-changed character.

For `K = UnramifiedClosure F` and the intermediate field `L` in the supplied
`UnramifiedZeroDatum`, `intermediateValuation_extends_fixedField` verifies the
extension condition directly from the definitions. The theorem
`intermediateValuation_conjugate` proves invariance of the prescribed valuation:
it uses the local norm on `F`, the spectral-norm tower equality for
`F ⊆ L ⊆ SeparableClosure F`, and spectral-norm invariance under the
`F`-algebra equivalence underlying a `K`-automorphism of `L`.

The theorem `UnramifiedZeroDatum.zeroPoints_le_characterValuationKernel`
combines the derived-cover and torus-norm inclusions by `sup_le`, preserving
the existing join definition of the zero subgroup over `K`.
`anisotropicZeroPoints_le_characterValuationKernel` then applies scalar
descent to its existing comap definition. Neither step requires a proof that
the join equals a product set.

The equality `characterValuationKernel_eq_rationalCommonNormKernel` identifies
the canonical valuation-one condition with the published normalized field norm
kernel using `Plancherel.fieldNormUnits_ker` and `Valuation.mem_unitGroup_iff`.
It gives `ZeroSubgroupDatum.centralizerZero_le_rationalCommonNormKernel` for
the full supplied centralizer-zero subgroup. The definition
`centralizerZeroNormKernelHom` restricts its subtype inclusion to this target;
`centralizerZeroNormKernelHom_coe` records the underlying identity map.
Finally, `zeroSubgroup_le_rationalCommonNormKernel` combines the derived-cover
image with the mapped centralizer-zero subgroup by `sup_le`.

## Remaining obligations

This unit proves containment, not finite index or equality with the norm kernel.
It proves neither compactness, closedness nor openness of the centralizer-zero
subgroup. It also leaves independence and existence of the supplied zero data,
normality of the derived-cover image, equality of the source joins with product
sets, and the full chamber Iwahori compact-openness target to their respective
proof obligations.
