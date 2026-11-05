# The specified field at the model's generic point

This derived extension of `FiniteSeparableEtaleSchemeModel` proves that the
specified algebraic extension `L/K` is the fraction field of the constructed
model ring itself, and hence the actual residue field at the model's generic
point. It contributes to the domain case of the monic-model step in Stacks
Lemma 37.24.8 (0551), registered source
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`, proof.
The source retains the specified extension in the generic residue field of its
finite etale cover.

The assumptions are those of the imported domain scheme model, in one arbitrary
universe, together with algebraicity of the given `L/K`. For the intended finite
separable constructor, algebraicity is automatic. No further model-existence,
Noetherianity or normality premise is imposed.

`extensionAlgebra` maps the actual ring `d.Carrier` into the original `L` by
inclusion into its generic tensor product followed by the proved `K`-algebra
equivalence. `algebraMap_extension_tmul` computes this map on the actual nested
base-change tensors, and `algebraMap_extension_comp_base` proves compatibility
with the original field map `K → L` on the localized original base.

The generic tensor product is the localization at the images of the nonzero
base elements. Transport across its actual ring equivalence with `L` proves
`extensionLocalization`. The base map is injective because the model is free
and nontrivial. Thus its localization is injective; in the field `L` every
nonzero element of the model becomes a unit. Enlarging the localization
submonoid to all nonzero elements proves `extensionFractionRing`.

`modelGenericMap` is literally the spectrum map of this inclusion. The equation
`modelGenericMap_toBase` identifies its composite with the model's structure
map as `Spec L → Spec K → Spec d.Base`, retaining the specified field map.
`modelGenericResidueFieldIso` then applies the published fraction-field/generic
residue-field comparison to the actual model ring. The comparison theorems prove
that its composite with the generic residue-field point is `modelGenericMap`
and that the resulting map to the base is the same specified field composite.

`toBase_genericPoint` proves that the actual model generic point maps to the
actual base generic point, using injectivity of the structural ring map.
`genericResidueMap` is the actual induced map of their residue-field spectra,
with the equality of base points transported by the canonical residue-field
congruence. Its equation with the residue-field points follows from naturality.
Finally, `modelGenericResidueFieldIso_hom_genericResidueMap` proves that, under
the two specified field identifications, this actual induced map is exactly
`Spec(algebraMap K L)`. The proof cancels the residue-field point, which is a
monomorphism, and uses the already proved equations over the base.

This unit handles the domain cover's fraction field and its actual generic
residue field. It does not prove the nonreduced irreducible-base case, construct
a geometric-component splitting extension, or discharge full Stacks 0551.
