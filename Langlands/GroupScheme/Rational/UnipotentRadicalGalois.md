# Unipotent radicals under field isomorphisms and Galois transport

This is an internal consequence of the published represented-radical,
base-change, and subgroup-functor interfaces. It supplies the invariance step
needed before attempting effective descent of a geometric radical. Every field
has the same arbitrary universe `u`; no characteristic, perfectness, finiteness,
separability, or algebraicity assumption occurs.

`IsUnipotentRadical.baseChange_ringEquiv` preserves an existing represented
ground-field radical under an actual field isomorphism `f : k ≃+* K`.
The ambient group over `k` is assumed affine. The radical predicate is unchanged:
it requires a smooth connected unipotent normal closed subgroup whose image
contains every such subgroup on every relative test scheme.

The pullback comparison along a section is natural in actual group-scheme
homomorphisms (`RadicalFieldTransport.sectionIso_naturality` and its inverse
version, imported from `GroupScheme/SectionComparisonNaturality`). The helper `range_le_of_section` transports containment through this
comparison and reflects it by fpqc descent of containment in a monic represented
subgroup. Its explicit hypotheses are quasi-compactness, flatness, and
surjectivity of the inverse base map, together with a section equation and
monicity of the pulled-back inclusion.

For the field-isomorphism theorem, the inverse field isomorphism gives that
section and an isomorphism of base schemes. Closed immersion, smoothness, and
normality are preserved by pullback. Connectedness is transported through the
underlying scheme isomorphism. Affineness of the subgroup follows from its
closed immersion into the affine ambient group; unipotence is transported by
the published field-extension theorem, with the algebra structure induced by
the specified field homomorphism.

To verify greatestness, pull any competing subgroup back along the inverse
field isomorphism and compose its inclusion with the section comparison. It
satisfies all six required geometric and normality conditions over `k`, so the
original radical's greatestness applies. The containment helper then gives
containment in the original pullback over `K`. This argument uses invertibility
of the field map; the module makes no radical-preservation assertion for an
arbitrary field extension.

For an arbitrary field extension `K / k`, an affine group `G` over `k`, an
existing represented radical `i : U ⟶ G_K`, and any actual `k`-automorphism `σ`
of `K`, `radicalGaloisHom i σ` is the pullback of `i` along `Spec σ`, followed by
the canonical descent isomorphism of `G_K`. The theorem
`IsUnipotentRadical.galoisTransport` applies field-isomorphism transport and
ambient-isomorphism transport to this actual inclusion. Uniqueness of greatest
represented radicals gives `range_galoisTransport` on every relative test.
Rewriting the represented range through pullback and the ambient comparison
gives `descentTransport_range` for the existing subgroup-functor transport.

`IsUnipotentRadical.galoisSourceIso` is the actual isomorphism from the translated
source `(Spec σ)^* U` to `U` obtained from equality of the two closed subgroup
images. Its theorem `galoisSourceIso_hom_comp` states that it commutes with the
actual inclusions. This module proves invariance and that commuting comparison;
existence, effective descent, splitness, and a descent cocycle law are separate
obligations. The rational maximal-torus conjugacy theorem remains unproved.
