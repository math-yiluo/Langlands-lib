# Relative parabolic transport compatibility import

Worker 648.

This compatibility module imports the canonical
`RelativeLevi.ParabolicBaseChange` module. It declares no new mathematics.
The imported module provides source and ambient isomorphism transport,
field-point parabolicity and preservation of relative parabolicity under
arbitrary scheme base change in a reductive ambient group.

Earlier development of the étale conjugacy proof used this module path.
Keeping the import preserves that path while sharing the canonical transport
declarations with the parabolic moduli construction. The canonical constructor
`relativeParabolicBaseChange` takes an inclusion equipped with its relative
parabolicity proof as a subtype argument.

## Unbundled inclusion constructor

# Transport of relative parabolic subgroup inclusions

Worker 648.

This is an internal transport construction from the published
`IsRelativeParabolicSubgroup` predicate, parabolic preservation under
field extension (`parabolicFieldExtensionStatement`), reductive residue
fibres, and the canonical pullback comparisons. It introduces no external
mathematical input.

For a group-scheme homomorphism `i : P → G` over an arbitrary scheme `S`,
`IsRelativeParabolicSubgroup.comp_iso` transports relative parabolicity
through an isomorphism of the ambient group. Smoothness and affineness of
`P` are unchanged, monomorphy is preserved by the ambient isomorphism,
and each residue-fibre parabolic is transported through the base change
of that isomorphism.

`IsRelativeParabolicSubgroup.iso_comp` transports the predicate through an
isomorphism of source presentations. Smoothness and affineness transfer
through the source isomorphism, as does monomorphy; the residue-fibre
condition uses the corresponding published field-level source transport.
Neither isomorphism lemma requires reductivity.

When `G` is reductive,
`IsRelativeParabolicSubgroup.isParabolicSubgroup_baseChange` proves that
the actual pullback of `i` along every morphism `f : Spec k → S` from a
field spectrum is parabolic. Factor `f` through the residue field at its
image point, use connected reductivity of that residue fibre and the
published parabolic field-extension theorem, then transport the result
through `Descent.pullbackComparison`. Its naturality identifies the
resulting inclusion with the actual pullback along `f`.

`IsRelativeParabolicSubgroup.baseChange` proves preservation under every
scheme morphism `b : S' → S`, with reductivity of `G` as a hypothesis.
The source's smoothness, affineness, and the inclusion's monomorphy are
preserved by pullback. For each point of `S'`, the preceding field-point
lemma applies to the composite `Spec κ(s') → S' → S`; the pullback
comparison identifies this direct fibre with the iterated fibre of the
base-changed inclusion.

`relativeParabolicBaseChangeOfInclusion b hG i hi` packages the actual homomorphism
`(baseChange b).map i` and its relative parabolicity in a subtype. Its
value is exactly the base-changed inclusion, as recorded by
`relativeParabolicBaseChangeOfInclusion_val`. The construction imposes no affine,
reduced, Noetherian, or finite-type condition on the base schemes.
