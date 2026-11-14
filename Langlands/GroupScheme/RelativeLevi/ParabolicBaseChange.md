# Presentation transport and base change of relative parabolic subgroups

Worker 610. This is derived infrastructure for the scheme of parabolic subgroups.
It does not construct the parameter scheme or prove
`RelativeParabolicSchemeStatement`.

The module imports the unchanged `RelativeLevi.Basic` predicates and proves:

- `IsRelativeParabolicSubgroup.iso_comp` and `.comp_iso`: isomorphisms of the
  source presentation and the ambient group preserve relative parabolicity.
- `.of_range_eq` and `isRelativeParabolicSubgroup_iff_of_range_eq`: two monic
  presentations with equal all-test subgroup functors have the same relative
  parabolic property. No ambient reductivity or closedness premise is needed.
- `.isParabolicSubgroup_baseChange`: for a reductive ambient group, the pullback
  of a relative parabolic along any field-valued point is a field parabolic.
- `.baseChange`: for a reductive ambient group, arbitrary scheme base change
  preserves relative parabolicity.
- `relativeParabolicBaseChange`: the actual base-change operation on inclusions
  equipped with proofs of relative parabolicity, with its value formula.

The field-point proof factors `Spec k → S` through the residue field at its
image, applies the published `parabolicFieldExtensionStatement` to the residue
fibre using `IsReductive.isConnectedReductive_residueFiber`, and transports
source and target along the canonical iterated-pullback comparisons. For
arbitrary scheme base change it applies this field-point result to each residue
field of the new base and uses the same comparisons. Smoothness, affineness and
being a monomorphism are preserved by pullback.

For presentation invariance, equality of represented subgroup functors supplies
an isomorphism of their monic presentations. The isomorphism preserves the
structure morphism properties and every residue-fibre parabolic property.

These are derived consequences of the published definitions and imported
transport, field-extension and reductive-base-change theorems. No new source
assertion is postulated. The general-base parabolic convention is Conrad,
*Reductive group schemes* (2014), Definition 5.2.1, p.151; these lemmas justify
the base-change operation used by the functor in Corollary 5.2.9, pp.156–157.
