# Almost simplicity of identity components under field extension

This internal derived module supplies the geometric descent step used by
Worker 97 in Task 5397. Its groups and identity components are the actual
published group schemes; no quaternionic classification result is assumed or
proved here. The fields have arbitrary characteristic and lie in an arbitrary
common universe.

For a smooth affine group `G` over a field `k`, formation of its identity
component commutes with every field extension `L/k`, through the published
`IdentityComponent.baseChangeIso`. Almost simplicity and absolute almost
simplicity of the extended identity component therefore reflect to `G⁰`,
using `IsAlmostSimple.of_fieldExtension` and
`IsAbsolutelyAlmostSimple.of_fieldExtension`, respectively.

The final theorem starts with an affine `G` without assuming it smooth. Its
inputs are a smooth affine group `H` over `L`, an actual group-scheme
isomorphism from `G_L` to `H`, and absolute almost simplicity of `H⁰`. The
isomorphism first transports smoothness to `G_L`. The published
`fieldExtension_fpqc` and `smooth_of_baseChange` descend smoothness to `G`.
With this instance available, `IdentityComponent.mapIso` identifies the
identity components of `G_L` and `H`; the preceding reflection lemma then
descends absolute almost simplicity to `G⁰`. The existential smoothness
witness in the conclusion records the instance needed to form this component.

All steps are compositions of the named published comparison, transport and
descent results. In particular, this module neither constructs a Morita
isomorphism for a quaternionic isometry group nor proves ordinary orthogonal
smoothness or almost simplicity. Those remain separate geometric inputs.
