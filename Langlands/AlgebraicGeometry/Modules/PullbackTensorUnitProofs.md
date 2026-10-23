# Pullback compatibility with the explicit tensor unitors

This module proves
`Langlands.Scheme.Modules.PullbackTensorUnitCoherenceStatement` from
`Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitStatements`.
The theorem `pullbackTensorUnitCoherence` is the conjunction of
`pullbackTensorLeftUnitor` and `pullbackTensorRightUnitor`. For every scheme
morphism `f : X ⟶ Y` and module sheaf `M` on `Y`, each law identifies the
composite of the canonical pullback tensor comparison, the tensor of the
canonical unit comparison with an identity, and the corresponding explicit
unitor on `f* M`, with pullback applied to that unitor on `M`.

All schemes and module sheaves lie in an arbitrary universe `u`. The proofs
use the existing `Scheme.Modules.pullback` and its adjunction with pushforward.
They impose no geometric condition, monoidal structure, or tensor-comparison
invertibility hypothesis. The maps and target statement are the published
ones; this module does not redefine them.

The proof uses four helper lemmas and the existing unitor naturality laws.
First, `tensorHomEquiv_leftUnitor` and `tensorHomEquiv_rightUnitor` identify the
explicit sheaf unitors, under the sheafification hom equivalence, with the
unitors of the underlying presheaves. These identities are the inverse laws
of that adjunction's hom equivalence.

The public `tensorLeftUnitor_naturality` and `tensorRightUnitor_naturality`
lemmas are reused from [TensorUnitorLaws](TensorUnitorLaws.md). That module
contains the unchanged scheme-module lemmas formerly in
`Langlands.AlgebraicGeometry.Picard.RigidifiedTensorUnit`. Sharing them at
the Modules layer removes the duplicate private proofs without importing
the Picard layer. This module's local presheaf monoidal instance retains
the explicit name `pullbackTensorUnitProofsMonoidal`.

Next, `pushforwardTensor_leftUnitor` and `pushforwardTensor_rightUnitor` prove
unitality for the pushforward tensor comparison and the structure-sheaf map
`unitToPushforwardUnit`. The sheafification hom equivalence reduces each
equality to an equality of presheaf maps. Extensionality on opens and pure
tensors reduces that equality to the appropriate unitor identity above,
applied on the inverse image open to a tensor whose scalar has been mapped
by the scheme's structure-sheaf morphism.

For each main law, the proof applies injectivity of the pullback-pushforward
adjunction's hom equivalence. It uses the published characterization
`homEquiv_pullbackTensorComparisonApp`, then naturality of
`pushforwardTensorApp` to move the unit comparison through that map.
The published theorem `pullbackUnitAdjunction` identifies the adjunction unit
followed by pushforward of `pullbackUnitIso.hom` with
`unitToPushforwardUnit`. Functoriality of `tensorMap` separates the resulting
tensor into a map containing the adjunction unit and a map containing the
structure-sheaf morphism. The pushforward unitality lemma reduces the latter
part to an explicit unitor. Finally, unitor naturality and naturality of the
adjunction unit give the required equality. The right law uses the same
argument with the factors interchanged.

This is internal categorical infrastructure derived from the imported
constructions and their stated adjunction properties. The proof uses the
pinned Mathlib presheaf tensor unitors, their naturality, and tensor-product
extensionality; it makes no independent literature claim. Full strong
symmetric monoidal pullback, invertibility of the tensor comparison, and
identification with unitors of a localized monoidal structure are separate
obligations, beyond the proposition proved here.
