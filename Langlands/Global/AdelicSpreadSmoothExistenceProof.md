# Compatible smooth morphisms over actual arithmetic integer rings

Authors: Worker 208 and Worker 1557.

This proof establishes
`Langlands.Global.AdelicSpreadSmoothExistenceStatement` in arbitrary common
universe `u`. It adapts Worker 208's proper-model existence proof, retaining
the original arithmetic rings and generic-fibre coherence.

The reusable helpers `curvePlaceSpreadMorphismPropertyExistence` and
`numberFieldSpreadMorphismPropertyExistence` require an isomorphism-invariant morphism
property and its actual arithmetic eventual-detection theorem. This endpoint uses
them for smoothness and for smoothness conjoined with the prescribed full
fibre geometry. These are instantiated with the separate arithmetic
smoothness/fibre-geometry proof; they are not assumptions of the final
theorem. They also provide the same compatible-model construction for any
property with a separately proved eventual-detection theorem.

Choose separated finite-type arithmetic models for the target and source,
successively above the prescribed initial finite set. Base-change the
target model to the source's level, obtaining two models over one actual
integer ring. Conjugate the field morphism by their generic-fibre
isomorphisms. Isomorphism invariance transports its property. Descend this
morphism to a finite superlevel using the actual integer-algebra colimit
and the published model-morphism descent theorem.

Naturality of the canonical iterated-pullback isomorphisms identifies the
generic fibre of this descended morphism with the conjugated field
morphism. Isomorphism invariance again gives its generic-fibre property.
The arithmetic eventual-detection theorem enlarges once more so that the
model morphism has the property. Both models remain separated and of
finite type by actual base change. This argument retains source
separatedness from its chosen separated model; smoothness alone does not
imply source separatedness.

Compose the canonical generic-fibre isomorphisms through both
enlargements with the original identifications. Their naturality
equations prove the required generic-fibre square. Transitivity of finite
set containment supplies a final level above the originally prescribed
set.

The two arithmetic branches follow this construction using their actual
integer subrings and literal inclusions. The endpoint instantiates the
helper with smoothness alone and, for every fixed `d`, smoothness together
with nonempty geometrically connected pure-dimensional fibres. The latter
uses the previously proved common-stage detection theorem.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, registered as
`conrad-2011-weil-grothendieck-adelic-points` with PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The provenance is the compatible-model step in the proof of Conrad's
Theorem 4.5, and Theorem 3.4(1),(2) with Remark 3.5, as detailed in the
target's paired Markdown. This proof does not perform the
connected-component dimension reduction, establish Lang–Weil, or prove
adelic openness.

The proof uses every prescribed finite initial set, including the empty set,
and arbitrary perfect function-field constants through the published
arithmetic colimits and separated-model existence results. No separability
over the chosen rational-function field or affineness of the field schemes
is added. The public generic helpers retain their explicit eventual-property
premise; `adelicSpreadSmoothExistence` discharges it with the published
`curvePlaceSpreadEventualSmoothFiberGeometry` and
`numberFieldSpreadEventualSmoothFiberGeometry` proofs.
