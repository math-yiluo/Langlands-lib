# Base change of topological morphism properties of algebraic spaces

For arbitrary schemes `S` and `T` and `g : T → S`, this internal supporting
module proves preservation of quasi-compactness, universal closedness,
nonempty geometrically connected fibres and properness of algebraic-space
morphisms under `baseChangeMap g`. The morphisms need not be representable.
There are no extra finiteness or separation hypotheses.

`compactFibreAtlasBaseChange` constructs an actual compact scheme atlas of
the fibre over each affine test scheme over `T`, from a quasi-compact
morphism over `S`. View the test scheme over `S` and use the original
quasi-compactness assertion to choose a compact surjective étale atlas of
its presheaf fibre. `FibreRestrictionAtlas.of_original` gives this same
underlying atlas scheme its induced structure over `T` and the appropriate
new chart. Compactness is unchanged because the underlying scheme is
identical. The chosen atlas together with its compactness proof is retained
as data. `IsQuasiCompactMorphism.baseChangeMap` extracts the required
compact atlas from this construction.

For `IsUniversallyClosedMorphism.baseChangeMap`, the actual fibre point
homeomorphism identifies the tested fibre over `T` with the same fibre
viewed over `S`. The represented target-scheme point homeomorphism
identifies the target point spaces. The proved projection compatibility
expresses the new projection as the composite of the fibre homeomorphism,
the old closed projection and the inverse target homeomorphism. Each
homeomorphism is closed, so this composite is closed. This proves the
published universal-closedness predicate for every test scheme over `T`.

For `HasGeometricallyConnectedFibres.baseChangeMap`, a test over `T` with
field `K` and structure map `s : Spec K → T` is viewed over `S` with
structure map `s ≫ g` and the same Yoneda section. The actual fibre point
homeomorphism transfers the original `ConnectedSpace` instance to the
new fibre. This retains nonemptiness as required by the published
`ConnectedSpace` convention.

`IsProperMorphism.baseChangeMap` combines these results for quasi-compactness
and universal closedness with the already proved preservation of
separatedness and local finite type. Its conclusion is exactly the
published four-part properness predicate.

The provenance is internal: these are composite proofs from the actual
fibre homeomorphism and common-atlas construction, the definitions of the
morphism predicates, and the existing scheme-base-change results. No
external mathematical assertion is assumed. This unit establishes
preservation under base change, not eventual descent from a limit; the
remaining clauses of `SpaceLimitPropertyDescentStatement` remain open.
