# Gluing actual line bundles on an arbitrary scheme open cover

This is a derived construction from the Library's actual module-sheaf gluing
and its definition of a line bundle. It packages no additional mathematical
assumption beyond the specified descent datum.

For `X : Scheme.{u}` and any `𝒰 : X.OpenCover.{u}`,
`LineBundleGluingData 𝒰` consists of a line bundle on each cover member and
module-sheaf isomorphisms on every ordered pairwise scheme pullback. Its
`cocycle` is exactly the published module-gluing cocycle
`Langlands.Scheme.Modules.OpenCoverModuleGluing.CocycleCondition`: it compares
the two composites on triple scheme pullbacks using the canonical
`squarePullbackIso` comparisons. It includes repeated indices. The construction
does not infer coherence from the mere existence of pairwise isomorphisms.

`LineBundleGluingData.gluedModule` is the multiequalizer module constructed in
`Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof`.
`moduleIso` uses that module's proved comparison isomorphisms with the given
pieces. `moduleIso_compatible` retains their proved agreement with the original
transition maps.

Local rank one uses the published
`IsLocallyFreeRankOne.exists_of_pullback` from
[`RigidifiedClassesZariskiGluingProof`](RigidifiedClassesZariskiGluingProof.md).
It transports a trivializing neighborhood through the open immersion's
isomorphism with its open range. The theorem concerns arbitrary scheme modules
and open immersions and has no abelian-scheme or rigidification hypothesis.
`rankOne_of_cover` chooses a cover member above each point and applies it.

Consequently `gluedModule_rankOne` proves the defining local condition for the
glued module, `glue` is an actual `LineBundle X`, and `iso i` identifies its
actual line-bundle pullback with the input piece. There are no Noetherianity,
separation, integrality or quasi-compactness hypotheses. The index type and
schemes use the same arbitrary universe `u`; no smallness claim about the
category of all line bundles is made.

This construction supports the local-to-global part of open-immersion extension.
It does not construct local extensions or prove the general extension statement:
applications must still supply a coherent descent datum covering the target.
