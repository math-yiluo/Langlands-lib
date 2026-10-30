# Cotangent base change at the identity

`Langlands.GroupScheme.cotangentBaseChangeIsIso` proves the published
proposition `Langlands.GroupScheme.CotangentBaseChangeIsIsoStatement S`
for every `S : AlgebraicGeometry.Scheme.{u}`. Its complete theorem type is

```text
(S : AlgebraicGeometry.Scheme.{u}) : CotangentBaseChangeIsIsoStatement S.
```

Thus for every scheme `T`, morphism `b : T ⟶ S`, and actual group scheme
`G : Langlands.GroupScheme S`, the conclusion is
`IsIso (Langlands.GroupScheme.cotangentBaseChangeMap b G)`.
All schemes lie in a common arbitrary universe. There are no smoothness,
flatness, finiteness, commutativity, or supplied comparison hypotheses.
The target statement and its imported constructions are unchanged.

Write `G_T = (GroupScheme.baseChange b).obj G`, let `e_T` be its identity
section, and let `q = Limits.pullback.fst G.X.hom b`. The canonical map has
source `(Scheme.Modules.pullback b).obj G.cotangentAtIdentity` and target
`G_T.cotangentAtIdentity`. Its definition in `LieBaseChange` is the composite
of the component of `cotangentBaseChangePullbackIso b G` at
`relativeDifferentials G.X.hom` and the image of
`relativeDifferentialsBaseChangeMap G.X.hom b` under pullback along `e_T`.
The first factor identifies the two pullbacks to the new identity section,
using `e_T ≫ q = b ≫ G.identitySection`.

The proof instantiates the published unconditional theorem
`Langlands.Scheme.relativeDifferentialsBaseChangeIsIso`, imported from
`Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeIsIso`, at
`S`, `G.X.left`, `T`, `G.X.hom`, and `b`. This provides the local `IsIso`
instance for the concrete differential comparison. It then converts that
map to an isomorphism with `asIso` and applies the identity-section pullback
functor's `mapIso`. Composing with the component of
`cotangentBaseChangePullbackIso` gives an isomorphism whose hom is
definitionally `cotangentBaseChangeMap b G`. `Iso.isIso_hom` proves the
required invertibility. The two elaboration transparency settings agree
with the canonical comparison construction.

This is a derived categorical consequence of the published differential
base-change theorem. Its source assertion is Stacks Project Lemma 29.33.10
(tag [01V0](https://stacks.math.columbia.edu/tag/01V0)), with the canonical
map characterized in Lemma 29.33.8
(tag [01UV](https://stacks.math.columbia.edu/tag/01UV)). The originals and
their proofs occur in `01UM.html`, lines 321–371, of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, directory content
SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
The implementation pulls the established differential isomorphism back
along the identity section and uses the existing pullback coherence
isomorphism; it makes no new affine comparison or gluing argument.

The result concerns the cotangent module at the identity. Lie base change
additionally needs the separate dual-pullback comparison and hypotheses
ensuring its invertibility.
