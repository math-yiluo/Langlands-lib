# Cotangent modules at the identity under base change

Let `S` and `T` be arbitrary schemes in a common universe, let `b : T ⟶ S`,
and let `G : Langlands.GroupScheme S`. Write `G_T` for
`(Langlands.GroupScheme.baseChange b).obj G`, `e` and `e_T` for their
identity sections, and `q : G_T.X.left ⟶ G.X.left` for
`Limits.pullback.fst G.X.hom b`. The scheme underlying `G_T` is the
actual categorical fiber product, with structure map `pullback.snd`.

`Langlands.GroupScheme.identitySection_baseChange_fst b G` proves
`e_T ≫ q = b ≫ e`. Its implemented proof unfolds the unit of the
pullback group object: it is the monoidal unit comparison followed by
the pullback of the original unit. Mathlib identifies the underlying
unit comparison with the inverse of `pullback.snd (identity S) b`.
The pullback projection formula and its commutative square then give
the equality. The reassociated equality is also available to simplification.

`cotangentBaseChangePullbackIso b G` is an isomorphism of functors
from modules on `G.X.left` to modules on `T`:

`pullback e ⋙ pullback b ≅ pullback q ⋙ pullback e_T`.

It composes the actual module pullback composition isomorphism,
the transport along `e_T ≫ q = b ≫ e`, and the inverse of the
pullback composition isomorphism on the other side. Thus it identifies
`b*(e*M)` with `e_T*(q*M)` for every module sheaf `M` on `G`.

`cotangentBaseChangeMap b G` is the canonical module morphism

`(pullback b).obj G.cotangentAtIdentity ⟶ G_T.cotangentAtIdentity`.

It first applies that functor isomorphism to the actual relative
differential sheaf `relativeDifferentials G.X.hom`, and then applies
`pullback e_T` to the canonical differential comparison
`relativeDifferentialsBaseChangeMap G.X.hom b`. This is an actual
morphism of `O_T`-modules built from the published differential and
cotangent constructions; no comparison morphism or invertibility
witness is supplied as input. No smoothness, flatness, finite presentation,
commutativity, or other geometric hypothesis is imposed.

## Provenance

This unit derives the identity-cotangent comparison from the canonical
relative-differential comparison of Stacks Project Lemma 29.33.8
(tag 01UV), specialized to the fiber-product square in Lemma 29.33.10
(tag 01V0). Both occur in `01UM.html` of registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
Lemma 29.33.16 (tag 0474) in that source identifies the cotangent module
along a section with the pullback of relative differentials, explaining
the connection with the existing `cotangentAtIdentity` definition.
The group-object identity-section equality and the functor isomorphism
are derived categorical consequences, with their explicit implementation
explained above; they are not separate claims quoted from Stacks.

The implementation uses Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`CategoryTheory/Monoidal/Cartesian/Over.lean` supplies the monoidal unit
comparison for pullback; `CategoryTheory/Comma/Over/Pullback.lean`
supplies the pulled-back unit morphism and its projection;
`AlgebraicGeometry/Modules/Sheaf.lean` supplies `pullbackComp` and
`pullbackCongr`. The imported project `RelativeDifferentialsBaseChange`
supplies the canonical differential map and its local characterization.

## Scope

This file constructs the cotangent comparison and proves the
identity-section compatibility needed to define it. It does not prove
that the differential or cotangent comparison is invertible, nor does
it construct a Lie base-change isomorphism. The unconditional
cotangent isomorphism consequence of tag 01V0 is a separate statement
and proof obligation. Passing from cotangent to Lie also requires the
canonical dual-pullback comparison and appropriate hypotheses for its
invertibility.
