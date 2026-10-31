# Naturality of the actual cotangent base-change comparison

This module gives Prop-valued statement definitions for an internal coherence
property of the published constructions in `LieFunctor` and `LieBaseChange`.
It introduces no new cotangent or base-change map and proves none of these
propositions.

For an arbitrary scheme `S : Scheme.{u}`,
`Langlands.GroupScheme.CotangentBaseChangeNaturalityStatement S` quantifies,
in order, a scheme `T : Scheme.{u}`, a morphism `b : T ⟶ S`, group schemes
`G,H` over `S`, and an actual group-scheme homomorphism `f : G ⟶ H`.
The universe `u` is arbitrary. Put `G_T = (GroupScheme.baseChange b).obj G`
and similarly for `H_T`. With `C_G = G.cotangentAtIdentity` and similarly
for the other groups, the four actual arrows are:

| Lean expression | Source | Target |
| --- | --- | --- |
| `(pullback b).map (GroupScheme.cotangentMap f)` | `b* C_H` | `b* C_G` |
| `GroupScheme.cotangentBaseChangeMap b G` | `b* C_G` | `C_(G_T)` |
| `GroupScheme.cotangentBaseChangeMap b H` | `b* C_H` | `C_(H_T)` |
| `GroupScheme.cotangentMap ((GroupScheme.baseChange b).map f)` | `C_(H_T)` | `C_(G_T)` |

The statement equates the first two arrows composed in order with the last
two arrows composed in order. Both sides are morphisms of actual module
sheaves on `T`, from `b* C_H` to `C_(G_T)`. The direction reflects the
contravariance of the cotangent differential. The comparison map is the
published identity-section pullback comparison followed by the pullback of
the actual relative-differentials base-change map.

`Langlands.AbelianScheme.CotangentBaseChangeNaturalityStatement S` has the
same telescope with abelian schemes `A,B` and a homomorphism `f : A ⟶ B`.
It uses `AbelianScheme.groupHom f`, `A.toGrp`, `B.toGrp`, and
`AbelianScheme.groupHom ((AbelianScheme.baseChange b).map f)` explicitly.
Thus it is the actual abelian-scheme specialization of the group-scheme
square. The existing forgetful maps and base-change constructions give
the same underlying group objects and homomorphisms.

`Langlands.CotangentBaseChangeNaturalityStatements S` is the conjunction
of these two propositions, in the preceding order. It supplies one exact
proof target covering the general square and its specialization.

## Provenance and proof obligation

These are derived compatibility statements for existing Library
definitions. Their provenance is the definitions of `cotangentMap`,
`identityPullbackIso`, `cotangentBaseChangeMap`, and
`cotangentBaseChangePullbackIso`, together with the canonical
relative-differentials maps and module-pullback coherence used by those
definitions. No new assertion is attributed to original literature here.
The missing proof must establish compatibility of those actual comparison
maps with the differential of `f`; naturality is not supplied as construction
data or as a premise.

The group-scheme statement imposes no smoothness, commutativity, flatness,
finite-presentation or other extra geometric condition. The abelian
specialization uses the existing abelian-scheme bundle and imposes no extra
condition on either base scheme or on `b`. Invertibility is not required
to formulate either cotangent square.

Worker 208 authored these statements and their explanation.
