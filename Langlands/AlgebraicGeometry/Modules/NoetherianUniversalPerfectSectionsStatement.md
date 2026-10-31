# Universal perfect sections over a noetherian base

Author: Worker 137.

`NoetherianUniversalPerfectSectionsStatement.{u}` is the noetherian-base
specialization of the published `UniversalPerfectSectionsStatement.{u}`.
For an arbitrary universe-`u` commutative ring `R` with
`IsNoetherianRing R`, a smooth proper morphism `f : X ⟶ Spec R`, and an
actual line bundle `L` on `X`, it asks for one integer-indexed complex
`K` of `R`-modules satisfying
`IsUniversalPerfectSectionsRepresentative f L.obj K`.

The published representative predicate requires three conclusions:
`K` is bounded with finite projective terms; its image in the derived
category is isomorphic to actual derived `R`-module sections of `L.obj`;
and, for every commutative ring `T` in the same universe and every ring
map `φ : R ⟶ T`, the ordinary degreewise scalar extension of that same
`K` is isomorphic to actual derived `T`-module sections of the ordinary
pullback of `L.obj`. The latter sections use the base-changed structure
map `pullback.snd f (Spec.map φ)` and coefficient projection
`pullback.fst f (Spec.map φ)`. Both the original-base comparison and
every scalar comparison are expressed by `Nonempty`.

Only `R` is assumed noetherian. The scalar rings `T` remain arbitrary.
The existential complex precedes every scalar extension, and no
comparison with actual derived sections is supplied as a premise.
The proposition asserts no naturality or compatibility among chosen
isomorphism witnesses.

This is an internal specialization of the published existence target,
using its unchanged actual module, derived section, strict perfection,
and scalar-extension definitions through the published representative
predicate. It isolates the noetherian geometric case for a separate
proof and subsequent descent assembly. Defining this proposition does
not prove either the noetherian case or the unrestricted target.
