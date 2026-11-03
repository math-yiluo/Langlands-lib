# Proper formal line-bundle effectivity over complete local rings

`ProperFormalLineBundleEffectivityStatement.{u}` is the proposition that
every compatible system of actual line bundles on the maximal-ideal
thickenings of a proper scheme over a complete local noetherian ring
has an actual line-bundle algebraization.

Precisely, the base is any commutative ring `R : Type u` with
`IsNoetherianRing R`, `IsLocalRing R`, and
`IsAdicComplete (IsLocalRing.maximalIdeal R) R`. Write `m` for the
maximal ideal. For every scheme `X : Scheme.{u}` and proper morphism
`f : X → Spec R`, the system consists of actual locally free rank-one
module sheaves on
`X_n = X ×[Spec R] Spec (R / m^(n+1))`, with specified isomorphisms
from the ordinary pullback of the next sheaf to the current sheaf.
Natural numbers start at 0.

The conclusion is an actual `L : LineBundle X` and a
`FormalLineBundleSystem.Comparison` from its ordinary restriction
system to the given system. Its component isomorphisms commute with
every transition, as required by
`FormalLineBundleSystem.IsAlgebraization`. Separate unrelated
isomorphisms on the individual thickenings are insufficient.

The source is the Stacks Project, Proposition 30.25.4 (Tag 088C) and
Section 30.27, Remark 30.27.2 (Tag 0CYW), retained as
`stacks-formal-line-bundle-effectivity-2026-11-03` at
`literature/Stacks Project - Grothendieck existence and compatible formal
module systems (2026-11-03)/088C.html` and `0CYW.html`.
Proposition 30.25.4 gives the completion equivalence for coherent
module sheaves on a proper scheme over a noetherian ring complete for
an ideal. Remark 30.27.2 describes the equivalent actual system on
the scheme thickenings, with its ordinary-pullback isomorphisms;
the support restrictions disappear for a proper scheme.

The statement here is a derived rank-one specialization, with the
completion ideal restricted to the maximal ideal of a local ring.
The source's coherent existence theorem must be supplemented by a
proof that the coherent algebraization of a compatible rank-one
system is locally free of rank one. The local freeness near the
closed fibre and its extension over the whole proper scheme remain
part of the proof obligation. This file defines the proposition; it
does not prove either coherent existence or this specialization.

There is no projectivity, smoothness, flatness, residue-field, or
characteristic restriction. The conclusion asserts existence of a
compatible algebraization. Full faithfulness of completion and
smooth-chart construction are separate obligations.
