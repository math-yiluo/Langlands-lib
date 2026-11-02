# Gluing factorizations through a scheme monomorphism

`Langlands.AlgebraicGeometry.exists_lift_of_openCover` states that a scheme
morphism `f : X ⟶ Y` factors through a monomorphism `i : Y′ ⟶ Y` if it
factors through `i` on every member of an open cover of `X`. All schemes
have an arbitrary common universe; no affineness or separation is assumed.

Choose the local factorizations. Their composites with `i` agree on each
overlap by the pullback equation. Cancellation of the monomorphism makes
the factorizations agree, so `Scheme.Cover.glueMorphisms` glues them.
The cover's morphism extensionality proves that the glued map composes
with `i` to give `f`.

This is the existing proof relocated from
[dynamic closed subgroups](../../GroupScheme/Dynamic/ClosedSubgroup.md),
where it was named `Langlands.GroupScheme.exists_lift_of_openCover`.
Both that module and the
[open extension of an étale equivalence relation](../EtaleEquivalenceRelationOpenExtension.md)
reuse this single generic result. The statement and proof are unchanged;
the shared module imports only Mathlib's scheme gluing infrastructure.
