# Finiteness of a generated ample linear system on a proper scheme

`fibrePullbackLineBundleTrivialization f L y` is an isomorphism from the
restriction of `f*L` to the scheme-theoretic fibre of `f` at `y` to that
fibre's structure sheaf. It first identifies the two consecutive pullbacks
with pullback along the composite. The fibre square factors the composite
through `Spec κ(y)`. `fieldLineBundleTriviality` supplies a trivialization of
the pullback of `L` to `Spec κ(y)`; the construction pulls that isomorphism
back to the fibre and then uses `pullbackUnitIso`. No closedness assumption on
`y` is needed. The trivialization is chosen, not canonical.

`isFinite_of_isAmple_pullback` proves that a proper morphism `f : X ⟶ Y`
is finite if some line bundle `L` on `Y` has ample pullback to `X`. The
residue-field map `Spec κ(y) ⟶ Y` is affine: the inverse image of an affine
open is either the whole field spectrum or empty. By base change the fibre
inclusion is affine, so the ample pullback restricts to an ample bundle on
the fibre. This restriction is trivial by the isomorphism above. Each fibre
is proper over `Spec κ(y)` and hence finite by `properAmpleTrivialFinite`.
The proper, locally quasi-finite criterion for finiteness then applies.

`isFinite_linearSystemMap_of_isAmple` applies this argument to the map to
projective space associated with a finite generating family of sections of
an ample line bundle on a proper scheme over a field. The map is proper
because its composite with the separated structure morphism of projective
space is the given proper map. The line bundle in the first argument is
`O(1)` on projective space. `linearSystemTwistIso` identifies its pullback
with the input line bundle, so `ampleIso` supplies ampleness. The result is
finiteness, not closed immersion, and does not require a complete basis.

This is an internal auxiliary construction from the Library's fibre,
line-bundle pullback and projective twist comparisons. The finiteness
criterion is Mathlib's `IsFinite.iff_isProper_and_locallyQuasiFinite`.
