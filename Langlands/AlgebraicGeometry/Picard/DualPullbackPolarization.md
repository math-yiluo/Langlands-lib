# Actual dual pullback of relative polarizations

This internal CM comparison construction works over an arbitrary scheme
`S : Scheme.{u}`. It uses the published actual contravariant dual homomorphisms
and the canonical Poincare-compatible dual base-change comparisons. Its
pullback-tensor, Mumford Picard-zero, universal base-change, Picard-zero
pullback, composition, unit, associativity, comparison, symmetry, chosen dual
geometry, and inverse-evaluation prerequisites remain explicit. It assumes no
new compatibility equation for the dual comparison.

For `g : Y ⟶ X` and any scheme classifier `fX : X.X ⟶ dualScheme X hX`,
`dualBaseChangeMap_dualPullback` identifies the canonical base change of the
actual composite `g; fX; g^vee` with the actual composite of the changed `g`,
the canonical changed `fX`, and the actual dual of the changed `g`. The proof
expands `dualBaseChangeMap`, maps the two compositions through the actual
scheme pullback functor, and applies the published
`dualSchemeMap_dualSchemeBaseChangeIso`. The underlying base-changed
homomorphism is definitionally the corresponding scheme pullback map.

`isAffineHom_baseChange_map` applies stability of affine morphisms under
base change to that underlying map. Consequently
`hasAmpleMumfordAfterBaseChange_dualPullback` first rewrites by the actual
classifier equality and then applies the published affine transport theorem
`hasAmpleMumfordPresentation_dualPullback` to the changed homomorphism.
`hasFieldAmpleMumfordPresentation_dualPullback` retains the original
presentation's field extension, its field structure, and its ring map, and
uses this transport over that same extension. These presentation lemmas
require only affineness of `g`, with no isogeny or dual-isogeny hypothesis.

`isPolarization_integralDualPullbackHom` considers an actual homomorphism
`g : A ⟶ B`, its actual contravariant dual between the constructed dual
abelian schemes, and a supplied relative polarization `lamB` on `B`.
It assumes explicitly that both `g` and its actual dual are isogenies, in
the finite-flat-surjective sense. It proves that the published actual
integral composite `integralDualPullbackHom ... g lamB`, namely
`g; lamB; g^vee`, satisfies `IsPolarization` on `A`.

The isogeny part follows by composing the three supplied isogenies.
Finiteness of `g` implies affineness, which persists on every geometric
fibre. For each algebraically closed geometric-fibre field, the original
polarization supplies a field ample Mumford presentation after an extension.
The canonical classifier equality and the field transport lemma give the
required presentation on the changed `A`. Thus the proof uses exactly the
two conjuncts of the published `IsPolarization` definition; it requires no
chosen relative ample bundle on the original base.

`dualPullbackPolarization` bundles this proved polarization as a subtype
whose value is literally `integralDualPullbackHom ... g lamB`. It neither
changes the supplied maps nor chooses a substitute dual comparison.

The provenance is internal: the new proof combines published canonical dual
naturality, affine ample-Mumford transport, and stability of isogenies under
composition. Isogeny of the map and of its dual are explicit premises here;
this module does not derive them from a rational isomorphism. It does not
construct a representing scheme or prove the division-case CM
representability statement.
