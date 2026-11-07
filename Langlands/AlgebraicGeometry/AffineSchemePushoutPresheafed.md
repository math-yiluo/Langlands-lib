# A presheafed-space pushout criterion

This internal construction combines a topological pushout with a pullback of
pushed presheaves. It is used in the affine scheme pushout proof, but its input
spaces are arbitrary presheafed spaces with values in `CommRingCat`.
The ring universe `u` and topological-space universe `v` are independent.

Let `f : W ⟶ X`, `g : W ⟶ Y`, `i : X ⟶ Z`, and `j : Y ⟶ Z` be actual
presheafed-space morphisms, with `w : f ≫ i = g ≫ j`. Assume that their
underlying continuous maps form a pushout. Push all source presheaves onto `Z`.
`firstPresheafMap` is the pushforward along `i.base` of `f.c`, with target
`(f.base ≫ i.base)_* W.presheaf`. `commonPresheafMap w` pushes `g.c` along
`j.base` and uses the equality of composite continuous maps obtained from `w`
to identify its target with that same common presheaf.

The other hypothesis is the categorical pullback square with point
`Z.presheaf`, legs `i.c` and `j.c`, and outgoing maps `firstPresheafMap` and
`commonPresheafMap w`. Both hypotheses remain explicit inputs. The module does
not establish them for spectra.

`presheafedPushoutIsColimit w hT hS` constructs a colimit witness for the
actual cocone `PushoutCocone.mk i j w`. To construct its descent morphism to
an arbitrary compatible cocone `s`, first use the topological pushout to obtain
`presheafedPushoutBase hT s`. The two topological factorization equations
identify the pushed presheaves with the presheaves appearing in `s.inl.c` and
`s.inr.c`. Composing with these identifications defines
`presheafedPushoutFst` and `presheafedPushoutSnd`.

Their compatibility follows from the equality of presheafed-space composites
in `s`, naturality of the section maps, and composition of restriction maps.
The equality transports are morphisms in the opposite category of opens;
this category is thin, so the resulting parallel transports agree.
Pushforward of presheaves is precomposition and preserves pullbacks.
The pulled-back universal property therefore lifts the two compatible maps
uniquely to a morphism into the pushforward of `Z.presheaf`. This supplies
`presheafedPushoutDesc` and its two factorization equations.

For uniqueness, `presheafedPushout_hom_ext` first identifies the base continuous
maps by the topological pushout. With the bases equal, pullback uniqueness
identifies the two presheaf maps. These constructions give the colimit witness
and the theorem `isPushout_presheafedSpace`. Its target is the full category of
presheafed spaces in the stated universes; no affine or sheaf condition is
imposed on the test object.

This is derived internal infrastructure. The proof uses Mathlib's existing
pushout and pullback universal properties, its definition of presheafed-space
morphisms, naturality, equality-induced pushforward isomorphisms, and limit
preservation by precomposition. The auxiliary inverse-component formula for
`pushforwardEq` and the pushforward pullback-preservation instance make those
standard constructions available with the precise presheaf category instances.
The result introduces no additional external mathematical assertion.
