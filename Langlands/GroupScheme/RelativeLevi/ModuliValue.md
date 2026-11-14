# Relative Levi subgroup images and conjugation

Author: Worker 179.

This definition module constructs the values of the relative Levi moduli problem
over a fixed base and their actual conjugation actions. It does not construct the
contravariant restriction maps on changing the base, a representing scheme, a
torsor, or any global Levi subgroup.

`RelativeLevi.IsLeviImage F` means that `F` is the all-test image of an actual
homomorphism `l : L → P` satisfying the existing `IsRelativeLeviSubgroup l`.
`RelativeLevi.LeviImage P` is the subtype of such subgroup functors. Equality is
equality of the image subgroup functors on every scheme test; no presenting group
scheme is part of the equality. `LeviImage.ofHom` and
`LeviImage.exists_presentation` give the two directions of this description.

All schemes and group schemes have the same arbitrary universe `u`. The type of
images is in `Type (u+1)` because an image is tested on all `u`-small schemes.
This uses no resizing assumption and does not enlarge the geometric objects.

The two ambient-isomorphism helpers preserve the original radical and Levi
predicates. The radical proof transports each geometric-fibre radical through
the actual pulled-back ambient isomorphism. The Levi proof also postcomposes its
multiplication isomorphism by that isomorphism. `LeviImage.mapIso` transports
the image via inverse image under the inverse ambient isomorphism.

`conjugateImage` conjugates each subgroup of points by the restriction of an
actual base point. Its naturality follows from `constantPoint_conj_naturality`.
The lemma `conjugateImage_range` identifies it with the range of the actual
inclusion followed by `innerIso`. Thus `LeviImage.conjugate` preserves the Levi
condition, and `LeviImage.conjugationAction r` is a proved group action of the
base points of any supplied `r : U → P`. For a supplied relative unipotent
radical it is exactly that radical's conjugation action. The identity and
multiplication laws are proved on all subgroup functors, using the group laws
on points. No existence, uniqueness or transitivity theorem is assumed.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Definition 5.4.2 on printed/PDF page 174 defines the values of `Lev(P)` as Levi
subgroups after base change. Corollary 5.4.6 on page 178 uses the radical's
conjugation action. The image subtype and the isomorphism helpers are internal
implementations of these values and of this action; this module does not assert
the representability or torsor theorem of that corollary. The original source
states this moduli problem for a parabolic in a reductive group. The definitions
here are available for any `P` with the existing relative-Levi predicate; the
eventual geometric theorem must retain the parabolic and reductive hypotheses.

Shared declarations `IsRelativeUnipotentRadical.comp_iso`, `IsRelativeLeviSubgroup.comp_iso` are imported from `Langlands.GroupScheme.RelativeLevi.AmbientTransport`; their mathematical hypotheses, conclusions and data are unchanged.
