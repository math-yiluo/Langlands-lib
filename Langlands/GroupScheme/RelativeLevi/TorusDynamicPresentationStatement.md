# Statement: local dynamic presentations along a prescribed maximal torus

Worker 592.

`Langlands.GroupScheme.RelativeTorusDynamicPresentationStatement.{u}` is a
`Prop`-valued statement definition. This module supplies no proof.

For every scheme `S`, reductive group scheme `G`, relative parabolic
`i : P ⟶ G`, commutative group scheme `T`, and homomorphism `t : T.toGrp ⟶ P`,
assume that `T` is a relative torus, that `t` is a closed subgroup, and that
`t` is maximal on every residue-field fibre of `P`. These are exactly the
hypotheses of `RelativeTorusLeviStatement`.

The conclusion gives an étale `Scheme.Cover` of `S`. On each member of the
cover there is a cocharacter `nu` of the pulled-back prescribed torus.
The pulled-back inclusion `i` represents the dynamic parabolic of the
composite of `nu`, the pulled-back `t`, and the pulled-back `i`.
Representation includes monomorphy and equality of subgroup functors on
all test schemes, including nonreduced tests. It asserts neither a global
cocharacter nor a global dynamic presentation.

## Provenance

This is the local presentation input used in Brian Conrad, *Reductive
group schemes* (2014), the proof of Proposition 5.4.5 on p.177, derived
from Proposition 5.2.3 on p.152. The registered source is
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Page numbers here are one-based PDF pages and agree with the printed
pages.

Proposition 5.2.3 gives a Zariski-local dynamic presentation when the
given maximal torus and ambient reductive group form a split pair. Its
proof first observes that a maximal torus of a parabolic is also maximal
in the ambient reductive group, and then passes étale-locally to a split
pair. Applying the same reduction to the prescribed `T` gives the cover
in this statement. The proof of Proposition 5.4.5 applies this reduction
with its prescribed torus and then chooses its defining cocharacter in
that torus.

The fieldwise maximality and relative-torus conventions agree with those
explained in [TorusLeviStatement](TorusLeviStatement.md): residue-fibre
maximality agrees with geometric maximality by Conrad's Remark A.1.2,
and relative tori are étale forms of finite split tori. No splitness,
reducedness, affineness of `S`, or supplied cocharacter is added to the
hypotheses.

## Role in the proof

The conclusion concerns dynamic parabolics alone. It does not assert
existence or uniqueness of a Levi subgroup. Together with dynamic Levi
structure, comparison of relative radicals, and effective gluing of the
unique local Levi containing the torus, it is an input to the separate
torus-Levi theorem.
