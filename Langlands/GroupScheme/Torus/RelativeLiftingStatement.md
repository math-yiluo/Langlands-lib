# Lifting a split torus from a residue fibre

`Langlands.GroupScheme.RelativeSplitTorusLiftingStatement.{u}` states a
relative subgroup-lifting result over every scheme in universe `u`.
The ambient group scheme is smooth and affine over its base. There is no
Noetherian, reducedness, characteristic, or connected-fibre hypothesis.

For a point `s` of `S`, the input consists of an actual group scheme `T₀`
over `Spec κ(s)`, a proof that it is a split torus in the published sense
`IsSplitTorus`, and an actual group-scheme homomorphism
`i₀ : T₀ ⟶ G_{κ(s)}` whose underlying scheme morphism is a closed immersion.
The fibre is exactly `GroupScheme.baseChange (S.fromSpecResidueField s)`.

The conclusion supplies a scheme `U`, an etale map `p : U ⟶ S`, and a map
`b : Spec κ(s) ⟶ U` with `b ≫ p = S.fromSpecResidueField s`. Thus this is a
pointed etale neighbourhood with no residue-field extension: the point lies
above `s` and its residue field is identified with `κ(s)`. Indeed, the
residue-field map at this point is finite separable by etaleness, and the
map induced by `b` is a retraction to `κ(s)`, so that field extension is
trivial. Surjectivity of `p` onto all of `S` is not asserted.

Over `U` the conclusion supplies an actual split torus `T`, an actual closed
group-scheme inclusion `i : T ⟶ G_U`, and an actual isomorphism
`e : T_b ≅ T₀`. The final equality says that pulling back `i` along `b`,
identifying the iterated ambient pullback with the pullback along `b ≫ p`
using `(baseChangeCompIso p b G).inv`, and then using the equality of base
maps, gives exactly `e.hom ≫ i₀`. It therefore recovers the given subgroup
embedding, including its map into the given residue fibre. An abstract
isomorphism of fibre groups alone would not express this conclusion.

## Source and provenance

The registered original source is Brian Conrad, *Reductive group schemes*
(2014 SGA3 notes), source ID `conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
readable at
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`.
Proposition 3.1.6, printed/PDF pp.83–84, lifts a multiplicative-type subgroup
to a residually trivial etale neighbourhood and recovers it inside the
original fibre. The paragraph following that proposition explains why the
subgroup embedding is closed. The proof of Corollary 3.1.8, printed/PDF p.85,
then passes to an etale neighbourhood to make that subgroup split and uses
the torus fibre to see that its character group is free. No Conrad-specific
errata note was found in the supplied local indices.

This statement is a derived split-torus specialization with a pointed
splitting refinement, rather than a literal encoding of the more general
multiplicative-type proposition. To retain the original residue field when
making the lift split, use the isomorphism sheaf from the constant split
torus of the given rank to the lifted torus. It is an etale sheaf represented
by an etale scheme, and the split special fibre supplies a `κ(s)`-point.
Taking an etale neighbourhood of that point gives the required pointed
refinement. The displayed isomorphism and commuting square encode the
source's recovery of the subgroup as an actual subgroup of the fibre.
This refinement and all the lifting existence assertions remain proof
obligations of this proposition; no relative lifting theorem is assumed by
the definition.

## Status and consumer

This file defines a proposition. It does not prove that proposition or
openness of the reductive identity-component locus. It isolates the
split-torus lifting input in Conrad's proof of Proposition 3.1.9(1),
printed/PDF pp.85–88. Any consumer must establish it from the stated
hypotheses and use its actual inclusion comparison when identifying the
resulting torus in a geometric fibre.
