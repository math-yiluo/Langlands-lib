# Actual relative Hom and characters satisfy sheaf descent

Worker 616.

All declarations belong to `Langlands.GroupScheme.Cartier`, in every
universe `u`. For commutative group schemes `G` and `H` over an arbitrary
scheme `S`, this module constructs `relativeHomLocalNatEquiv` and proves
`isSheaf_relativeHomFunctor` for every subcanonical Grothendieck topology
on `Over S`. It specializes the result to actual Cartier characters and
the big relative étale topology.

## Objects and comparison

`RelativeHom G H T` is the published actual Hom group between the pullbacks
of `G` and `H` to the scheme `T.left`, for `T : Over S`. The functor
`relativeHomFunctor G H` and all its restriction maps are unchanged.

The comparison target is Mathlib's
`presheafHom (GroupScheme.points G.toGrp) (GroupScheme.points H.toGrp)`.
Its value at `T` is the type of natural transformations between the two
group-valued point functors restricted to `Over T`. Here `Over T` is an
iterated slice: objects are schemes over `S` equipped with a morphism to
`T`. This natural-transformation type lies in `Type (u + 1)`, whereas the
actual Hom group lies in `Type u`. The comparison is an equivalence of
those types, rather than an isomorphism between presheaves in a single
fixed category of types. The sheaf argument explicitly permits these
different universes.

For a relative homomorphism `χ` and a morphism `a : V ⟶ T`,
`relativeHomLocalPoints` lifts each original `G`-point over `V` to the
pullback over `T`, applies `χ`, and projects to an original `H`-point.
It is a group homomorphism. Its naturality follows from the published
pullback point comparisons. `relativeHomToLocalNatTrans` packages these
maps into the indicated natural transformation.

In the other direction, `localNatTransPoints` applies the given local
natural transformation to the canonical `T`-point of each scheme over
`T.left`, conjugating by the published pullback point equivalences.
The resulting natural family of group homomorphisms is recovered by
`homOfPoints`. Writing that actual group-scheme homomorphism additively
gives `localNatTransToRelativeHom`.

The two inverse identities are proved on points. The first uses the
pullback universal property; the second uses naturality along the
canonical comparison between the iterated test scheme and the original
one. `relativeHomLocalNatEquiv G H T` packages these maps and identities.
The auxiliary projection formula `relativeHomLocalPoints_left` states
that the resulting underlying point is obtained by a pullback lift,
followed by the actual scheme map of `χ` and projection to `H`.

`relativeHomToLocalNatTrans_restrict` proves compatibility with the
original relative Hom restriction maps. It uses that projection formula,
the published `restrict_fst` formula, and the pullback universal property.
Thus the naturality of the equivalence does not redefine restriction to
make it hold.

## Sheaf proof and scope

`isSheaf_relativeHomFunctor G H J` assumes only that `J` is subcanonical.
The point functor of `H` is a sheaf by the published
`LocalGroupIso.points_isSheaf`. Mathlib's `Presheaf.IsSheaf.hom` then makes
the natural-transformation presheaf a sheaf. The natural equivalence just
constructed transports this sheaf condition to the underlying
set-valued relative Hom presheaf, using
`Presieve.isSheaf_iff_of_nat_equiv`. The standard forgetful functor from
abelian groups reflects this sheaf condition, giving the abelian-valued
conclusion.

`isSheaf_characters G J` specializes `H` to the actual multiplicative
group scheme `Gm S`. `isEtaleSheaf_characters G` specializes the topology
to `Scheme.etaleTopology.over S`, the published
`EtaleLocalSystem.topology S`. Its subcanonicity follows from the
inequalities from the étale topology through the pro-étale topology to
the fpqc topology, Mathlib's fpqc subcanonicity, and subcanonicity of the
induced slice topology.

No normality, finite generation, multiplicative-type hypothesis,
representability of a Hom scheme, or local constancy is assumed.
In particular, the final theorem establishes the sheafness clause needed
for relative character local constancy; it does not establish the local
constant-model clause or normal-base isotriviality.

## Derived provenance

This is an internal construction from the published actual pullback
point equivalences, group-valued Yoneda recovery, relative Hom
restriction projection formulas and Mathlib's sheaf-Hom theorem.
No external source assertion or classification theorem is used. The
proof follows the implemented natural equivalence and its inverse laws.
