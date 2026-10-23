# Canonical group-scheme fibre comparison

This is derived categorical infrastructure for actual scheme pullbacks, with no
claim that a separate theorem of the literature is being formalized.
The construction uses `GroupScheme.baseChange` and Mathlib's lift of natural
transformations between cartesian monoidal functors to group objects.

For an arbitrary scheme `S`, group scheme `G` over `S`, slice morphism
`h : T ⟶ U`, and scheme morphism `s : V ⟶ T.left`, `fibreComparison G h s`
is a group-scheme morphism over `V` from `s*(T*G)` to `(s ≫ h.left)*(U*G)`.
All schemes are in one arbitrary universe. No smoothness, commutativity,
connectedness, or restriction on the base maps is assumed.

The underlying map is constructed by two pullback lifts: its coordinates in
`G` and `V` are the original projection to `G` and the original projection to
`V`. The coordinate in `U` is the projection to `V` followed by `s ≫ h.left`.
The slice equation `h.left ≫ U.hom = T.hom` makes these coordinates compatible.
These maps form a natural transformation of the iterated slice pullback functors.
Automatic monoidality in cartesian categories and `Functor.mapGrpNatTrans`
produce the actual group homomorphism; `Functor.mapGrpCompIso` identifies
lifting a composite functor with composing the lifts.

`fibreComparison_fst` proves that the comparison followed by the two first
projections to `G` equals the original two first projections.
`fibreComparison_snd` proves that its projection to `V` is the original second
projection. The first proof simplifies the pullback lift equations; the second
is the structure equation of the resulting morphism in `Over V`.
Both lemmas also have generated reassociated versions for postcomposition.

This module does not construct an inverse or prove any Picard-zero statement.
