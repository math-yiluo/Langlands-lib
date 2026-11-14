# Étale-local maximal tori in relative Levi subgroups

This internal construction works over an arbitrary scheme `S` in every
universe `u`. Its inputs are a reductive group scheme `G`, a relative
parabolic inclusion `i : P ⟶ G`, and a relative Levi inclusion `l : L ⟶ P`.
The entire proposition `EtaleLocalMaximalTorusExistenceStatement.{u}` remains
an explicit input.

`exists_etaleMaximalTorusCover` supplies an étale cover of `S`, indexed in
universe `u`. On each member there is an actual commutative group scheme `T`
with relative torus structure and a closed inclusion `t` into the pulled-back
Levi `L`. This inclusion is maximal on every residue-field fibre of the
cover member. The composite of `t` with the actual pullback of `l` is also
closed and maximal on every residue-field fibre of the pulled-back
parabolic `P`.

The proof first derives `IsReductive L` using
`IsRelativeLeviSubgroup.isReductive`. It applies the supplied maximal-torus
existence proposition to this actual `L`. Each covering morphism is étale,
so `IsRelativeLeviSubgroup.baseChange_etale` gives the full relative Levi
predicate for the pullback of `l`. Affineness of the parabolic is part of
its relative parabolic predicate and persists under pullback.
`IsFibrewiseMaximalTorus.comp_relativeLevi` then proves ambient maximality;
composition of closed subgroup inclusions proves ambient closedness.
No additional base-change stability premise is required.

`etaleMaximalTorusCover` chooses the cover and, on every member, an actual
torus and inclusion with all five properties above. It returns these data
as a dependent sum and subtypes. Containment of the ambient torus in the
pulled-back Levi follows directly from the composite inclusion by
`SubgroupFunctor.range_comp_le`.

The provenance is derived from the relative Levi reductivity, étale
transport, and maximality lemmas and the explicitly supplied torus-existence
proposition. This contribution does not prove that proposition, construct
global maximal tori, or prove the unchanged relative Levi conjugacy target.
