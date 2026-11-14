# Étale base change of relative Levi subgroups

This internal construction pulls back any supplied relative Levi inclusion
`l : L ⟶ P` along an étale morphism `b : S' ⟶ S`. The schemes and universe are
arbitrary. The ambient group `P` is assumed affine over `S`; no dynamic
presentation or torus containment is required.

`IsRelativeLeviSubgroup.baseChange_etale` proves the full relative Levi
predicate for the actual pullback inclusion. Closedness and smoothness persist
under base change. A radical witnessing the original Levi predicate is pulled
back using `IsRelativeUnipotentRadical.baseChange_etale`, whose affineness
hypothesis accounts for that hypothesis here. The canonical product comparison
identifies the pullback of the original Levi-first multiplication isomorphism
with multiplication of the pulled-back inclusions, by
`subgroupMultiplication_isIso_baseChange`.

`RelativeLevi.etaleBaseChangeLevi` returns the actual pullback group, its
inclusion, and this full certificate. Its source projection is recorded by
`etaleBaseChangeLevi_group`.

The provenance is derived from the existing relative Levi predicate and the
radical and multiplication transport lemmas. This module establishes no new
Levi existence or uniqueness assertion.
