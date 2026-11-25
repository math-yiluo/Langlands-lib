# Relative reductive quotients from pointwise dynamic presentations

This internal derived module proves
`Langlands.GroupScheme.RelativeParabolicReductiveQuotientLocalDynamicStatement`
in every universe. It retains an arbitrary base scheme `S`, a reductive
group scheme `G`, a relative parabolic `i : P → G`, and a supplied relative
unipotent radical `r : U → P`. It assumes the proposition
`DynamicRelativeLeviStatement` and a pointwise étale dynamic presentation:
every point of `S` lies in the image of an étale map `b : T → S` for which
the pullback of `i` represents the dynamic parabolic of some cocharacter of
the pullback of `G`.

The conclusion is an actual reductive group scheme `M` over `S` and an
fppf quotient `q : P → M` with full kernel precisely
`SubgroupFunctor.range r` on every scheme over `S`. There is no affineness,
quasi-compactness, reducedness or noetherianity assumption on the base.

## Implemented proof

`RelativeLevi.exists_reductiveQuotient_of_pointwise_dynamic` gets smoothness
and affineness of `P` from the relative parabolic predicate. The supplied
radical is closed, hence monomorphic; its smoothness and normality are
already fields of its predicate.

On each chosen étale neighbourhood, reductivity of `G` is preserved by
base change. The étale pullback of `r` is a relative radical, by
`IsRelativeUnipotentRadical.baseChange_etale`. The supplied local dynamic
presentation and the explicitly assumed dynamic relative Levi theorem
allow `isRepresentedBy_unipotent_of_relativeRadical` to identify the
composite of that radical with the ambient parabolic inclusion as a
representative of the contracting subgroup on all tests.

`dynamicReductiveQuotient` then supplies a reductive centralizer quotient
of the actual pulled-back `P`, with full kernel equal to the range of the
actual pulled-back `r`. Thus these local quotients have exactly the
subgroup prescribed by reductive normal quotient gluing.
`NormalQuotient.exists_reductive_fppfQuotient_of_pointwise_etale` descends
them to the asserted quotient over `S`, retaining reductivity and the full
kernel identity.

## Provenance and remaining inputs

This is an internal composition of dynamic radical identification,
étale transport of relative radicals, dynamic reductive quotients and
reductive normal quotient gluing. It introduces no new assertion from an
external source. The radical comparison and transport constructions are
reused unchanged from `DynamicRadicalIdentification` and
`UnipotentRadicalDescent`.

Both the dynamic relative Levi theorem and pointwise dynamic
presentations remain explicit inputs of this module. The final assembly in
`ReductiveQuotientProof` discharges these inputs with published theorems
and combines this quotient construction with radical annihilation to prove
the universal property in `RelativeParabolicReductiveQuotientStatement`.
