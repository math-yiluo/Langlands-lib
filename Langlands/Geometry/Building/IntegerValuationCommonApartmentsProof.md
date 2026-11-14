# Common apartments for the actual integer-valued quotient

`MaximalUnramified.commonApartments` proves the exact published proposition
`MaximalUnramified.CommonApartmentsStatement` at arbitrary universe `u`.
It retains the original inertia fixed field, its prescribed integer valuation,
the original rational-point group, apartment, sharp-fixer quotient relation,
and action. The final specialization uses the published order-one unit in
the actual maximal unramified extension.

The proof first works with supplied `IntegerValuationBuildingData B` over
any field with an order-one unit. The already constructed stabilizer of the
sharp chamber cover `P_C N P_C` contains `P_C` and the full actual normalizer
`N`. The chamber generation theorem says that these subgroups generate the
whole rational-point group. Therefore the cover stabilizer is the whole
group. Since the identity belongs to the cover, translating it shows that
every rational point belongs to `P_C N P_C`.

For two points `x,y` of the original apartment, local finiteness supplies
regular points `c,d` whose affine facet closures contain `x,y` respectively.
Their facets `C,D` are chambers. AS4 and the existing depth-zero filtration
comparison show that `P_C` is contained in the singleton sharp fixer at `x`,
and `P_D` in that at `y`: the root fixer of a facet is contained in the
filtration at `c` or `d`, and this filtration only grows at closure points.
Taking the subgroup join over roots preserves these inclusions.

Affine Weyl chamber transitivity and its containment in the actual
normalizer action provide an actual `m` with `m C = D`. Apply the chamber
cover to `g*m = p*n*q`, where `p,q` lie in `P_C`. Normalizer covariance puts
`m*q*m^-1` in `P_D`, and the group identity

`g = p * (n*m^-1) * (m*q*m^-1)`

gives the required mixed singleton-sharp-fixer factorization for every
original rational point `g`. The published
`ApartmentQuotient.hasCommonTranslatedApartment_iff_factorization` converts
this directly into common translated apartments of the original quotient.

This proof is an internal composition of the chamber cover, actual group
generation, facet filtration comparisons, chamber transitivity, actual
normalizer lifts, and the quotient factorization criterion. It assumes no
local-field structure on the inertia fixed field and introduces no
replacement quotient or additional geometric hypothesis.
