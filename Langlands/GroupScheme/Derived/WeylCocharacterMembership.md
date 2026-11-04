# Membership in normal subgroup functors under integral Weyl averaging

Author: Worker 1374.

The internal definition `Langlands.GroupScheme.cocharactersEvaluatingIn i F z`
is the integral submodule of cocharacters `ν` for which the actual point
`z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom` belongs to `F.carrier U`.
Here `i : T.toGrp ⟶ G` is an actual homomorphism from a commutative group
scheme, `F` is a subgroup functor of `G`, `U` is any test scheme over the
base, and `z : U ⟶ (Gm S).X`. This definition works over any scheme
`S : Scheme.{u}`. Evaluation converts sums and integer multiples of
cocharacters into products and integer powers of points; subgroup closure
gives its integral submodule laws.

The subsequent results use a field `k : Type u`. If `F.IsNormal`, the
actual normalizer action preserves this submodule. The proof uses
`groupHom_cocharacterAut_comp` to identify postcomposition by
`normalizingAut i n` with ambient conjugation. On each test scheme,
`comp_innerIso_hom` expresses that conjugation by the restriction of the
rational normalizer point. Normality of `F` proves the membership.
The evaluation point `z` and test scheme `U` stay fixed throughout.

If the underlying scheme map of `i` is monomorphic, representatives of
the actual quotient `relativeWeylGroup i = N(k)/Z(k)` give the same
membership conclusion for `relativeWeylCocharacterAction i`.
If this quotient has a `Fintype` instance, its integral Weyl sum
`relativeWeylCocharacterSum i ν` belongs to the submodule whenever `ν`
does: every summand belongs, and the submodule is closed under finite
sums.

The final theorem, `relativeWeylCocharacterSum_eval_mem_derived`,
specializes this to the normal subgroup functor `derivedSubgroup G`.
Thus if the original evaluated point belongs to the actual algebraic
derived subgroup on `U`, so does the evaluated integral Weyl sum.
It requires neither a full-range derived containment hypothesis on `i`
or `ν`, nor an identification with abstract commutators.

The provenance is internal: the proof combines the published actual
normalizer/cocharacter transport, integral Weyl-sum construction,
normality of `derivedSubgroup`, and subgroup closure. There is no
additional literature assertion. No reductivity, splitness, smoothness,
reflection-existence or topological hypothesis is used. Finiteness of
the actual quotient remains explicit; the module does not establish
that hypothesis, centrality of the sum, or the full smooth-real
annihilation target.
