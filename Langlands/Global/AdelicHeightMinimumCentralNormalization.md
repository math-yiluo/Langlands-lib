# Central positive normalization of actual height minima

Author: Worker 83.

This derived interface records the minimum inequalities on the full actual
adelic group, restricts them through a fixed right factor, and proves that
extracting an actual central positive-torus factor preserves them. It is
intended for a Levi factor whose own character norms were not prescribed
by ambient norm-one membership.

Fix an arbitrary universe `u` and number field `F : Type u`. All points,
representations, rational-point homomorphisms and heights are the actual
Library constructions. No matrix realization of the group is substituted
for those constructions.

## Inequalities before imposing norm-one membership

`adelicChainHeightMinimalSet F G r d ρ v Q c` is the set of all adelic points
`g` satisfying

`height_i(g) ≤ c · height_i(g · rational(q))`

for every `i < r` and every `q ∈ Q i`. The finite family can have different
representation dimensions and selected vectors at each index; each rational
comparison subgroup is specified. This definition requires no reductivity,
affineness, finite-type hypothesis, nesting of the rational subgroups or sign
condition on `c`.

`mem_adelicChainHeightMinimalSet_coe` identifies these inequalities, for a
point already supplied in the norm-one subgroup, with the existing
`chainHeightMinimalSet`. The equivalence is definitional.

`mem_adelicChainHeightMinimalSet_restrict_of_fixed_factor` restricts and
reindexes the inequalities from an ambient group `G` to an actual subgroup
morphism `f : H ⟶ G`. Suppose

`p = image(h) x`,

where `h` is any adelic point of `H` and `x` belongs to an adelic subgroup
`N` fixing each retained representation vector. The index map `σ` must send
the retained indices `i < s` to indices `σ i < r`. Every tested rational
point of `R i` must map into `Q (σ i)` and normalize `N`. The conclusion
places `h` in the corresponding full adelic minimum set for the restricted
representations, reindexed vectors and comparison groups `R`, with the
same `c`.

The proof applies an ambient inequality to the image of the tested rational
point. It removes `x` initially by fixedness and after translation by
normalization of `N`. Actual representation restriction and principal-point
naturality identify the remaining inequality with the inequality in `H`.
Neither `h` nor `p` is required to be norm one. The original norm-one transfer
is compatible through the definitional membership equivalence.

## Cancellation of a central line-scalar factor

`mem_adelicChainHeightMinimalSet_central_mul_iff` takes any actual central
morphism `z : A ⟶ G` of group schemes. Each retained representation must
preserve its selected coordinate line after restriction along `z`, on all
scheme tests with a global unit as scalar. For every adelic `a` of `A`
and every adelic `g` of `G`, it proves

`image(a) g ∈ adelicChainHeightMinimalSet ↔ g ∈ adelicChainHeightMinimalSet`.

The selected vectors are `e_(j_i)`. No torus or reductivity assumption on
`A` or `G` is needed for this cancellation. No norm-one assumption on `a`
or `g` is present.

The actual all-test centrality makes `image(a)` commute with every adelic
point of `G`. Moving it to the right in each height and using the exact
line-character scaling theorem multiplies both sides of the comparison by
the same positive real number, the normalized idele norm of the line
character at `a`. That number is positive because its value is a unit of
the nonnegative reals. Cancellation proves each inequality equivalence,
including after every rational translation. The real constant `c` is
unchanged and may have any sign. Empty prefixes are included.

## Constructing a norm-one minimum representative

`exists_normOne_chainHeightMinimalSet_of_splitComponent` assumes connected
reductivity of `G` and an actual split component `z : A.toGrp ⟶ G`. It
retains the all-test selected-line preservation input on `A`. For every
adelic point `g` in the full adelic minimum set, it constructs

`a ∈ PositiveRealTorus.intrinsicSubgroup F A`,

`m ∈ normOneSubgroup F G`,

with the exact equality `positivePointMap(a) m = g` and with `m` in the
existing norm-one `chainHeightMinimalSet` for the same representations,
coordinate vectors, rational subgroups and constant.

The proof obtains injectivity and finite index of character restriction
from the published `characterRestriction` theorem. Splitness of `A` supplies
its finite split coordinates. The published actual `positiveFactor` and
`normOneFactor` then give the two factors and their equality. Centrality
of the split component and the proved cancellation equivalence transfer
the original minimum inequalities to `m`. The theorem neither assumes nor
infers that the original `g` itself is norm one.

## Provenance and scope

These are internal consequences of the imported actual orbit-height,
fixed-factor restriction, line-character scaling, character-restriction
and positive/norm-one decomposition theorems. No additional assertion from
external literature is introduced.

The final theorem assumes a supplied split component and supplied selected-line
preservation. Applying it to a canonical standard Levi still requires the
published structural results and the comparison with the ambient adapted
parabolic family. This module does not construct an ambient Levi-unipotent
factorization, prove rank-one height-to-root bounds, perform rank induction
or establish `AdelicSiegelChamberReductionStatement`.
