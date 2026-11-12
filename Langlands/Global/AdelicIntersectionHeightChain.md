# Successive height minima over preceding stabilizer intersections

Author: Worker 83.

This derived module constructs the height-minimal sets used in Godement's
section 8. Each representation is adapted to one individual closed subgroup.
Its minimizing rational subgroup is the intersection of all preceding
stabilizers. The individual subgroups need not form a descending chain.
The construction also applies to the actual canonical standard parabolics.

## Rational prefix intersections

Fix a number field `F : Type u`, an actual group scheme `G` over `F`, and
group-scheme morphisms `z i : H i → G`, indexed by natural numbers.
`closedPrefixRationalSubgroup F G H z l` is the intersection, for `i < l`,
of the actual rational-point ranges of `z i`. Membership means that the
rational point factors through each preceding morphism over `F`.
The empty intersection is the full rational group. The successor intersection
is the preceding intersection intersected with the range of `z l`.
The membership, zero and successor lemmas prove these identities directly.

`closedPrefixRationalSubgroup_antitone` proves that these rational subgroups
descend. No inclusion between two individual ranges is assumed: a point in a
longer prefix belongs to every range in a shorter prefix.

## Prescribed representations

`exists_mul_rational_mem_closedPrefix_minima` takes actual representations
`ρ i : G → GL_(d i)` and coordinate indices `j i`. On every affine test,
membership in the range of `z i` must imply that the actual matrix of `ρ i`
scales the selected coordinate vector by a unit of the test algebra.
Only this implication is needed; closedness and exact stabilizer equality
are not premises of this theorem.

For every finite length `r` and `g ∈ G(𝔸_F)¹`, there is a rational point `q`
such that, with `h = g · rationalNormOne(q)`, every `i < r` and every
rational point `s` in the intersection of the ranges of `z k` for `k < i`
satisfy

`orbitHeight(ρ i,e_(j i),h) ≤ orbitHeight(ρ i,e_(j i),h · rational(s))`.

The proof applies the published simultaneous-minimum theorem. Each coordinate
vector is nonzero by evaluation at its selected index. The prefix subgroups
descend by the preceding lemma. If `i < l`, every point in the `l`-th prefix
belongs to the range of `z i`. Specialize the affine scalar premise to the
test algebra `F`: this proves the later-scalar-action premise of the published
height-chain theorem. Its product-formula argument and attained one-vector
minima then give all the required inequalities at one translate. The empty
chain is included.

## Actual adapted representations

If `G` is affine and locally of finite type over `F`, and each `z i` is an
actual closed subgroup inclusion, `exists_adapted_closedPrefix_minima`
constructs dimensions `d i + 1`, coordinate indices and actual representations.
The stabilizer of the selected line is exactly the individual range of
`z i`, on every relative scheme test. The same choices work for every
finite prefix and every norm-one adelic point.

The proof chooses these representations with the published actual Chevalley
line-stabilizer theorem. Restricting to `H i` proves
`((ρ i).restrict (z i)).PreservesCoordinateLine (j i)` on every scheme test:
the image of each test point lies in the range by its exhibited factorization.
This preservation is included in the conclusion, so the actual algebraic
line character and the exact height-scaling results in
`AdelicLineCharacterHeight` apply to the chosen representations.
The canonical affine/global-section comparison supplies the affine premise
of the preceding minimum theorem.

`exists_adapted_standardParabolicPrefix_minima` applies the construction to
the actual closed representatives `Standard.parabolicScheme i ν (J l)`.
The published range equality identifies their all-test line stabilizers with
the choice-free `standardParabolic i ν (J l)`. The minimizing subgroups are
the corresponding preceding rational intersections. This theorem needs no
nesting condition on `J`; in particular, it permits the usual individual
maximal-parabolic family `J l = Δ \ {α_l}` when such a root enumeration is
specified. It does not itself assert maximality for arbitrary `J`, or identify
the prefix intersection with another named standard parabolic.

## Provenance and scope

The source is R. Godement, *Domaines fondamentaux des groupes arithmétiques*,
Séminaire Bourbaki, Exposé 257 (1963), section 8, printed p.212
(PDF page 13). The displayed inequalities use all of `G(k)` for the first
representation, `P(1)(k)` for the second, and
`P(1)(k) ∩ P(2)(k)` for the third. The subsequent sentence invokes attained
height minima to cover the adelic group by rational translates of the set
with constant one. The original rendered page was read directly.
Registered source: `godement-1963-bourbaki-257-domaines-fondamentaux`,
SHA-256 `b0a531469f376c1a56a7816f0fa579cd301c4162fb1c1aa8909c886e303c722d`.

The implemented result is a number-field specialization using the published
normalized primitive-vector height, generalized to any family of actual
closed subgroups. The proof route derives the needed descent and scalar
premises and then uses the published `AdelicHeightChain`. This is distinct
from adapting the representations to the nested intersections themselves:
here the individual subgroup at index `i` is the exact line stabilizer.

No line character is identified with a simple root or a fundamental weight.
The module does not prove uniform root bounds, rank-one reduction, torus
coordinates, compactness, or the chamber-reduction target.
