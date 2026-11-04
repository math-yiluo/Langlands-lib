# A nonidentity normalizer from proper quotient geometry

This internal assembly constructs an actual rational normalizer point whose
class in `relativeWeylGroup i = N(k)/Z(k)` is not the identity. It works over
every algebraically closed field `k : Type u` and retains the supplied
geometric inputs needed by its two constituent constructions.

`nonidentityNormalizerOfProperFlagQuotient` takes a smooth connected group
scheme `G`, an actual maximal torus `i : T → G`, and a finite actual Weyl
quotient. The torus factors through a supplied closed subgroup `j : P → G`.
Maximal tori must be conjugate inside `P`, the whole-torus centralizer's
rational points must belong to `P(k)`, and the subgroup functor represented
by `j` must differ from the whole group.

The quotient morphism `q : G → Q` is flat, surjective and quasi-compact, with
exact right `P`-coset fibers on every scheme test; `Q` is proper over `k`.
An actual matrix representation `ρ` on `k^(n+1)` and a coordinate index `l`
are supplied. On every scheme test, the range of `j` must be exactly the
stabilizer of the line spanned by the `l`th coordinate vector, expressed
using a unit scalar in that test scheme's global sections.

The implemented construction first applies
`Dynamic.nonfixedFlagQuotientLift`. Properness of `Q` supplies local finite
type and separatedness. The finite Weyl bound and the connected smooth
finite-target action theorem then produce a rational group point whose
quotient section is not torus-fixed. Next,
`nonidentityNormalizerOfNonfixedProperFlagQuotient` contracts that section's
matrix orbit to two distinct torus-fixed extreme-weight lines. The exact
stabilizer and fiber laws identify them with distinct all-test fixed
quotient sections. Internal maximal-torus conjugacy provides normalizer
representatives of their cosets, and centralizer containment shows that
the quotient of those representatives has nonidentity Weyl class.

`IsConnectedReductive.rankOneNonidentityNormalizerOfProperFlagQuotient`
specializes to connected reductive `G`, a split maximal torus, and pairwise
integral dependence of the actual roots. The existing rank-one sign
embedding into `Bool` supplies Weyl finiteness; smoothness and connectedness
come from connected reductivity.

The provenance is internal composition of
`Dynamic.NonfixedFlagQuotientSection`,
`Dynamic.NonidentityNormalizerFromProperQuotient`, and
`Rational.RankOneWeylQuotient`. In particular the nonfixed rational section
and the nonidentity Weyl class are constructed, while the quotient geometry,
line stabilizer, centralizer containment and internal torus conjugacy
remain explicit inputs. No dimension bound or unconditional
`RankOnePositiveRootUniquenessStatement` is proved by this assembly.
