# Actual torus reflections and coroot compatibility in a commuting square

Author: Worker 1283.

This internal unit constructs the actual involution of a commutative
group scheme attached to a character `α` and a cocharacter `ν` whose
actual lattice pairing is two. It proves that supplied actual root data
have compatible coroots in a commuting square, provided the torus map
is epimorphic, the roots match, and the target's full normalizer image
on its character lattice is finite.

The base field has arbitrary universe `u`. The root index types of the
two supplied root data have independent universes `v` and `w` and need
not carry finite instances. The main coroot theorem assumes affine
ambient groups for the published `IsRootDatumOf` predicates, a split
source torus, a monomorphic target torus embedding, and the displayed
finite normalizer-image instance. It does not assume connectedness,
reductivity, or centrality of the ambient map. In the intended central
isogeny application, epimorphy of the restriction and finiteness of the
full target normalizer image are separate geometric obligations.

The construction `latticeReflectionIso α ν h` has both hom and inverse
`id - α ≫ ν`. The pairing condition identifies `ν ≫ α` with twice the
identity of the multiplicative group. Hence, for `a = α ≫ ν`,
`a ≫ a = 2 a`, and bilinearity of composition gives
`(id - a) ≫ (id - a) = id`. This works for any supplied commutative group
scheme with those actual maps and pairing; splitness is not needed for
the construction. Its character action is
`χ ↦ χ - ⟨χ, ν⟩ α`.

For an actual root datum `P`, its reflection along `P.root j` has exactly
this formula with `ν = P.coroot j`. `IsRootDatumOf` realizes that
reflection by a normalizing point and an automorphism `σ` of the torus.
Characters separate maps into a split torus, so `σ` is the constructed
involution itself. Thus the root datum realizes the explicit involution,
not just an unspecified automorphism with the same action on roots.

Suppose `i ≫ φ = groupHom t ≫ i'` and
`t ≫ α' = α`. The explicit source involution and the explicit target
involution for `α'` and `ν ≫ t` commute with `t`; this follows directly
from their formulas. Naturality of inner automorphisms, the square and
this commuting relation identify the source normalizing-point equation
with the target equation after precomposition by `groupHom t`.
Epimorphy cancels that precomposition. Consequently the image of the
source normalizing point realizes the target involution on every test
scheme.

Apply this to matching roots of supplied actual root data `P` and `Q`.
The target involution is defined by the pushed source coroot, whose
pairing with the matched target root is two by associativity of the
actual lattice pairing. It and the target datum's reflection belong to
the finite full normalizer image, so their product has finite order.
`Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections`,
from `Reductive.RootDatumCorootComparison`, identifies their defining
functionals by its integral finite-order calculation. Perfectness of
`Q`'s actual lattice pairing then identifies the two cocharacters,
giving `P.coroot j ≫ t = Q.coroot j'`.

All these steps are internal deductions from the existing commutative
category, actual character pairing, character separation, inner
conjugation and root-datum interfaces. The integral argument implements
the normalizer-based coroot comparison without choosing an invariant
positive form. No finite-image theorem, root bijection, epimorphy of a
central isogeny's torus restriction, or isomorphism criterion is proved
here. In particular, the full
`CentralIsogenyRootDatumHomStatement` remains outstanding.
