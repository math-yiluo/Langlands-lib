# Integer multiplication on bundled abelian schemes

Author: Worker 124.

This module specializes the published group-scheme multiplication construction
to the published `Langlands.AbelianScheme` bundle. It imports `Basic` and
`MultiplicationIsogenyStatement` by module name.

`Langlands.AbelianScheme.multiplication A n` is `n • 𝟙 A` in the actual additive
group of homomorphisms of the abelian scheme `A`, for an arbitrary integer `n`.
The Hom group in `Basic` is the pointwise group of actual group-scheme
homomorphisms, expressed using `Additive`; its integer scalar action is integer
power in multiplicative notation. Consequently `groupHom_multiplication` and
`hom_multiplication` are definitional equalities identifying this endomorphism
and its underlying scheme map with the existing
`Langlands.GroupScheme.multiplication A.toGrp n`. No new geometric map or
alternative isogeny predicate is supplied.

`points_multiplication` applies the published sections formula: on every
`U : Over S` and section `x : U ⟶ A.X`, postcomposition with the underlying
multiplication map is `x ^ n`. `multiplication_baseChange` unfolds the bundled
base-change functor and transports the published arbitrary-base-change identity
through `Additive.ofMul`.

`isIsogeny_multiplication_of_statement` is an explicitly conditional lemma. Its
first hypothesis is the whole published proposition
`Langlands.GroupScheme.MultiplicationIsogenyStatement`. Given that hypothesis,
it supplies the bundle's underlying group scheme, commutativity instance,
smoothness, properness and geometric connectedness to the proposition. For
`n ≠ 0`, the result is the existing `GroupScheme.IsIsogeny` predicate on the
underlying group-scheme homomorphism, hence finiteness, flatness and surjectivity
of the actual scheme morphism.

This lemma does not prove the geometric proposition or assume it as a field of
the bundle. The generic proposition remains the sole unresolved geometric
target; its proof can be passed directly to this lemma. No extra restriction on
the base, dimension, sign of `n`, or residue characteristics is introduced.

## Provenance and scope

The provenance of this module is internal: it is an interface construction and
conditional specialization of existing Library declarations. It introduces no
new theorem attributed to the literature. The mathematical source correspondence
for the geometric target, including its nonzero restriction and its derived
negative-integer and varying-dimension scope, remains in the imported
`MultiplicationIsogenyStatement.md`. The explicit-commutativity convention and
its separate source-definition equivalence obligation remain in `Basic.md`.

The only proved assertions here are the identifications of the constructed map,
its action on sections, its base-change law, and the conditional specialization.
There is no unconditional isogeny claim, rational inverse, degree, etaleness or
torsion-rank assertion.
