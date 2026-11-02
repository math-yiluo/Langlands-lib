# Proper scheme quotients for improper dynamic parabolics

Author: Worker 1275.

This internal derived construction handles the improper case of the published
`DynamicFlagQuotientExistenceStatement`. It uses the published actual dynamic
subgroup functors and the existing relative scheme and open-subscheme objects.
No reductivity assumption is needed for this case.

For every field `k : Type u`, `improperFlagQuotient k` is `Spec k` over itself,
and `improperFlagQuotientMap k G` is the structure morphism of the actual group
scheme `G`. Its structure morphism is the identity, hence proper. Two morphisms
from any test scheme to this relative base coincide, since both are the
structure morphism of that test scheme. If `Dynamic.parabolic χ = ⊤`, this
is precisely the required fiber equivalence, because every `g⁻¹h` belongs to
the full subgroup on every test scheme.

The group identity gives a section on the entire quotient. The implemented
section has source `openOver k (improperFlagQuotient k) ⊤`; its composite with
the quotient map equals `openOverι` by the same uniqueness of maps to the
relative base. Every rational point has its whole underlying image in the top
open. Thus `exists_properFlagQuotient_of_parabolic_eq_top` supplies one actual
model satisfying all three clauses of the target in this case.

The corollary `exists_properFlagQuotient_trivialCocharacter` applies the
published `parabolic_trivialCocharacter`. It covers finite and infinite fields
and arbitrary group schemes, including the trivial group. The construction
also applies to every improper parabolic regardless of how its equality to
the full subgroup is established. It does not identify rank-zero groups or
construct quotients for proper subgroups.

Provenance: this is derived from the identity morphism's properness in pinned
Mathlib, elementary laws in the category of relative schemes, and the existing
`Dynamic.ImproperParabolic` results. It asserts no new external structural
result and supplies no proof of the full reductive existence statement.
