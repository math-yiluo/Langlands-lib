# Assembling an integral Iwasawa family from actual local model properties

For a number field `F : Type u`, actual group schemes `G` and `P` over `F`,
and a supplied morphism `p : P ⟶ G`, fix a finite set `S` of finite places
and an actual `S`-integer integral model `M` of `G`. The internal predicate
`ModelLocalConditions` records two properties at every place outside `S`:
every compact subgroup containing the actual local model image equals that
image, and the range of the original `P.affinePointsTarget p` multiplied on
the left of that image covers the whole original completion point group.
The topology is the existing regular-function evaluation topology.

`isIntegralIwasawaFamily_of_models` additionally assumes that `G` is affine
and locally of finite type. It proves all three clauses of the published
`IsIntegralIwasawaFamily` for the existing
`FiniteTypeIntegralFamily.subgroup F G`. This family was chosen from one
closed representation before any place, adelic point, regular function,
integral model, or local structural proof used here.

The proof combines `IntegralModelCompletions.eventually_subgroup_eq` with
the cofinite set of places outside `S`. At those places the fixed family
equals the actual image of the supplied model, so the two local assumptions
give its maximality and its literal parabolic-left product equality.
Compactness follows from the existing finite-type family theorem. The
existing adelic absorption and uniform regular-function integrality theorems
give the other two clauses directly for this same family. In particular,
the family does not depend on the later adelic point or regular function,
and each function's exceptional set is uniform over all points of the
chosen subgroup.

`ModelLocalConditions.of_canonicalModels` supplies these two local conditions
from the corresponding explicit premises for the canonical-integer
specializations of `M`. The local field is the original
`FiniteCompletion F v`, with `FiniteCompletion.valuativeRel v`, and both
rational and coefficient points carry the existing evaluation topologies.
The proof applies the previously established
`subgroup_maximal_of_canonicalModel` and
`subgroup_covering_of_canonicalModel`. These preserve the exact integral
image, the original generic coefficient maps, and the actual supplied
parabolic-left morphism.

This is an internal assembly consequence of the published finite-type family
and the actual model comparisons. It is uniform in universe `u`. It retains
the arithmetic model, local maximality, and local covering as premises; it
does not derive them from connected reductivity and parabolicity. Therefore
it does not prove `IntegralIwasawaFamily.ExistenceStatement`. Proving that
unconditional statement still requires the good-model existence and both
local structural results.
