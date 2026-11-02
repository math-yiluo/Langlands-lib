# Reducing cocycle vanishing to finite subcoactions

This internal algebraic reduction uses the finite-core and directed-union
theorems for the unchanged `GroupoidCoaction` interface. The commutative rings
B and C lie in arbitrary universe u, the coefficient module M lies in
independent universe v, and t is the separate target ring map.

`finiteStableSubmodules θ` is the set of B-submodules H that are finite as
B-modules and stable under θ. To prove `IsStableSubmodule.sup`, decompose an
element of H + K as h + k, lift θ(h) and θ(k) to their respective coefficient
modules, and map both lifts into C tensor_B (H + K). Their sum lifts θ(h + k).
This step needs no Noetherian or ring-relation hypothesis.

Mathlib's `Submodule.finite_sup` shows that H + K is finite when H and K
are finite. Thus `finiteStableSubmodules_directed` uses H + K as a common
upper bound. For Noetherian B and `RingEtaleEquivalenceRelation t`, the
published `exists_finite_subcoaction` theorem supplies a finite submodule
containing each m, together with a coaction whose inclusion is equivariant.
The stable-submodule existence criterion turns this into membership of
the directed family, proving `finiteStableSubmodules_cover`.

`oneCohomologyVanishes_of_finite_subcoactions` assumes vanishing for every
finite submodule equipped with a coaction and equivariant inclusion in M.
Apply the directed stable-union vanishing theorem to the preceding family.
Its canonical restriction coactions satisfy exactly the assumed condition,
so this proves `OneCohomologyVanishes` for θ. Only the published flat-test
cocycle predicate is used; no separate colimit construction is needed.

For M in the same arbitrary universe u as the rings,
`isAcyclic_of_finite_subcoactions` gives the corresponding reduction for
the unchanged `IsAcyclic` predicate. Convert finite-subcoaction acyclicity
to cocycle vanishing using `oneCohomologyVanishes_of_isAcyclic` from
`GroupoidCoactionCocycleExtension`, apply the preceding reduction, and
convert back with its equivalence. The common universe is needed by the
cocycle-extension converse, whose extension objects include M × B.

The provenance is internal: stability of sums follows from additivity and
tensor inclusion, directedness from finite generation, and the reduction
from the existing finite-core, restriction, and cocycle theorems. Vanishing
on finite subcoactions is an explicit assumption here and remains to be
proved for the host task's geometric target.
