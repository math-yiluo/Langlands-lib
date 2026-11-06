# Finite compact support under normalized induction

This internal supporting unit passes finiteness of fixed-vector support from
a family of inducing representations to its family of actual normalized
inductions. The group, carrier and index universes `uG`, `uV` and `uI` are
independent. The induced carriers have universe `max uG uV`.

`SmoothRep.CompactFiniteFixedVectorSupport A` means that for every compact open
subgroup, the set of indices whose actual fixed-vector module is nonzero is
finite. It does not say that the family itself is finite or that any fixed
module has finite dimension.

`compactFiniteFixedVectorSupport_of_finite_constituent_classes` applies the
actual fixed-vector constituent theorem at each compact open level. Its
premises explicitly supply a class label for every irreducible actual
subquotient of each family member, a qualifying property `Q`, and finiteness
of the classes with a qualifying irreducible representative having nonzero
fixed vectors. Retaining a nonzero fixed generator in an irreducible cyclic
quotient puts every visible family label in that finite set.

`finite_fixedVectorSupport_normalizedInduction` assumes an actual semidirect
decomposition `P = M ⋉ U` in a locally compact nonarchimedean group, closedness
of `M` and `U`, and compactness of the left quotient `P \ G`. The inducing
family has `CompactFiniteFixedVectorSupport`. For any open subgroup `K`, the
compact-visibility theorem chooses a finite set of compact open Levi
subgroups before the inducing representation. Every induced object with
nonzero `K`-fixed vectors has nonzero vectors fixed by one of these subgroups.
Its label therefore lies in a finite union of the finite inducing supports.
Compactness of `K` is not needed for this conclusion.

`normalizedInduction_compactFiniteFixedVectorSupport` applies this argument
at every compact open subgroup of the ambient group.

Worker 1751 derives this unit from the actual cyclic-quotient detection and
normalized-induction evaluation constructions. This is an internal
composition of those results, rather than a new assertion attributed to
literature. It proves neither compact-level inertia finiteness nor existence
of a category decomposition, and it supplies no component compression
stability. Those remain inputs to the intended uniform-compression application.
