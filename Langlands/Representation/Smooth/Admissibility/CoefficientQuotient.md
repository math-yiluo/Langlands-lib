# Admissibility of native coefficient quotients

This derived transport module works with a commutative complex algebra `R`, a
topological group `G`, and representations on `R`-modules `V` and `W`. The ring,
group and both modules have independent universe levels. The modules have no
topology. All conclusions use the original `R`-linear representations, the
original `Langlands.fixedVectors`, and finite generation over `R`.

`fixedVectorsQuotientEquiv_of_complexAlgebra` constructs the canonical
`R`-linear equivalence from the source's compact-open fixed-vector module modulo
the kernel of the restricted intertwiner onto the target's fixed-vector module.
Its formula on quotient classes is the original native `fixedVectorsMap`.
This is a quotient of fixed-vector modules, not an inverse or a splitting of
the original representation intertwiner.

`fixedVectorsMap_surjective_of_complexAlgebra` says that a surjective native
`R`-linear intertwiner from a smooth representation induces a surjection on
vectors fixed by any compact open subgroup. It needs neither a Noetherian ring
nor finite generation. Target smoothness follows from source smoothness and
surjectivity.

`isAdmissible_of_surjective_coefficients` assumes in addition that `R` is
Noetherian and every open subgroup of `G` contains a compact open subgroup.
Admissibility of the source then implies admissibility of the target, using the
existing convention that fixed vectors for **every open subgroup** must form a
finitely generated `R`-module.

The first proof locally equips the same source and target carriers with their
canonical complex scalar restrictions. Restricting the given linear map gives
an intertwiner of their actual complex group actions. The published
`Langlands.Compact.fixedVectorSurjectivity` supplies a compact-open invariant
preimage. The actions and map on underlying vectors are unchanged by restriction,
so this is also a preimage for the original native `fixedVectorsMap`. The
complex argument supplies invariant lifts; it does not assert complex
admissibility or complex finite dimensionality.

The canonical quotient equivalence is Mathlib's first isomorphism construction
applied to the now-surjective native fixed-vector map. Its quotient-class
formula is definitional.

For admissibility, the published smoothness quotient theorem supplies target
smoothness. Given an open subgroup `H`, choose a compact open `K ≤ H`. The
quotient of the finitely generated source `K`-fixed module is finitely
generated. `Module.Finite.of_surjective` applied to the canonical quotient
equivalence gives finite generation of the target's `K`-fixed vectors. The
published `finite_fixedVectors_of_le` then gives finite generation of the
`H`-fixed submodule. This last submodule step uses Noetherianity.

The argument is an internal consequence of the published complex compact
averaging, scalar-restriction, smoothness-transfer and cofinal-admissibility
modules. It extends the coefficient scope of the existing complex-only helper
`Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective`; it does not
replace or modify that result. Worker 1780 identified this native quotient
transport needed by the rational coefficient Jacquet comparison and suggested
the scalar-restriction route; Worker 1755 implemented it.

This module provides no orbit geometry, no rational Jacquet finiteness theorem,
and no unrestricted uniform compression stabilization theorem. Those results
retain their separate hypotheses and proof obligations.
