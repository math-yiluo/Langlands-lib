# Admissibility under actual Levi inflation

Author: Worker 198.

This module proves the published proposition
`Langlands.Parabolic.LeviInflationAdmissibilityClause` in
`Langlands.Representation.Parabolic.AdmissibilityStatement`, preserving its
prime, finite p-adic field, supplied topology, block shape, complex module,
and independent field and module universes.

The internal argument is derived directly from the published smoothness,
fixed-vector and admissibility definitions. For any homomorphism `q : H → G`,
`fixedVectors_comp_eq_map` identifies the fixed submodule for a subgroup `K`
of `H` in the pullback representation with the fixed submodule for `q(K)`
in the original representation. Both implications unpack the image-subgroup
membership witness.

For a continuous open surjective `q`, the theorem
`isAdmissible_comp_iff_of_open_surjective` proves admissibility equivalence
for any commutative coefficient ring and module. Smoothness descends by
mapping an open fixing subgroup through the open map. Smoothness pulls back
by the published `isSmooth_comp`. For finiteness descending to `G`, pull an
open subgroup back through `q`; surjectivity identifies its image with the
original subgroup. For finiteness pulling back to `H`, map an open subgroup
forward through `q`. In each case the equality of fixed submodules transports
`Module.Finite` directly. The argument tests every open subgroup, with no
compactness, Noetherianity, or finite-dimensional ambient module assumption.

The closing theorem `Langlands.Parabolic.leviInflationAdmissibility` applies
this transport argument to the actual block projection. Its continuity is
`B.leviProjectionContinuous`. Its openness follows by composing the published
`B.decompositionHomeomorph` with the open second product projection. Its
surjectivity follows from the section identity `B.leviProjection_section`.
The topology and ring-continuity instances come from the supplied `T`.

This is a proof of the existing inflation clause, with an elementary transport
argument supplied here. Source correspondence for the target is documented
in the unchanged published statement pair. The other three clauses of
`AdmissibilityStatement` are outside this proof.

The proof and a private complete-signature check compiled without diagnostics.
The latter assigns the unapplied theorem constant with explicit universe
arguments `.{uF, uV}` to the full target telescope at those same independent
universes. The declaration universe order is field first, module second, as
in the target. Declaration inspection reports only
`propext`, `Classical.choice`, and `Quot.sound`. Development checks do not
replace independent semantic review or formal candidate validation.
