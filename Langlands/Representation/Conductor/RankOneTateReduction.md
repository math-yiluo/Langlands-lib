# Rank-one conductor reduction to scalar Tate theory

This internal unit reduces the complete rank-one conclusion of
`Conductor.ConductorExponentStatement` to the separately published, unproved
`GodementJacquet.LocalTateConductorStatement`. It retains arbitrary
nonarchimedean local fields and independent universes for the field and the
original representation carrier. It adds no character-model, dimension or
fixed-vector hypothesis to the host normalization and genericity assumptions.
It does not prove the scalar statement or any higher-rank assertion.

The first theorem uses only admissibility and irreducibility of the original
rank-one representation. The published `tateCharacterModel` constructs an
actual continuous quasicharacter and an equivalence from that carrier to its
scalar character representation. The scalar proposition then supplies the
least character level, both analytic predicates, explicit normalized Euler
generators and a single nonzero coefficient with the exact level exponent.
Those conclusions are packaged into `ScalarTateEpsilonData`, and
`rankOneConductorConclusion_of_scalar` transfers the full pair epsilon relation
and the fixed-space conclusions to the original carrier.

The host has no measurable structure assumption on the field's unit group.
The proof installs its canonical Borel measurable structure locally and uses it
only in the scalar integrals and their intermediate transport. The concluding
pair relation and fixed-vector submodule use exactly the original supplied
structures. This creates no extra hypothesis in the host specialization.

`rankOneTateConductorWitness` chooses the actual coefficient and natural level
from this existence theorem, with proofs of the complete epsilon relation,
least nonzero fixed level and dimension-one fixed space. The final theorem
extracts admissibility and irreducibility from `Whittaker.IsGeneric` to obtain
the exact rank-one host clause. It needs no extra nontrivial-carrier premise.

The provenance is internal. This is a composition of published constructions
and the preceding character-level adapter, conditional on the explicitly
supplied scalar theorem. The analytic existence, local Fourier computation and
principal-unit exponent theorem are not established here. No source result is
newly asserted, and this reduction does not discharge the full
`EssentialConductorStatement` proof task.
