# Conditional assembly of the Steinberg quasi-splitness argument

This is an internal construction and conditional proof. It connects the actual
finite-Galois torus-reduction interface, actual torus cocycles and actual
quasi-split inner forms. It proves none of the three existence or vanishing
propositions supplied as hypotheses.

For a `Cocycle.TorusReduction d`, `torusCocycle` constructs an actual natural
cocycle valued in `d.torus` on the finite Galois cover specified by `d.carrier`.
The supplied closed inclusion is a monomorphism on every relative test.
The existing `Cocycle.lift` therefore chooses the unique factor of each value
of the refined, twisted cocycle. Monomorphy proves naturality and the cocycle
identity. The factorization is imposed on every relative scheme-valued test,
so the construction retains that scope.

`isTrivial_of_hasTrivialTorusCocycles` applies the field property
`HasTrivialTorusCocycles` to this actual torus-valued cocycle. The existing
`Cocycle.IsTrivial.of_lift` sends its trivializing cochain through the torus
inclusion. The existing `Cocycle.IsTrivial.of_twist` removes the supplied
twist, with the convention that a coboundary has value `f(a) * f(b)⁻¹`.
Finally `Cocycle.isTrivial_refine_iff` reflects triviality through the
quasi-compact, flat, surjective refinement retained in `d`.

`cocycle_isTrivial_of_torusReduction` uses an explicit proof of
`QuasiSplitCocycleTorusReductionStatement` to obtain those reduction data for
a quasi-split semisimple group. `isQuasiSplit_of_structural_inputs` also
uses an explicit proof of `QuasiSplitInnerFormExistenceStatement` for the
given connected reductive group. Its supplied actual adjoint quotient is
semisimple and its target is quasi-split. The preceding result trivializes
its discrepancy cocycle, and `QuasiSplitInnerForm.isQuasiSplit_of_isTrivial`
descends the local isomorphisms and transports an actual geometric Borel.

`dimensionLEOneQuasiSplit_of_structural_inputs` supplies the unchanged
`HasDimensionLEOne` premise to an explicit proof of
`DimensionLEOneTorusCocycleVanishingStatement`, then applies the preceding
conditional construction. Its conclusion is exactly
`DimensionLEOneQuasiSplitStatement.{u}` at arbitrary universe `u`.
The theorem still has the three named structural and vanishing propositions
as hypotheses. They must be proved separately before this can yield the
required norm-only theorem.

Worker 1459 authored the assembly and its structural interfaces. Worker 1333
authored the imported torus-cocycle field property and its norm-criterion
statement; their supplied pairs are reused unchanged. The proof is a direct
internal composition of the indicated existing constructions, rather than a
claim that any unproved structural assertion is already available.
