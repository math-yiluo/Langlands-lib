# Finite-Galois presentations from separable-closure innerness

This internal construction turns a supplied quasi-split model, full-centre
adjoint quotient, quasi-split adjoint, and specified separable-closure
isomorphism with inner discrepancy into an actual finite-Galois
`QuasiSplitInnerForm`. The ground field is arbitrary and all fields and
schemes lie in an arbitrary universe `u`.

For any field extension `Ω/k`, `IsoModel.hasInnerDiscrepancy` starts with
an exact finite model `D` of a specified isomorphism `e`, a faithful
automorphic action, and inner discrepancy for the local family of `e`.
The actual cover refinement `Spec Ω → Spec E`, where `E` is the model's
finite field of definition, is quasi-compact, flat and surjective.
`D.localIso_refine` identifies the refined finite family with the family
of the specified `e`. Fpqc reflection of inner discrepancy then gives
innerness for `D.localIso` on every relative test scheme and every
subsequent refinement.

`IsoModel.innerCocycle` constructs the canonical natural discrepancy
cocycle over `Spec E` from this descended innerness. Its discrepancy
theorem verifies the equation for the finite local family.
`IsoModel.innerCocycle_refine` proves that extending this cocycle along
`Spec Ω → Spec E` gives exactly the canonical cocycle for the original
specified family. The proof refines the discrepancy equation, uses exact
recovery of the family, and applies canonical-cocycle uniqueness.
Neither a finite-stage cocycle nor any of its coherence laws is input.

The selected construction `QuasiSplitInnerForm.ofSeparableClosure`
assumes connected reductivity of the target `G`, quasi-splitness of a
supplied model `H`, an actual full-centre adjoint quotient `q : H → A`,
quasi-splitness of `A`, a specified actual isomorphism `H_sep ≅ G_sep`,
and inner discrepancy of that isomorphism's local family for the actual
adjoint action of `q`. Affineness of `H` supplies quasi-compactness and
quasi-separatedness; smoothness of `G` supplies local finite
presentation. The finite-model construction therefore descends the
specified isomorphism to a finite intermediate field `E` of the
separable closure. This field is separable over `k` and has universe `u`.
Faithfulness of the actual adjoint action gives the preceding finite
cocycle and its discrepancy equation. The existing
`ofFiniteSeparable` construction enlarges `E` to its finite Galois normal
closure and refines the local family and cocycle. The result retains the
supplied model and quotient and includes the actual all-test natural
multiplicative equivalences, the natural adjoint-valued cocycle and their
discrepancy equation.

The provenance is internal: this module combines exact finite-stage
recovery, fpqc reflection and canonical discrepancy, actual adjoint-action
faithfulness, and finite-separable-to-Galois refinement from the existing
interfaces. It constructs the finite cover, local family and cocycle.
It does not construct the supplied quasi-split model, quotient,
separable-closure isomorphism or its innerness, so it does not prove
`QuasiSplitInnerFormExistenceStatement`.
