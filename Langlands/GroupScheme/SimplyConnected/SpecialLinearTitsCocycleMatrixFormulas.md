# Conditional matrix formulas on every Galois-cover test

This internal derived helper transfers the formulas in
`SpecialLinearTorusAutomorphismStatement` to the local Galois discrepancy of a
supplied `SpecialLinearTitsCocycle.Presentation`. The automorphism statement
remains an explicit premise. The helper does not prove that statement or
identify the discrepancy's based root action with the original star action.

`Presentation.discrepancy_eq_discrepancyIso` compares the discrepancy of
`p.localIso` with the action of the actual special-linear group-scheme
automorphism `p.discrepancyIso sigma`, evaluated on the test
`LocalGroupIso.coverTest a` over the extension field. Both identifications in
this specialization are definitional: `p.localIso` is
`LocalGroupIso.ofBaseChangeIso p.baseChangeIso`, and `p.discrepancyIso sigma`
is `matrixDiscrepancyIso p.baseChangeIso sigma`. The proof rewrites these
identifications explicitly and applies the general all-test comparison.

`Presentation.exists_discrepancy_matrices` supplies one matrix
`x sigma` over `p.L` for each Galois automorphism, conditional on
`SpecialLinearTorusAutomorphismStatement` in the same universe. Apply that
statement to `p.coordinatePinning`, `p.discrepancyIso sigma`,
`p.discrepancyTorusIso sigma` and their actual inclusion square. Classical
choice selects the matrices simultaneously. For every ground-field relative
test scheme, every cover point `a`, and every determinant-one matrix `g`, the
result has two implications:

- If the based projection of the actual discrepancy root-datum automorphism
  fixes every simple-root index, the discrepancy is `X g X⁻¹`.
- If that projection moves some simple-root index, the discrepancy is
  `X (g⁻¹)ᵀ X⁻¹`.

Here `X` is the image of `x sigma` under `coefficients a`. The root-datum
automorphism and its based projection are precisely the constructions used by
the automorphism statement, with the supplied coordinate pinning and square.
The proof specializes its all-test formulas to `coverTest a`, rewrites the
discrepancy comparison, identifies the structure-ring map with
`coefficients a`, and uses preservation of inverse by the general-linear
group homomorphism.

`Presentation.discrepancyMatrices p hAut` names a classical choice of the
simultaneous matrices from this existence theorem.

This is a composition of existing interfaces, with no new external
mathematical input. Its fields, characteristic, rank and universe are
unrestricted. The formula holds on all relative test schemes; it does not
replace the local group-scheme isomorphism by its field-valued points. The
full Tits cocycle statement still requires the automorphism-classification
proof and the comparison with the original Tits star action.
