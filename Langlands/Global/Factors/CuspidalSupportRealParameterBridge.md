# Real cuspidal parameters for the every-place support proof

`realCuspidalParameters` gives a list of real standard-module parameters at
each real place of a cuspidal operator realization over a number field with
compact additive adele quotient. The proof supplies the real-place premise
of [`CuspidalSupportEveryPlaceProof`](CuspidalSupportEveryPlaceProof.md).

For an irreducible admissible generic real component, the principal-series
quotient and its reduction to a standard module in Langlands order give a
nonzero intertwiner onto the component. The infinitesimal-character theorem
and Kostant's Whittaker theorem give maximal faithfulness. The injectivity
criterion for a maximally faithful Langlands quotient makes the intertwiner
an embedding. This applies `realGenericStandardParameterReduction` with
both premises discharged.

The global generic-component bridge gives an irreducible admissible generic
submodule at the given real place. The transport lemma
`OperatorRealization.hasRealPlaceParameter_of_component` composes its inclusion
with the standard-module embedding. This is the real branch of
`cuspidalArchimedeanParameterReduction`. The provenance of the local inputs
is given in [`CuspidalSupportEveryPlaceProof`](CuspidalSupportEveryPlaceProof.md).
