# Applying generic Henselian quasi-splitness to the actual unramified field

The theorem `unramifiedQuasiSplit_of_henselianDiscrete` proves the exact
`UnramifiedQuasiSplitReductionStatement` at arbitrary universe `u`. Its premise
is the generic `HenselianDiscreteQuasiSplitStatement`; its conclusion is the
unchanged `UnramifiedQuasiSplitStatement`. The generic theorem remains an
explicit premise, so this result does not prove unconditional quasi-splitness or
sharp torus conjugacy.

The implementation first proves two arithmetic adapters for the published
integer-normalized valuation `MaximalUnramified.valuation F` on the actual
inertia fixed field. Rewriting by `valuationSubring_eq F` reduces Henselianity to
`LocalGalois.Separable.fixedFieldIntegersIsHenselian F`. The same equality reduces
algebraic closedness of the actual residue field to the first field of
`LocalGalois.Separable.fixedFieldResidueIsAlgClosure F`. That first field is
algebraic closedness, while the other field is algebraicity over the base
residue field and is not needed here.

The final proof introduces the original local field `F`, an arbitrary connected
reductive group `H` over `UnramifiedClosure F`, and its reductivity witness. It
applies the generic theorem with that exact field, the published normalized
valuation, its `valuation_surjective F` theorem, and the two arithmetic adapters.
The result is the required field-defined geometric Borel for `H`.

No completion is substituted for the inertia fixed field; no change of universe,
extra field property, integral model or supplied Borel is introduced. The proof
uses the existing arithmetic theorems and a specialization of the generic
statement; it does not reproduce the source's dimension-one and Steinberg
arguments for the generic statement.
