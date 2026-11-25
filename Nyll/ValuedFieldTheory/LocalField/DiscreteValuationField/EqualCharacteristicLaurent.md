# Laurent-series evaluation for local fields of equal characteristic

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.EqualCharacteristicLaurent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file treats the equal-characteristic branch of the structure theory of local fields. For a complete discretely valued field `K` whose valuation ring has characteristic `p` and whose residue field `κ` is finite of order `p^n`, it uses the Teichmüller section `κ → O_K` and a uniformizer `π` to build an evaluation map `κ((X)) → K`: first `κ⟦X⟧ → O_K`, `X ↦ π`, then the extension to `κ((X)) = κ⟦X⟧[X⁻¹]`. It shows that this map is onto.

## Main definitions and results

- `coeffSubringHom`, `coeffHom`: the Teichmüller ring homomorphisms `κ → O_K` and `κ → K`; `teichmullerRepresentativeSystem` records the first as a system of residue representatives.
- `powerSeriesEvalSubringHom`, `powerSeriesEvalHom`, `laurentSeriesEvalHom`: the evaluations `κ⟦X⟧ → O_K`, `κ⟦X⟧ → K` and `κ((X)) → K`, sending constants to their Teichmüller lifts and `X` to `π`. In this general form the topologies on `κ` and `O_K`, continuity of the section and topological nilpotence of `π` are hypotheses.
- `adicPowerSeriesEvalSubringHom`, `adicLaurentSeriesEvalHom`: the same maps with `κ` discrete and `O_K` carrying its maximal-ideal-adic topology, which the file shows linear, complete and Hausdorff, with `π` topologically nilpotent.
- `adicPowerSeriesEvalSubringHom_surjective`: every element of `O_K` is a power series in `π` with Teichmüller digits. `adicLaurentSeriesEvalHom_surjective`: the Laurent evaluation is onto `K`.
- `LocalField.laurentImageSubfield`, the image of the evaluation, equals `⊤` (`laurentImageSubfield_eq_top`), and `laurentSeriesEquivLaurentImageSubfield` is the ring isomorphism of `κ((X))` onto it. The image gets a nontrivially normed field structure and `K` a normed algebra over it, from the range-restricted valuation.
- `finiteDimensional_over_laurentSeries`: for every uniformizer `π`, `K` is finite-dimensional over `κ((X))` via the `laurentSeriesAlgebra` of `π`. The final `equalCharacteristic_exists_laurent_finiteExtension`: for a local field with these hypotheses there are a uniformizer and an algebra structure `κ((X)) → K` making `K` finite-dimensional over `κ((X))`.
- `finiteDimensional_of_surjective_algebraMap`: a field algebra with surjective structure map is finite-dimensional.

## Proofs

Surjectivity on `O_K` compares the partial sums of the series with the `π`-adic expansion (`LubinTate.Valuations.partialSum_tendsto_adic`). For `K`, write a nonzero `x` as `π^m u` with `u` a unit (`exists_laurent_unit`). Finite dimensionality is then deduced from surjectivity.

## Points to watch

- The final theorem asserts only existence of an algebra structure with `K` finite-dimensional over `κ((X))`. The file's results give more, namely that the evaluation is an isomorphism `κ((X)) ≅ K` (dimension one), but no single equivalence `κ((X)) ≃+* K` is stated.
- The characteristic hypothesis is `CharP F.valuationSubring p` together with `[Fact p.Prime]` and `Nat.card κ = p ^ n` for a positive `n`, not a hypothesis on `K`.
- The normed structures on the image subfield play no role in the finite-dimensionality argument.
- `laurentSeriesAlgebra` exists in two versions, one in `CompleteDVF.EqualCharacteristicLaurent` (with topology hypotheses) and one in `LocalField` (through the image subfield).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/EqualCharacteristicLaurent.lean`: the Lean file is the source byte for byte (SHA-256 `97c9d0c56f56a0caf55aa886ed6dc4eb46bb8ea06b95e4301073dedc1dc375b0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
