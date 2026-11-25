# The decompositions O^* ≅ μ_(q−1) × U¹ and K^* ≅ μ_(q−1) × U¹ × ℤ

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a field `K` with a chosen complete discrete valuation (the library's `CompleteDVF`), valuation ring O, and finite residue field with q elements. With μ_(q−1) the Teichmüller representatives (the (q − 1)-st roots of unity in O, which reduce isomorphically onto the residue units), the file proves O^* = μ_(q−1) × U¹ and, after fixing a uniformizer ϖ, K^* = μ_(q−1) × U¹ × ϖ^ℤ, with uniqueness of the factors.

## Main definitions and results

- `residueRootsTimesPrincipalUnitMulHom F`: the multiplication map μ_(q−1) × U¹ → O^*, shown injective and surjective. `valuationSubringUnitsEquivRootsTimesPrincipalUnits F` is the resulting group isomorphism.
- `valuationSubringUnitFieldUnitHom F`: the injective inclusion O^* → K^*.
- `exists_roots_principalUnit_uniformizer_zpow`: every x ∈ K^* equals ζ·u·ϖ^n with ζ ∈ μ_(q−1), u ∈ U¹, n ∈ ℤ. `roots_principalUnit_uniformizer_zpow_eq_iff`: two such expressions are equal iff their three factors agree.
- `fieldUnitDecompositionFactors F`: the group (μ_(q−1) × U¹) × `Multiplicative ℤ`; `rootsPrincipalUnitUniformizerMulHom F ϖ` multiplies the factors, and `fieldUnitsEquivRootsPrincipalUnitsUniformizer` is the group isomorphism with K^*.
- The existence, uniqueness and isomorphism statements each have a `..._of_zeroSubgroup_eq_unitGroup` form taking the hypothesis as an equality of subgroups of K^*; `mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq` converts it.

## Proofs

For O^*, a unit u is written ζ·(ζ⁻¹u) with ζ the Teichmüller lift of its residue; injectivity reduces modulo 𝔪 and uses injectivity of reduction on μ_(q−1). The field statements combine this with the library's unit–uniformizer normal form for `V`.

## Points to note

- The field-unit results do not use the valuation of `F` directly. They take a separate valuation `V : MultiplicativeIntegerValuation Kˣ` (a library notion), a uniformizer ϖ of `V`, and a hypothesis `hzero` saying that the elements of valuation zero for `V` are exactly the image of O^*. The decomposition of K^* holds only under that hypothesis.
- The decomposition depends on the chosen ϖ; the integer factor is the exponent of ϖ.
- Finiteness of the residue field is an instance hypothesis of both decompositions; the inclusion O^* → K^* and the lemma converting `hzero` do not use it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/TeichmullerDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `601b9e771af7c7fed3572097ddc59bf36265aa90177325b98612ce1f3433d86e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
