# All-field port of `Langlands.Representation.Shahidi.Induction`

`Langlands.AllField.Representation.Shahidi.Induction` is the all-field port of the Library module `Langlands.Representation.Shahidi.Induction`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Shahidi.Induction` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Shahidi's two-block induced representations `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`**

For positive ranks `m, n`, a complex number `s` and representations `π₁` of `GL_m(F)`
and `π₂` of `GL_n(F)`, Shahidi (1984, printed pages 67 and 72) induces
`π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)` from the standard upper parabolic of `GL_(m+n)(F)`
with Levi `GL_m × GL_n`, and compares it with the induction `I(-s, π₂ ⊗ π₁)` from the
parabolic with Levi `GL_n × GL_m`.

Both representations are the published normalized block induction
`BlockShape.productInducedOf` (respectively `TopologicalData.normalizedProductInduced`)
of a block tensor product of determinant twists. The normalizing character is the
positive square root of the explicit block modulus `|det m₁|^n / |det m₂|^m`. The
resulting covariance exponents are `(s + n)/2` and `-(s + m)/2` for the original order
and `(m - s)/2` and `(s - n)/2` for the swapped order.

The general layer works over any field with a topology and a real absolute value whose
norm-one units form an open set; for a non-archimedean local field this holds when the
absolute value is trivial on valuation units. The p-adic layer feeds the unit
`q^(-t) = exp(-t log q)` to the Library's unramified determinant characters.

## Imports from the port

- `Langlands.AllField.Group.GL.UnramifiedCharacterSupplement`
- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.Shahidi.TwoBlocks`

## Declarations

- `Langlands.LocalFieldData.residueCardinality_real_pos` (theorem): The residue cardinality `q`, as a positive real number.
- `Langlands.LocalFieldData.absUnits_eq_normalizedAbsUnits` (theorem).
- `Langlands.LocalFieldData.isOpenNormOne_of_eq_normalizedAbs` (theorem): The normalized absolute value satisfies the smoothness hypothesis of the general
  layer.
- `Langlands.LocalFieldData.determinantComplexPower` (def): `g ↦ |det g|^t` for every complex `t`: the Library's unramified determinant character
  at the nonzero complex number `q^(-t) = exp(-t log q)`.
- `Langlands.LocalFieldData.determinantComplexPower_apply` (theorem): The unramified parametrization agrees with the complex power of the positive
  normalized determinant absolute value.
- `Langlands.LocalFieldData.determinantComplexPower_eq_complexPower` (theorem).
- `Langlands.LocalFieldData.determinantComplexPower_add` (theorem).
- `Langlands.LocalFieldData.determinantComplexPower_neg` (theorem).
- `Langlands.LocalFieldData.determinantComplexPower_zero` (theorem).
- `Langlands.LocalFieldData.isOpen_ker_determinantComplexPower` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.Shahidi.complexPower`, `Langlands.Shahidi.complexPower_apply`, `Langlands.Shahidi.complexPower_zero`, `Langlands.Shahidi.complexPower_add`, `Langlands.Shahidi.complexPower_neg`, `Langlands.Shahidi.complexPower_mul`, `Langlands.Shahidi.complexPower_inv`, `Langlands.Shahidi.complexPower_pow`, `Langlands.Shahidi.complexPower_half`, `Langlands.Shahidi.complexPower_ofReal`, `Langlands.Shahidi.ker_le_ker_complexPower`, `Langlands.Shahidi.sqrt_mul_cpow_mul_cpow`, `Langlands.Shahidi.absUnits`, `Langlands.Shahidi.absUnits_apply`, `Langlands.Shahidi.determinantAbs`, `Langlands.Shahidi.determinantAbs_apply`, `Langlands.Shahidi.determinantPower`, `Langlands.Shahidi.determinantPower_apply`, `Langlands.Shahidi.determinantPower_add`, `Langlands.Shahidi.determinantPower_neg`, `Langlands.Shahidi.determinantPower_zero`, `Langlands.Shahidi.IsOpenNormOne`, `Langlands.Shahidi.isOpen_ker_determinantAbs`, `Langlands.Shahidi.isOpen_ker_determinantPower`, `Langlands.Shahidi.determinantPowerCharacter`, `Langlands.Shahidi.isOpenNormOne_of_valuation`, `Langlands.Shahidi.blockDeterminantAbs`, `Langlands.Shahidi.blockDeterminantAbs_apply`, `Langlands.Shahidi.leviModulus`, `Langlands.Shahidi.leviModulus_apply`, `Langlands.Shahidi.leviHalfModulus`, `Langlands.Shahidi.leviHalfModulus_apply`, `Langlands.Shahidi.leviHalfModulus_eq_complexPower`, `Langlands.Shahidi.leviHalfModulus_eq_one`, `Langlands.Shahidi.isOpen_ker_leviModulus`, `Langlands.Shahidi.isOpen_ker_leviHalfModulus`, `Langlands.Shahidi.leviHalfCharacter`, `Langlands.Shahidi.leviHalfCharacter_toMonoidHom`, `Langlands.Shahidi.swappedTwoBlocks`, `Langlands.Shahidi.swappedTwoBlocks_eq_rankCast`, `Langlands.Shahidi.swappedTwoBlocks_size_zero`, `Langlands.Shahidi.swappedTwoBlocks_size_one`, `Langlands.Shahidi.leviModulus_twoBlocks`, `Langlands.Shahidi.leviModulus_swappedTwoBlocks`, `Langlands.Shahidi.pairCarrier`, `Langlands.Shahidi.pairCarrier.instAddCommGroup`, `Langlands.Shahidi.pairCarrier.instModule`, `Langlands.Shahidi.pairVector`, `Langlands.Shahidi.pairTensor`, `Langlands.Shahidi.pairFamily`, `Langlands.Shahidi.pairFamily_zero`, `Langlands.Shahidi.pairFamily_one`, `Langlands.Shahidi.blockTensor_pairTensor`, `Langlands.Shahidi.blockTensor_pairFamily_twist`, `Langlands.Shahidi.swappedTwoBlocks_index`, `Langlands.Shahidi.swapRank_mem_swappedTwoBlocks_parabolic_iff`, `Langlands.Shahidi.swappedParabolicEquiv`, `Langlands.Shahidi.swappedParabolicEquiv_coe`, `Langlands.Shahidi.leviProjection_swappedParabolicEquiv`, `Langlands.Shahidi.swappedTwoBlocks_leviEmbedding`, `Langlands.Shahidi.twistedPair`, `Langlands.Shahidi.SourceSpace`, `Langlands.Shahidi.source`, `Langlands.Shahidi.sourceEval`, `Langlands.Shahidi.sourceFunction`, `Langlands.Shahidi.sourceFunction_apply`, `Langlands.Shahidi.source_eq`, `Langlands.Shahidi.source_apply`, `Langlands.Shahidi.isSmooth_source`, `Langlands.Shahidi.source_covariant`, `Langlands.Shahidi.TargetSpace`, `Langlands.Shahidi.target`, `Langlands.Shahidi.targetEval`, `Langlands.Shahidi.targetFunction`, `Langlands.Shahidi.targetFunction_apply`, `Langlands.Shahidi.target_eq`, `Langlands.Shahidi.target_apply`, `Langlands.Shahidi.isSmooth_target`, `Langlands.Shahidi.target_covariant`, `Langlands.Shahidi.target_covariant_swapRank`, `Langlands.PadicField.TopologicalData.shahidiAbsoluteValue`, `Langlands.PadicField.TopologicalData.shahidiAbsoluteValue_apply`, `Langlands.PadicField.TopologicalData.determinantAbs_eq_determinantNorm`, `Langlands.PadicField.TopologicalData.leviModulus_eq_leviModulus`, `Langlands.PadicField.TopologicalData.leviHalfModulus_eq_leviHalfModulus`, `Langlands.PadicField.TopologicalData.leviHalfCharacter_eq_leviHalfCharacter`, `Langlands.PadicField.TopologicalData.determinantComplexPower_def`, `Langlands.PadicField.TopologicalData.determinantPower_eq_determinantComplexPower`, `Langlands.PadicField.TopologicalData.determinantComplexPower_ofReal`, `Langlands.PadicField.TopologicalData.leviModulus_swappedTwoBlocks`, `Langlands.PadicField.TopologicalData.shahidiTwistedPair`, `Langlands.PadicField.TopologicalData.twistedPair_eq_shahidiTwistedPair`, `Langlands.PadicField.TopologicalData.ShahidiSourceSpace`, `Langlands.PadicField.TopologicalData.shahidiSource`, `Langlands.PadicField.TopologicalData.shahidiSourceEval`, `Langlands.PadicField.TopologicalData.shahidiSourceFunction`, `Langlands.PadicField.TopologicalData.shahidiSourceFunction_apply`, `Langlands.PadicField.TopologicalData.shahidiSource_eq`, `Langlands.PadicField.TopologicalData.shahidiSource_apply`, `Langlands.PadicField.TopologicalData.isSmooth_shahidiSource`, `Langlands.PadicField.TopologicalData.shahidiSource_covariant`, `Langlands.PadicField.TopologicalData.ShahidiTargetSpace`, `Langlands.PadicField.TopologicalData.shahidiTarget`, `Langlands.PadicField.TopologicalData.shahidiTargetEval`, `Langlands.PadicField.TopologicalData.shahidiTargetFunction`, `Langlands.PadicField.TopologicalData.shahidiTargetFunction_apply`, `Langlands.PadicField.TopologicalData.shahidiTarget_eq`, `Langlands.PadicField.TopologicalData.shahidiTarget_apply`, `Langlands.PadicField.TopologicalData.isSmooth_shahidiTarget`, `Langlands.PadicField.TopologicalData.shahidiTarget_covariant`, `Langlands.PadicField.TopologicalData.shahidiTarget_covariant_swapRank`, `Langlands.PadicField.canonicalShahidiSourceSpace`, `Langlands.PadicField.canonicalShahidiSource`, `Langlands.PadicField.canonicalShahidiTargetSpace`, `Langlands.PadicField.canonicalShahidiTarget`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
