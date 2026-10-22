# All complex unramified determinant characters

This module constructs the full family of unramified complex characters of the
multiplicative group of a finite extension of the p-adic field, and their actual
determinant pullbacks to general linear groups. The field universe `uF` is
arbitrary. Complex numbers have their ordinary topology; the field and matrix
unit groups use the supplied `T : F.TopologicalData`. Specialization to
`F.canonicalTopologicalData` needs no additional arithmetic input.

## Provenance and normalization

The source is Guy Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique*, Invent. Math. 139 (2000), 439–455, registered as
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
Section 1.1 and footnote 1, printed p.439, use continuous complex
quasicharacters and send geometric Frobenius to a uniformizer. Section 1.2(2),
p.440, twists the general-linear representation by a character composed with
determinant. Section 1.3 on the same page uses all unramified quasicharacters.

The implementation is derived infrastructure for those conventions, not a proof
of a correspondence claim in that article. It reuses the published normalized
order from `LocalField/Normalization/Proof`, the norm-one open subgroup from
`Group/GL/NormalizedCharacter`, the actual matrix determinant, and Mathlib's
integer-power homomorphism. Order of a uniformizer is **+1**. Thus the parameter
`z` is the uniformizer value, and the character is `a ↦ z ^ ord(a)`; there is no
extra sign or restriction of `z` to positive real numbers. The source's word
“character” requires unitarity; the Lean names `unramifiedCharacter` also include
nonunitary quasicharacters, as their explicit type `z : ℂˣ` indicates.

## Constructions and implemented arguments

- `ordUnits` is the genuine normalized order on `F.Carrierˣ`, with target
  `Multiplicative ℤ`. The order multiplication law proves its homomorphism law.
  `ord_eq_zero_iff_normalizedAbs` and `ker_ordUnits` identify its kernel with
  the normalized absolute-value-one subgroup. The former follows from the
  actual discrete valuation using the inverse logarithm/exponential identity
  away from zero. All inputs are units, so zero is excluded.
- `unramifiedCharacter z` composes `ordUnits` with integer powers of `z`.
  `unramifiedCharacterHom`, the identity/product/inverse laws, and the explicit
  evaluation formula describe the full multiplicative family. The order-zero
  kernel lies in each character kernel. The published open norm-one subgroup
  therefore proves `isOpen_ker_unramifiedCharacter`. The character is constant
  near the identity; the topological-group translation theorem proves
  continuity. `unramifiedCharacterContinuous` bundles this result.
- `uniformizerUnit` abbreviates the shared constructor
  `Langlands.LocalFactor.PadicAbelian.uniformizerUnit` from
  `LocalField/Uniformizer`, retaining the existing chosen uniformizer.
  Evaluation at it recovers `z`, proving injectivity.
  `IsUnramifiedCharacter χ` is the proposition that the normalized norm-one
  subgroup lies in `χ.ker`. No continuity premise is included. To establish
  `eq_unramifiedCharacter`, the proof divides any `a` by the uniformizer to the
  power `ord(a)`. The resulting element has order zero, hence character value
  one. This proves `χ(a) = χ(uniformizer) ^ ord(a)`.
  `unramifiedCharacterEquiv` consequently parametrizes **all** such field
  characters by `ℂˣ`, and `continuous_of_isUnramifiedCharacter` supplies
  continuity rather than assuming it.
- `determinantUnramifiedCharacter n z` composes the constructed character with
  the actual determinant on `GeneralLinear n F.Carrier`. Its kernel is open by
  continuous preimage, contains the determinant kernel, and also contains the
  normalized determinant norm-one subgroup. Its identity/product/inverse and
  scalar-matrix laws follow from the corresponding homomorphism laws.
  `determinantUnramifiedCharacterContinuous` uses the actual matrix topology.
- `realPowerCharacter_eq_unramifiedCharacter` applies the established field
  character parametrization to the published normalized real-power character.
  `realPowerDeterminant_eq_unramifiedCharacter` composes that equality with
  determinant. The parameter is explicitly the value of that real-power
  character at the chosen uniformizer. Thus the previous real-power family is
  included in the full complex family; this theorem does not choose a complex
  logarithm or a complex exponent.
- `norm_unramifiedCharacter` and `norm_determinantUnramifiedCharacter` prove
  pointwise norm one from `‖z‖ = 1` by the norm of integer powers.
  `norm_unramifiedCharacter_iff` proves the converse for field characters by
  evaluating at the uniformizer.

## Scope

The only choices are those already in the supplied local-field realization and
its chosen uniformizer. No field or topology is replaced by an arbitrary
surrogate. The construction works for every natural matrix rank, including
zero; later supercuspidal lattices use positive ranks. It does not classify all
characters of the general linear group: it constructs the determinant pullbacks
of all unramified field characters. It does not construct representation orbits,
prove their finiteness, or assert compatibility with reciprocity or a Langlands
correspondence. Those are separate consumers and obligations. Every theorem in
this pair is an intrinsic construction law with an implemented Lean proof.
