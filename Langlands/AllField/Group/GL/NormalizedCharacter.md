# The residue-normalized determinant character (all local fields)

`Langlands.AllField.Group.GL.NormalizedCharacter` ports the part of the p-adic module
`Langlands.Group.GL.NormalizedCharacter` that the unequal-rank JPSS functional equation
uses, for an arbitrary field `F` with nonarchimedean local-field data
`T : LocalFieldData F` (any characteristic). All declarations are in namespace
`Langlands.LocalFieldData`.

## Declarations

- `normalizedAbsHom`: `T.normalizedAbs` as a monoid-with-zero map `F →*₀ ℝ≥0`;
  `normalizedAbsHom_coe` is its value.
- `normalizedAbsUnits`: its restriction `Fˣ →* ℝ≥0ˣ`; `normalizedAbsUnits_coe` is its value.
- `determinantNorm n`: the character `g ↦ |det g|` of `GL_n(F)`, with the
  residue-cardinality normalization; `determinantNorm_coe` is its value and
  `determinantNorm_scalar` gives `|det (a·1)| = |a|^n`.
- `normalizedAbs_eq_one_iff_discreteValuation`: `|x| = 1` exactly when the discrete
  valuation of `x` is `1` (also for `x = 0`).
- `continuous_normalizedAbsHom`: continuity for the topology `T.topology`.
- `isOpen_ker_normalizedAbsUnits`, `isOpen_ker_determinantNorm`: the kernels of
  `normalizedAbsUnits` and `determinantNorm n` are open.

## Proofs and changes from the p-adic module

The algebraic declarations and proofs are those of the original. The original proves
continuity through the canonical norm of a finite extension of `ℚ_p`; here
`continuous_normalizedAbsHom` uses `continuous_normalizedAbs` from
`Langlands.AllField.LocalField.Foundation`. `isOpen_ker_normalizedAbsUnits` identifies
the kernel with the valuation sphere `{x | v(x) = 1}`, which is open in the valuative
topology (`Valuation.isOpen_sphere`). The p-adic lemmas that compare the norm with the
canonical spectral norm, and the canonical-topology specializations, are not needed and
are omitted.
