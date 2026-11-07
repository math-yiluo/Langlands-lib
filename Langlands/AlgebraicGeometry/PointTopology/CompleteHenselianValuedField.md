# Complete valued fields are henselian

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claims on adelic levels
(`Langlands.Global.AdelicSpaceLevelTopologyStatement`). Conrad's henselian valued fields
(`IsHenselianValuedField`, printed p.14) are the fields whose absolute value extends uniquely to
every algebraic extension. Conrad remarks that "the complete case is all we will actually need".
This module proves that complete fields are henselian in the two cases that occur for global
fields. It is a standard fact, not a numbered statement of the paper.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointTopology.CompleteHenselian`; `K` is a nontrivially
normed field.

- `toAlgebraNorm`, `toAlgebraNorm_apply`: an absolute value on a `K`-algebra `L` that extends the
  norm of `K` is a `K`-algebra norm. The construction is the one in Mathlib's
  `spectralNorm_unique_field_norm_ext`.
- `algebraNorm_eq` (requires `CompleteSpace K`): two power-multiplicative `K`-algebra norms on an
  algebraic extension `L` are equal. The proof is Mathlib's proof of `spectralNorm_unique`, with
  the spectral norm replaced by an arbitrary power-multiplicative norm. On each finite
  subextension `K⟮x⟯` the two norms are equivalent, since linear maps between
  finite-dimensional spaces over a complete field are continuous. Then
  `eq_of_powMul_faithful` gives equality. No non-archimedean hypothesis is used.
- `absoluteValue_eq`: **uniqueness** over a complete field. Two absolute values on an algebraic
  extension that extend the norm agree.
- `isHenselianValuedField_of_isUltrametricDist`: a complete non-archimedean field is a henselian
  valued field. The extension is Mathlib's multiplicative spectral norm `spectralMulAlgNorm`,
  which extends the norm (`spectralNorm_extends`).
- `isHenselianValuedField_of_isometry`: a complete field with an isometric ring map `φ : K → ℂ` is
  a henselian valued field. An algebraic extension `L` embeds in `ℂ` over `K`
  (`IsAlgClosed.lift`), and `y ↦ ‖σ y‖` is an absolute value extending the norm.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, definition of henselian
  valued fields and the remark on complete fields, printed p.14.
