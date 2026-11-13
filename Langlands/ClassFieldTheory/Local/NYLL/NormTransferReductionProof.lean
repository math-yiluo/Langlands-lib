import Langlands.ClassFieldTheory.Local.NYLL.NormTransferReductionStatement

/-! # The transfer equation from norm compatibility: proof

This module proves `Langlands.LocalClassField.NYLL.NormCompatibleTransferStatement`.
The only mathematical input is Mathlib's `Algebra.norm_algebraMap`: the norm of
an element of the base field is its `[E:F]`-th power.
-/

namespace Langlands.LocalClassField.NYLL

universe u v w

/-- Any pair of norm-quotient equivalences satisfying the norm clause also
satisfies the transfer clause, because the norm of an included scalar is its
`[E:F]`-th power. -/
theorem normCompatibleTransfer : NormCompatibleTransferStatement.{u, v, w} := by
  intro p _ F E L _ _ _ _ _ _ _ _ _ _ _ TF TE
  let := TF.topology
  let := TE.topology
  intro rF rE hnorm a
  rw [← hnorm, ← map_pow, ← QuotientGroup.mk_pow]
  congr 2
  apply Units.ext
  simp [Algebra.norm_algebraMap]

end Langlands.LocalClassField.NYLL
