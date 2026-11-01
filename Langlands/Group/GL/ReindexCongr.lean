import Langlands.Group.GL.Basic

/-! Reflexive finite-rank reindexing, shared by derivative and Rankin–Selberg modules. -/

namespace Langlands.RankinSelberg

/-- Reindexing along `finCongr` of a reflexive equation is the identity. -/
@[simp] theorem reindex_finCongr_self {R : Type*} [CommRing R] {k : ℕ} (h : k = k)
    (g : Langlands.GeneralLinear k R) : GeneralLinear.reindex (finCongr h) g = g := by
  ext i j
  simp [GeneralLinear.reindex]

end Langlands.RankinSelberg
