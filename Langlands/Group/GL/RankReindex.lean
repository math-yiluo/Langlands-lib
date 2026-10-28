import Langlands.Group.GL.Basic

/-!
# Reindexing general linear groups along an equality of ranks

Shared matrix-entry, identity and continuity laws for the published `reindex`.
-/

namespace Langlands.GeneralLinear

universe u

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- The entry-preserving reindex along `finCongr h` reads entries at the cast indices. -/
@[simp]
theorem reindex_finCongr_apply (h : m = n) (g : GeneralLinear m R) (i j : Fin n) :
    (reindex (R := R) (finCongr h) g : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin m) (Fin m) R) (Fin.cast h.symm i) (Fin.cast h.symm j) := rfl

/-- The inverse entry-preserving reindex reads entries at the cast indices. -/
@[simp]
theorem reindex_finCongr_symm_apply (h : m = n) (g : GeneralLinear n R) (i j : Fin m) :
    ((reindex (R := R) (finCongr h)).symm g : Matrix (Fin m) (Fin m) R) i j =
      (g : Matrix (Fin n) (Fin n) R) (Fin.cast h i) (Fin.cast h j) := rfl

/-- Along `rfl`, the entry-preserving reindex is the identity. -/
@[simp]
theorem reindex_finCongr_rfl :
    reindex (R := R) (finCongr (rfl : n = n)) = MulEquiv.refl (GeneralLinear n R) :=
  MulEquiv.ext fun _ => Units.ext (Matrix.ext fun _ _ => rfl)

variable [TopologicalSpace R]

/-- The entry-preserving reindex is continuous. -/
theorem continuous_reindex_finCongr (h : m = n) :
    Continuous (reindex (R := R) (finCongr h)) :=
  (reindexContinuous (R := R) (finCongr h)).continuous

/-- The inverse entry-preserving reindex is continuous. -/
theorem continuous_reindex_finCongr_symm (h : m = n) :
    Continuous (reindex (R := R) (finCongr h)).symm :=
  (reindexContinuous (R := R) (finCongr h)).symm.continuous

end Langlands.GeneralLinear
