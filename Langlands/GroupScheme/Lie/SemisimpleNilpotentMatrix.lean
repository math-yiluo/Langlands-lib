import Langlands.GroupScheme.Lie.SemisimpleElement

/-! # Vanishing of geometrically semisimple nilpotent matrices -/

noncomputable section

universe u

namespace Langlands.GroupScheme.Lie

/-- A nilpotent geometrically semisimple matrix vanishes over the ground field. -/
theorem IsGeometricallySemisimpleMatrix.eq_zero_of_isNilpotent
    {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n k} (hs : IsGeometricallySemisimpleMatrix M)
    (hn : IsNilpotent M) : M = 0 := by
  obtain ⟨d, hd⟩ := hn
  have hpow : (M.map (algebraMap k (AlgebraicClosure k))) ^ d = 0 := by
    rw [← Matrix.map_pow, hd, Matrix.map_zero _ (map_zero _)]
  have hnil : IsNilpotent
      (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) := by
    refine ⟨d, ?_⟩
    rw [← Matrix.toLin'_pow, hpow, map_zero]
  have hz := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hs
  have hmap : M.map (algebraMap k (AlgebraicClosure k)) = 0 :=
    Matrix.toLin'.injective (by simpa only [map_zero] using hz)
  apply Matrix.ext
  intro i j
  apply (algebraMap k (AlgebraicClosure k)).injective
  simpa only [Matrix.map_apply, Matrix.zero_apply, map_zero] using
    congrArg (fun N => N i j) hmap


end Langlands.GroupScheme.Lie
