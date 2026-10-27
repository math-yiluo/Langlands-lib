import Langlands.Representation.Classification.ParabolicConeExistenceProof
import Langlands.Representation.Classification.ParabolicConeUniquenessProof
import Langlands.Representation.Classification.ParabolicConeSubgroupProof

/-! The root/weight cone theorem for actual GL block parabolics. -/

namespace Langlands

universe uR

/-- Numerical cone existence and uniqueness, together with the matrix
containments, give the unique actual parabolic coarsening. -/
theorem glParabolicRootWeightCone : GLParabolicRootWeightConeStatement.{uR} := by
  intro n _hn B r
  obtain ⟨C, q, t, hq, hsurj, hs, ht, havg, hres⟩ := glBlockConeExists n B r
  refine ⟨C, ⟨q, t, hq, hsurj, hs, ht, havg, hres, ?_⟩, ?_⟩
  · exact glBlockCoarseningSubgroups n B C q hq hsurj hs
  · rintro D ⟨q', t', hq', hsurj', hs', ht', havg', hres', _⟩
    exact glBlockConeUnique n B r D C q' t' q t
      ⟨hq', hsurj', hs', ht', havg', hres'⟩
      ⟨hq, hsurj, hs, ht, havg, hres⟩

end Langlands
