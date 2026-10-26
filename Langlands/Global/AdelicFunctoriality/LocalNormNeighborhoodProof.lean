import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhoodStatement
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood

/-! # Combined local norm neighborhood theorem -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- The actual finite and infinite local norm images are neighborhoods of one. -/
theorem localNormNeighborhood : LocalNormNeighborhoodStatement.{u,v} := by
  intro K _ _ L _ _ _
  constructor
  · intro p q h
    let _ := h
    exact range_finiteLocalNorm_mem_nhds (K := K) (L := L) p q
  · intro p q h
    let _ := h
    exact range_infiniteLocalNorm_mem_nhds (K := K) (L := L) p q

end Langlands.Global.AdelicFunctoriality
