import Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof
import Langlands.LocalFactor.Ramification.Herbrand.TruncationQuotientStatement

namespace Langlands.Ramification.Kummer

universe u

/-- Through the transitivity index, the Weil inclusion pulls back the upper
ramification groups without changing their indices. -/
theorem truncationWeilComap : TruncationWeilComapStatement.{u} := by
  intro p _ F E μ htrans x hx_lower hx_upper
  have hψ := herbrandPsiTruncation p F E μ htrans x hx_lower hx_upper
  apply Subgroup.ext
  intro w
  simpa only [Subgroup.mem_comap, hψ] using!
    HerbrandBridge.intermediateWeilMap_mem_upperGroup_iff E hx_lower w

end Langlands.Ramification.Kummer
