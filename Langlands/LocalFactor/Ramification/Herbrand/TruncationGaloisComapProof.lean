import Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof
import Langlands.LocalFactor.Ramification.Herbrand.TruncationQuotientStatement

namespace Langlands.Ramification.Kummer

universe u

/-- Through the transitivity index, the Galois inclusion pulls back the absolute upper
ramification groups without changing their indices. -/
theorem truncationGaloisComap : TruncationGaloisComapStatement.{u} := by
  intro p _ F E μ htrans x hx_lower hx_upper
  have hψ := herbrandPsiTruncation p F E μ htrans x hx_lower hx_upper
  apply Subgroup.ext
  intro τ
  simpa only [Subgroup.mem_comap, hψ] using!
    HerbrandBridge.intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff E hx_lower τ

end Langlands.Ramification.Kummer
