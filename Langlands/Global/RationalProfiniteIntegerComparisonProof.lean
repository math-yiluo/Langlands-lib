import Langlands.Global.RationalProfiniteIntegerComparison
import Langlands.Global.IntegralFiniteAdelePadicProduct
import Langlands.Global.ProfiniteIntegerPadicProductComparisonProof
import Langlands.Global.IntegralFiniteAdeleRationalizationProof
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section

open scoped TensorProduct

namespace Langlands.Global

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The normalized topological integral comparison and its rational extension. -/
theorem rationalProfiniteIntegerAdeleComparison :
    RationalProfiniteIntegerAdeleComparison := by
  obtain ⟨ep, hep, hep_inv, hep_int⟩ := profiniteIntegerPadicProductComparison
  obtain ⟨E, hE⟩ := integralFiniteAdeleRationalization
  let e₀ := ep.trans rationalPadicProductIntegralEquiv
  refine ⟨e₀, continuous_rationalPadicProductIntegralEquiv.comp hep,
    hep_inv.comp continuous_rationalPadicProductIntegralEquiv_symm, ?_, ?_⟩
  · intro z
    change (rationalPadicProductIntegralEquiv
      (ep (ProfiniteIntegerRing.intCastHom z)) : FiniteAdeles ℚ) = _
    rw [show ep (ProfiniteIntegerRing.intCastHom z) =
      (fun p : Nat.Primes => (z : PadicInt p.val)) from funext (hep_int z)]
    exact rationalPadicProductIntegralEquiv_intCast z
  · refine ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ)
      e₀.toIntAlgEquiv).trans E, ?_⟩
    intro q a
    simpa using hE q (e₀ a)

end Langlands.Global
