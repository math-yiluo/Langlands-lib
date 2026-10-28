import Langlands.Algebra.PrimeLocalizationCriterion
import Langlands.Algebra.LocalApproximationSystem

universe uI uA uB uR uS uQ uQ'

open scoped TensorProduct

namespace Langlands.Algebra.LocalAlgebraSystem

/-- Quotient pushouts and compatible localizations establish prime localization
for the actual tensor transition map of a local algebra system. -/
theorem isPrimeLocalization_of_quotient_pushout
    {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)
    {i j : ι} (h : i ≤ j)
    {Q : Type uQ} {Q' : Type uQ'} [CommRing Q] [CommRing Q'] :
    letI := (D.baseMap i j h).toAlgebra
    ∀ [Algebra (D.base i) Q] [Algebra (D.base i) Q']
      [Algebra Q Q'] [Algebra (D.base j) Q']
      [IsScalarTower (D.base i) Q Q']
      [IsScalarTower (D.base i) (D.base j) Q']
      [_root_.Algebra.IsPushout (D.base i) Q (D.base j) Q']
      [Algebra Q (D.alg i)] [IsScalarTower (D.base i) Q (D.alg i)]
      [Algebra Q' (D.alg j)] [IsScalarTower (D.base j) Q' (D.alg j)]
      (M : Submonoid Q) (N : Submonoid Q')
      [IsLocalization M (D.alg i)] [IsLocalization N (D.alg j)],
      (D.algMap i j h).comp (algebraMap Q (D.alg i)) =
        (algebraMap Q' (D.alg j)).comp (algebraMap Q Q') →
      D.IsPrimeLocalization h := by
  let := (D.baseMap i j h).toAlgebra
  intro _ _ _ _ _ _ _ _ _ _ _ M N _ _ hQ
  let p := (IsLocalRing.maximalIdeal (D.alg j)).comap (D.ringBaseChangeMap h)
  let := (D.ringBaseChangeMap h).toAlgebra
  refine ⟨p, inferInstance, ?_⟩
  apply isLocalization_atPrime_tensor_of_isPushout_canonical M N (D.ringBaseChangeMap h)
  · ext q
    change D.ringBaseChangeMap h (algebraMap Q (D.alg i) q ⊗ₜ[D.base i] (1 : D.base j)) =
      algebraMap Q' (D.alg j) (algebraMap Q Q' q)
    simpa only [ringBaseChangeMap_tmul, map_one, mul_one, RingHom.comp_apply] using
      DFunLike.congr_fun hQ q
  · ext b
    change D.ringBaseChangeMap h ((1 : D.alg i) ⊗ₜ[D.base i] b) =
      algebraMap Q' (D.alg j) (algebraMap (D.base j) Q' b)
    simp only [ringBaseChangeMap_tmul, map_one, one_mul,
      ← IsScalarTower.algebraMap_apply]

end Langlands.Algebra.LocalAlgebraSystem
