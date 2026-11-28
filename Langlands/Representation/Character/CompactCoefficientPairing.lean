import Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof
import Langlands.Representation.Hecke.IntegratedConvolution
import Mathlib.RepresentationTheory.Invariants

/-! # Products of compact representation coefficients -/

noncomputable section

namespace Langlands.Representation.Character

open MeasureTheory HarmonicAnalysis

variable {K X Y : Type*} [Group K] [TopologicalSpace K]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- A Haar pairing of operator coefficients of two finite-dimensional smooth
compact representations vanishes if their intertwining space is zero. -/
def CompactCoefficientPairingStatement [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (μ : Measure K) [μ.IsHaarMeasure] (ρ : Representation ℂ K X) (σ : Representation ℂ K Y) : Prop :=
  IsSmooth ρ → IsSmooth σ →
  (∀ T : Representation.IntertwiningMap ρ σ, T = 0) →
  ∀ (a : Module.Dual ℂ (Module.End ℂ X)) (b : Module.Dual ℂ (Module.End ℂ Y)),
    (∫ k, a (ρ k⁻¹) * b (σ k) ∂μ) = 0

private theorem end_coefficient_columns {E : Type*} [AddCommGroup E] [Module ℂ E]
    {I : Type*} [Fintype I] (basis : Module.Basis I ℂ E)
    (a : Module.Dual ℂ (Module.End ℂ E)) (T : Module.End ℂ E) :
    a T = ∑ i, (a.comp (LinearMap.smulRightₗ (basis.coord i))) (T (basis i)) := by
  change a T = ∑ i, a ((basis.coord i).smulRight (T (basis i)))
  rw [← map_sum]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  simp_rw [← map_smul, ← map_sum, Module.Basis.coord_apply, Module.Basis.sum_repr]

variable [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]

theorem compactCoefficientPairing (μ : Measure K) [μ.IsHaarMeasure]
    (ρ : Representation ℂ K X) (σ : Representation ℂ K Y) :
    CompactCoefficientPairingStatement μ ρ σ := by
  intro hρ hσ hHom a b
  let Q := Representation.linHom ρ σ
  obtain ⟨Nρ, _, hnρ⟩ :=
    Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional ρ hρ
  obtain ⟨Nσ, _, hnσ⟩ :=
    Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional σ hσ
  have hQ : IsSmooth Q := by
    intro f
    refine ⟨Nρ ⊓ Nσ, fun k => ?_⟩
    have hkρ : k.val ∈ Nρ := k.property.1
    have hkσ : k.val ∈ Nσ := k.property.2
    apply LinearMap.ext
    intro x
    change σ k.val (f (ρ k.val⁻¹ x)) = f x
    rw [hnρ _ (Nρ.inv_mem hkρ), hnσ _ hkσ]
  let one : SchwartzBruhat K := ⟨fun _ => 1, IsLocallyConstant.const 1,
    HasCompactSupport.of_compactSpace _⟩
  have hOne : one ∈ Hecke.TestFunction.biInvariant (⊤ : Subgroup K) ⊤ :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hAve (T : X →ₗ[ℂ] Y) : Hecke.integratedAction μ Q hQ one T = 0 := by
    let A := Hecke.integratedAction μ Q hQ one T
    have hFixed := Hecke.integratedAction_mem_fixedVectors μ Q hQ hOne T
    have hInv : A ∈ Q.invariants := fun k => hFixed ⟨k, Subgroup.mem_top k⟩
    let U := Representation.invariantsEquivIntertwiningMap ρ σ ⟨A, hInv⟩
    exact congrArg (fun W : Representation.IntertwiningMap ρ σ => W.toLinearMap) (hHom U)
  have hCoefficients (x : X) (α : Module.Dual ℂ X) (y : Y) (β : Module.Dual ℂ Y) :
      (∫ k, α (ρ k⁻¹ x) * β (σ k y) ∂μ) = 0 := by
    let T : X →ₗ[ℂ] Y := α.smulRight y
    let ℓ : Module.Dual ℂ (X →ₗ[ℂ] Y) := β.comp (LinearMap.applyₗ' ℂ x)
    have heq := Hecke.integratedAction_dual μ Q hQ one T ℓ
    rw [hAve, map_zero] at heq
    rw [heq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun k => by
      change α (ρ k⁻¹ x) * β (σ k y) = (1 : ℂ) * β (σ k (α (ρ k⁻¹ x) • y))
      rw [one_mul, map_smul, map_smul, smul_eq_mul]
  classical
  let Xb := Module.finBasis ℂ X
  let Yb := Module.finBasis ℂ Y
  let α i := a.comp (LinearMap.smulRightₗ (Xb.coord i))
  let β j := b.comp (LinearMap.smulRightₗ (Yb.coord j))
  have hInt (i : Fin (Module.finrank ℂ X)) (j : Fin (Module.finrank ℂ Y)) :
      Integrable (fun k => α i (ρ k⁻¹ (Xb i)) * β j (σ k (Yb j))) μ := by
    have hα := ((Hecke.orbitMap_locallyConstant ρ (hρ (Xb i))).comp (α i)).comp_continuous
      continuous_inv
    have hβ := (Hecke.orbitMap_locallyConstant σ (hσ (Yb j))).comp (β j)
    exact (hα.continuous.mul hβ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFun (k : K) : a (ρ k⁻¹) * b (σ k) =
      ∑ i, ∑ j, α i (ρ k⁻¹ (Xb i)) * β j (σ k (Yb j)) := by
    rw [end_coefficient_columns Xb a, end_coefficient_columns Yb b, Finset.sum_mul_sum]
  simp_rw [hFun]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hInt i j)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j _ => hInt i j)]
  exact Finset.sum_eq_zero fun j _ => hCoefficients (Xb i) (α i) (Yb j) (β j)

end Langlands.Representation.Character
