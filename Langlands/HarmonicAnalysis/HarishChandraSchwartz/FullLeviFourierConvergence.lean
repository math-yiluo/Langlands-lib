import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction
import Langlands.Representation.Plancherel.CompactProductInducedCoefficients
import Langlands.Representation.Unitary.SmoothCoefficientBoundednessProof

/-! # The full-group double integral in the Fourier regularity argument -/

noncomputable section

universe uG uV

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate TensorProduct

namespace Langlands.HarishChandraSchwartz

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ] [SecondCountableTopology Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  {P M U : Subgroup Γ} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set Γ))
  (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ))
  (A : SmoothRep.{0, uG, uV} ℂ M) (μ : Measure Γ)

/-- At the full-group endpoint, the compact coefficient pairing is
integrable on the product with `K` for an integrable ambient function
and an admissible unitarizable inducing representation. -/
def FullLeviDoubleIntegrabilityStatement : Prop :=
  P = ⊤ → M = ⊤ → U = ⊥ → CompactOpenCofinal M →
    IsAdmissible A.representation → IsUnitarizable A.representation →
      ∀ f : Γ → ℂ, Integrable f μ →
      ∀ F : productInducedCoefficientObject h hU A,
        Integrable (fun x : Γ × K =>
          conj (CompactInduction.integrand h hU A K x.1 F x.2) * f x.1)
          (μ.prod (CompactInduction.measure K hK))

set_option maxHeartbeats 1000000 in
/-- On pure tensors the diagonal compact variable cancels in the dual
pairing. The remaining coefficient is bounded by unitarizability. -/
theorem fullLeviDoubleIntegrability :
    FullLeviDoubleIntegrabilityStatement h hU K hK A μ := by
  intro hP hM hbot hcof hadm hunit f hf F
  let : CompactSpace (Induction.LeftQuotient P) :=
    Induction.compactSpace_leftQuotient_of_compact_representatives P hK fun g =>
      ⟨g, hP ▸ Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩
  let E := normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
  obtain ⟨t, rfl⟩ := E.surjective F
  induction t using TensorProduct.inductionOn with
  | tmul w j =>
      let e := fullLeviGroupEquiv M hM
      let eV := fullLeviInductionEquiv h hU hP hM hbot A
      let eL := fullLeviInductionEquiv h hU hP hM hbot A.contragredient
      obtain ⟨v, rfl⟩ := eV.symm.surjective w
      obtain ⟨ℓ, rfl⟩ := eL.symm.surjective j
      let c (g : Γ) := smoothDualPairing A.representation ℓ (A.representation (e g) v)
      have hv (g : Γ) (k : K) :
          CompactInduction.integrand h hU A K g (E (eV.symm v ⊗ₜ[ℂ] eL.symm ℓ)) k = c g := by
        refine (productInducedCoefficientIntegrand_tensor h hU A (eV.symm v)
          (eL.symm ℓ) g ⟨k, Subgroup.mem_top _⟩).trans ?_
        change smoothDualPairing A.representation
          (smoothContragredient A.representation (e k) ℓ)
          (A.representation (e ((k : Γ) * g)) v) = c g
        rw [map_mul e, map_mul A.representation]
        exact smoothDualPairing_invariant (ρ := A.representation) (e k) ℓ (A.representation (e g) v)
      obtain ⟨B, _, hB⟩ := hunit.smoothCoefficient_bounded hcof hadm ℓ v
      have hc : Continuous c := (continuous_coefficient A.isSmooth v ℓ).comp e.continuous
      have hbase : Integrable (fun g => conj (c g) * f g) μ :=
        hf.bdd_mul (Complex.continuous_conj.comp hc).aestronglyMeasurable
          (Filter.Eventually.of_forall fun g => by simpa only [RCLike.norm_conj] using hB (e g))
      have hprod := hbase.mul_prod (integrable_const (1 : ℂ)
        (μ := CompactInduction.measure K hK))
      exact hprod.congr (Filter.Eventually.of_forall fun x => by
        change conj (c x.1) * f x.1 * 1 =
          conj (CompactInduction.integrand h hU A K x.1 (E (eV.symm v ⊗ₜ[ℂ] eL.symm ℓ)) x.2) *
            f x.1
        rw [mul_one]
        exact (congrArg (fun z => conj z * f x.1) (hv x.1 x.2)).symm)
  | add t s ht hs =>
      exact (ht.add hs).congr (Filter.Eventually.of_forall fun x => by
        let J := CompactInduction.integrand h hU A K x.1
        have hJ : J (E (t + s)) = J (E t) + J (E s) :=
          (congrArg J (map_add E t s)).trans (map_add J (E t) (E s))
        change conj (J (E t) x.2) * f x.1 + conj (J (E s) x.2) * f x.1 =
          conj (J (E (t + s)) x.2) * f x.1
        rw [hJ, Pi.add_apply, map_add, add_mul])

end Langlands.HarishChandraSchwartz
