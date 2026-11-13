import Langlands.Representation.Character.ModularTransportStatement
import Langlands.LinearAlgebra.FiniteRankTranspose
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.HarmonicAnalysis.Distribution.RenardModularProof

noncomputable section

namespace Langlands.Character

open HarmonicAnalysis MeasureTheory
open scoped NNReal

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The test function obtained by inverting a left Haar density. -/
def modularInversionTest (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun g => f g⁻¹ * (((Distribution.renardModular g : ℝ)⁻¹ : ℝ) : ℂ),
    (f.locallyConstant.comp_continuous continuous_inv).mul
      ((Distribution.RenardModular.regularity G).2.1.comp
        (fun r : ℝ≥0 => (((r : ℝ)⁻¹ : ℝ) : ℂ))),
    (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mul_right⟩

omit [MeasurableSpace G] [BorelSpace G] in
@[simp]
theorem modularInversionTest_apply (f : SchwartzBruhat G) (g : G) :
    modularInversionTest f g =
      f g⁻¹ * (((Distribution.renardModular g : ℝ)⁻¹ : ℝ) : ℂ) := rfl

variable (μ : Measure G) [μ.IsHaarMeasure]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Right translation of the input of an integrated operator, with its Haar factor. -/
theorem integratedAction_right_input_modular (a : G) (f : SchwartzBruhat G) (v : V) :
    Hecke.integratedAction μ ρ hρ f (ρ a v) =
      ((Distribution.renardModular a⁻¹ : ℝ) : ℂ) •
        Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.rightTranslate a⁻¹ f) v := by
  apply Module.eval_apply_injective ℂ
  apply LinearMap.ext
  intro L
  change L (Hecke.integratedAction μ ρ hρ f (ρ a v)) = _
  rw [map_smul]
  change L (Hecke.integratedAction μ ρ hρ f (ρ a v)) =
    ((Distribution.renardModular a⁻¹ : ℝ) : ℂ) *
      L (Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.rightTranslate a⁻¹ f) v)
  rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual]
  let s : SchwartzBruhat G :=
    ⟨fun x => f (x * a⁻¹) * L (ρ x v),
      ((Hecke.TestFunction.rightTranslate a⁻¹ f).locallyConstant).mul
        ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp L),
      (Hecke.TestFunction.rightTranslate a⁻¹ f).hasCompactSupport.mul_right⟩
  have ht := (Distribution.RenardModular.translation G μ).2 s a⁻¹ 1
  simpa [s, Distribution.ofMeasure_apply, map_mul, Module.End.mul_apply] using ht

/-- The full algebraic transpose image is smooth, using compact right invariance. -/
theorem integratedAction_dualMap_range_le_smoothVectors_modular
    (f : SchwartzBruhat G) :
    (Hecke.integratedAction μ ρ hρ f).dualMap.range ≤ smoothVectors ρ.dual := by
  classical
  obtain ⟨K, _, hK, hf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hfK := hf f (Finset.mem_singleton_self f)
  rintro _ ⟨L, rfl⟩
  refine ⟨K, ?_⟩
  intro k
  ext v
  change L (Hecke.integratedAction μ ρ hρ f (ρ (k : G)⁻¹ v)) =
    L (Hecke.integratedAction μ ρ hρ f v)
  rw [integratedAction_right_input_modular μ ρ hρ]
  simp only [inv_inv]
  rw [((Hecke.TestFunction.mem_biInvariant_iff _ _ f).mp hfK).2 k]
  have hk := (Distribution.RenardModular.regularity G).2.2.2
    K.toSubgroup hK (k : G) k.property
  simp [hk]

/-- Weighted inversion is adjoint to the actual smooth-contragredient operator. -/
theorem integratedAction_smoothDualPairing_modular (f : SchwartzBruhat G)
    (L : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ
        (Hecke.integratedAction μ (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) f L) v =
      smoothDualPairing ρ L
        (Hecke.integratedAction μ ρ hρ (modularInversionTest f) v) := by
  let ev : SmoothDual ρ →ₗ[ℂ] ℂ :=
    (Module.Dual.eval ℂ V v).comp (smoothDualPairing ρ)
  change ev (Hecke.integratedAction μ (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) f L) = _
  rw [Hecke.integratedAction_dual, Hecke.integratedAction_dual]
  change (∫ g, f g * smoothDualPairing ρ L (ρ g⁻¹ v) ∂μ) =
    ∫ g, modularInversionTest f g * smoothDualPairing ρ L (ρ g v) ∂μ
  let s : SchwartzBruhat G :=
    ⟨fun g => f g⁻¹ * smoothDualPairing ρ L (ρ g v),
      (f.locallyConstant.comp_continuous continuous_inv).mul
        ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp (smoothDualPairing ρ L)),
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).mul_right⟩
  obtain ⟨d, hd, _, hi⟩ := Distribution.RenardModular.inversionDensity G μ
  have ht := LinearMap.congr_fun hi s
  change (∫ g, s g⁻¹ ∂μ) = ∫ g, d g * s g ∂μ at ht
  simpa only [s, inv_inv, hd, modularInversionTest_apply, Complex.ofReal_inv, mul_left_comm, mul_comm,
    mul_assoc] using ht

/-- Transpose and full-image restriction compute the weighted dual character. -/
theorem distribution_smoothContragredient_modular
    (hρa : IsAdmissible ρ) (hdual : IsAdmissible (smoothContragredient ρ))
    (f : SchwartzBruhat G) :
    distribution μ (smoothContragredient ρ) hdual f =
      distribution μ ρ hρa (modularInversionTest f) := by
  let T := finiteRankIntegratedAction μ ρ hρa (modularInversionTest f)
  have hT : T.val.dualMap.range ≤ smoothVectors ρ.dual :=
    integratedAction_dualMap_range_le_smoothVectors_modular μ ρ hρa.1 _
  have heq : finiteRankIntegratedAction μ (smoothContragredient ρ) hdual f =
      FiniteRankEnd.transposeOn T (smoothVectors ρ.dual) hT := by
    apply Subtype.ext
    ext L v
    exact integratedAction_smoothDualPairing_modular μ ρ hρa.1 f L v
  rw [distribution_apply, heq, FiniteRankEnd.trace_transposeOn]
  rfl

end Langlands.Character

namespace Langlands

universe uG uV

/-- Renard III.1.12 Example, with the exact published universes and hypotheses. -/
theorem characterContragredientModular : CharacterContragredientModularStatement.{uG,uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ V _ _ ρ hρ
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hLc, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hLc, hLK⟩
  have hdual := isAdmissible_smoothContragredient_of_compact_cofinal hcofinal ρ hρ
  refine ⟨hdual, fun f => ⟨Character.modularInversionTest f, ?_, ?_⟩⟩
  · intro g
    rfl
  · exact Character.distribution_smoothContragredient_modular μ ρ hρ hdual f

end Langlands
