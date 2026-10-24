import Langlands.Representation.Character.TransportStatement
import Langlands.LinearAlgebra.FiniteRankTranspose
import Langlands.Representation.Hecke.SmoothTranspose
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.CuspidalSupport.GroupTransport

noncomputable section

namespace Langlands.Character

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- Right translation controls the integrated action on a translated input. -/
theorem integratedAction_right_input [IsMulRightInvariant μ]
    (a : G) (f : SchwartzBruhat G) (v : V) :
    Hecke.integratedAction μ ρ hρ f (ρ a v) =
      Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.rightTranslate a⁻¹ f) v := by
  have heq :
      (Hecke.actionIntegrand ρ hρ (Hecke.TestFunction.rightTranslate a⁻¹ f) v).comp
          (fun x => x * a) (measurePreserving_mul_right μ a).measurable =
        Hecke.actionIntegrand ρ hρ f (ρ a v) := by
    ext x
    simp [map_mul, Module.End.mul_apply]
  have h := AlgebraicIntegral.integral_comp_measurePreserving
    (Hecke.actionIntegrand ρ hρ (Hecke.TestFunction.rightTranslate a⁻¹ f) v)
    (fun x => x * a) (measurePreserving_mul_right μ a)
  rw [heq] at h
  exact h

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The full algebraic transpose image, not just its smooth part, is smooth. -/
theorem integratedAction_dualMap_range_le_smoothVectors [IsMulRightInvariant μ]
    (f : SchwartzBruhat G) :
    (Hecke.integratedAction μ ρ hρ f).dualMap.range ≤ smoothVectors ρ.dual := by
  classical
  obtain ⟨K, _, _, hf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hfK := hf f (Finset.mem_singleton_self f)
  rintro _ ⟨ℓ, rfl⟩
  refine ⟨K, ?_⟩
  intro k
  ext v
  change ℓ (Hecke.integratedAction μ ρ hρ f (ρ (k : G)⁻¹ v)) =
    ℓ (Hecke.integratedAction μ ρ hρ f v)
  rw [integratedAction_right_input μ ρ hρ]
  simp only [inv_inv]
  rw [((Hecke.TestFunction.mem_biInvariant_iff _ _ f).mp hfK).2 k]

variable [IsMulLeftInvariant μ]

/-- The actual smooth contragredient character is obtained by inversion. -/
theorem distribution_smoothContragredient [IsInvInvariant μ]
    (hρa : IsAdmissible ρ) (hdual : IsAdmissible (smoothContragredient ρ))
    (f : SchwartzBruhat G) :
    distribution μ (smoothContragredient ρ) hdual f =
      distribution μ ρ hρa (Hecke.TestFunction.inversion f) := by
  let : IsMulRightInvariant μ := by
    rw [← inv_eq_self μ]
    infer_instance
  let T := finiteRankIntegratedAction μ ρ hρa (Hecke.TestFunction.inversion f)
  have hT : T.val.dualMap.range ≤ smoothVectors ρ.dual :=
    integratedAction_dualMap_range_le_smoothVectors μ ρ hρa.1 _
  have heq : finiteRankIntegratedAction μ (smoothContragredient ρ) hdual f =
      FiniteRankEnd.transposeOn T (smoothVectors ρ.dual) hT := by
    apply Subtype.ext
    ext ℓ v
    exact Hecke.integratedAction_smoothDualPairing μ ρ hρa.1 f ℓ v
  rw [distribution_apply, heq, FiniteRankEnd.trace_transposeOn]
  rfl

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [IsMulLeftInvariant μ] in
/-- The actual integrated operator for automorphism pullback is a change of variables. -/
theorem integratedAction_comp_automorphism (e : G ≃ₜ* G)
    (he : MeasurePreserving e μ μ) (hpull : IsSmooth (ρ.comp e.toMonoidHom))
    (f : SchwartzBruhat G) (v : V) :
    Hecke.integratedAction μ (ρ.comp e.toMonoidHom) hpull f v =
      Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.pullback e.symm.toHomeomorph f) v := by
  have heq :
      (Hecke.actionIntegrand ρ hρ
          (Hecke.TestFunction.pullback e.symm.toHomeomorph f) v).comp e he.measurable =
        Hecke.actionIntegrand (ρ.comp e.toMonoidHom) hpull f v := by
    ext x
    change f (e.symm (e x)) • ρ (e x) v = f x • ρ (e x) v
    rw [e.symm_apply_apply]
  have h := AlgebraicIntegral.integral_comp_measurePreserving
    (Hecke.actionIntegrand ρ hρ (Hecke.TestFunction.pullback e.symm.toHomeomorph f) v) e he
  rw [heq] at h
  exact h

/-- Character transport follows from equality of the actual finite-rank operators. -/
theorem distribution_comp_automorphism (e : G ≃ₜ* G)
    (he : MeasurePreserving e μ μ) (hρa : IsAdmissible ρ)
    (hpull : IsAdmissible (ρ.comp e.toMonoidHom)) (f : SchwartzBruhat G) :
    distribution μ (ρ.comp e.toMonoidHom) hpull f =
      distribution μ ρ hρa (Hecke.TestFunction.pullback e.symm.toHomeomorph f) := by
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  ext v
  exact integratedAction_comp_automorphism μ ρ hρa.1 e he hpull.1 f v

end Langlands.Character

namespace Langlands

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

theorem characterTransport : CharacterTransportStatement.{uG,uV} := by
  constructor
  · intro G _ _ _ _ _ _ _ _ μ _ _ _ V _ _ ρ hρ
    have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
        IsCompact (L : Set G) ∧ L ≤ K := by
      intro K
      obtain ⟨L, hLK, hLc, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
      exact ⟨L, hLc, hLK⟩
    have hdual := isAdmissible_smoothContragredient_of_compact_cofinal hcofinal ρ hρ
    exact ⟨hdual, Character.distribution_smoothContragredient μ ρ hρ hdual⟩
  · intro G _ _ _ _ _ _ _ _ μ _ _ e he V _ _ ρ hρ
    have hpull := isAdmissible_comp_continuousMulEquiv ρ e hρ
    exact ⟨hpull, Character.distribution_comp_automorphism μ ρ e he hρ hpull⟩

end Langlands
