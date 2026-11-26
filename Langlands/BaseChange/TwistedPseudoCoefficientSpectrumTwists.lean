import Langlands.BaseChange.TwistedCharacter.InductionTwist
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.Group.GL.BlockDeterminant
import Langlands.AllField.Group.GL.PadicBlocks

/-! # Stability of the spans of twisted characters under unramified twisting -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uG u v z

section Spectrum

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G) (ψ : G →* ℂˣ) (hψ : IsUnramifiedCharacter ψ) (hψθ : ∀ g, ψ (θ g) = ψ g)

include hψθ

set_option maxHeartbeats 800000 in
/-- If a class of irreducibles is stable under an unramified twist, the same holds for
its span of twisted distributions. -/
theorem characterTwistDistribution_map_twistedSpectrumSpan_le
    (P : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W], Representation ℂ G W → Prop)
    (hP : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G W), P W ρ → P W (twist ψ ρ)) :
    (twistedSpectrumSpan μ θ P).map (characterTwistDistribution ψ hψ.isOpen_ker) ≤
      twistedSpectrumSpan μ θ P := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro d ⟨W, iAdd, iMod, ρ, hρ, A, hirr, hPρ, hd⟩
  let := iAdd
  let := iMod
  let D := characterTwistDistribution ψ hψ.isOpen_ker
  have ht := (isAdmissible_twist_iff ψ ρ hψ.isOpen_ker).mpr hρ
  let B := twistTwistedIntertwiner θ ψ hψθ A
  have hB : D (twistedDistribution μ ρ hρ A.toLinearMap) =
      twistedDistribution μ (twist ψ ρ) ht B.toLinearMap :=
    (twistedDistribution_twist_eq_comp μ ρ hρ A.toLinearMap ψ hψ.isOpen_ker ht).symm
  apply Submodule.mem_comap.mpr
  have hm := twistedDistribution_mem_twistedSpectrumSpan μ θ P ht
    ((isIrreducible_twist_iff ψ ρ).mpr hirr) (hP W ρ hPρ) B
  exact ((congrArg D hd).trans hB).symm ▸ hm

variable {V : Type z} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V)

/-- The orbit span is stable under every invariant unramified twist. -/
theorem characterTwistDistribution_map_twistedOrbitSpan_le :
    (twistedOrbitSpan μ θ τ).map (characterTwistDistribution ψ hψ.isOpen_ker) ≤
      twistedOrbitSpan μ θ τ :=
  characterTwistDistribution_map_twistedSpectrumSpan_le μ θ ψ hψ hψθ _
    (fun _ _ _ _ h => h.twist ψ hψ hψθ)

/-- The span of essentially tempered representations outside the orbit is stable. -/
theorem characterTwistDistribution_map_twistedOtherEssentiallyTemperedSpan_le :
    (twistedOtherEssentiallyTemperedSpan μ θ τ).map (characterTwistDistribution ψ hψ.isOpen_ker) ≤
      twistedOtherEssentiallyTemperedSpan μ θ τ := by
  apply characterTwistDistribution_map_twistedSpectrumSpan_le μ θ ψ hψ hψθ
  intro W _ _ ρ ⟨hn, η, hη, hηθ, ht⟩
  refine ⟨fun h => hn ((isUnramifiedTwistOf_twist_iff ψ hψ hψθ).mp h), η * ψ⁻¹,
    hη.mul hψ.inv, fun g => ?_, ?_⟩
  · change η (θ g) * (ψ (θ g))⁻¹ = η g * (ψ g)⁻¹
    rw [hηθ, hψθ]
  · rwa [← twist_twist, twist_inv_twist]

/-- Unramified twists preserve absence of vectors fixed by a compact open subgroup. -/
theorem characterTwistDistribution_map_twistedInvisibleSpan_le (J : OpenSubgroup G)
    (hJ : IsCompact (J : Set G)) :
    (twistedInvisibleSpan.{uG,z} μ θ J).map (characterTwistDistribution ψ hψ.isOpen_ker) ≤
      twistedInvisibleSpan.{uG,z} μ θ J := by
  apply characterTwistDistribution_map_twistedSpectrumSpan_le μ θ ψ hψ hψθ
  intro W _ _ ρ h
  rwa [fixedVectors_twist_eq_of_le_ker ψ ρ J.toSubgroup (fun g hg => hψ _ hJ g hg)]

end Spectrum

section ProperInduction

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] [ValuativeRel E] [IsNonarchimedeanLocalField E]
  {n : ℕ} (σ : E ≃ₐ[F] E)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

set_option maxHeartbeats 800000 in
/-- The proper-induction span is stable under an invariant unramified character of
`GL_n`. Its restriction to a standard parabolic factors through the Levi projection. -/
theorem characterTwistDistribution_map_sigmaProperInducedSpan_le (i : Fin n)
    (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
    (hψθ : ∀ g, ψ (entrywiseAut σ n g) = ψ g) :
    (sigmaProperInducedSpan.{u,v,z} σ μ).map (characterTwistDistribution ψ hψ.isOpen_ker) ≤
      sigmaProperInducedSpan.{u,v,z} σ μ := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro d ⟨B, hB, X, iAdd, iMod, Ξ, hΞ, hΞirr, BΞ, hI, hval⟩
  let := iAdd
  let := iMod
  let P := B.parabolic E
  let p := B.leviProjection E
  let η := ψ.comp (B.leviEmbedding E)
  have hη : IsUnramifiedCharacter η :=
    hψ.comp_of_continuous _ (B.leviEmbeddingContinuous E).continuous
  have hηθ (m : B.Levi E) : η (leviAut σ B m) = η m := by
    change ψ (B.leviEmbedding E (leviAut σ B m)) = ψ (B.leviEmbedding E m)
    rw [← entrywiseAut_leviEmbedding, hψθ]
  have hηp (x : P) : ψ x = η (p x) := by
    change ψ (x : GeneralLinear n E) = ψ (B.leviEmbedding E (p x))
    have hdet : determinant (x : GeneralLinear n E) = determinant (B.leviEmbedding E (p x)) := by
      let y : B.parabolic E := B.leviInParabolic E (p x)
      change determinant x.val = determinant y.val
      rw [determinant_blockParabolic B x, determinant_blockParabolic B y]
      simp only [y, B.leviProjection_section, p]
    rw [eq_detOrderCharacter_of_isUnramified E i ψ hψ]
    simp only [determinantOrderHom, MonoidHom.comp_apply, hdet]
  obtain ⟨hI', hd⟩ := characterTwistDistribution_induced μ (entrywiseAut σ n)
    (continuous_entrywiseAut_of_isModuleTopology σ n)
    (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n) P
    (entrywiseAut_mem_parabolic_iff σ B) p (leviAut σ B) (leviProjection_entrywiseAut σ B)
    Ξ BΞ ψ hψ.isOpen_ker hψθ η hηθ hηp hI
  change characterTwistDistribution ψ hψ.isOpen_ker
    (twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ).toLinearMap) =
    twistedDistribution μ _ hI' (TwistedPaleyWiener.inducedSigmaIntertwiner σ B (twist η Ξ)
      (twistTwistedIntertwiner (leviAut σ B) η hηθ BΞ)).toLinearMap at hd
  let T := LocalFieldData.ofInstances E
  let : IsTopologicalGroup (B.Levi E) := T.leviTopologicalGroup B
  let : T2Space (B.Levi E) := T.leviT2Space B
  let : LocallyCompactSpace (B.Levi E) := T.leviLocallyCompactSpace B
  have : ∀ j : Fin B.length, TotallyDisconnectedSpace (GeneralLinear (B.size j) E) :=
    fun j => LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size j)
  have : TotallyDisconnectedSpace (B.Levi E) := inferInstance
  apply Submodule.mem_comap.mpr
  have hm := twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB (twist η Ξ)
    ((isAdmissible_twist_iff η Ξ hη.isOpen_ker).mpr hΞ) ((isIrreducible_twist_iff η Ξ).mpr hΞirr)
    (twistTwistedIntertwiner (leviAut σ B) η hηθ BΞ) hI'
  exact ((congrArg (characterTwistDistribution ψ hψ.isOpen_ker) hval).trans hd).symm ▸ hm

end ProperInduction

end Langlands.BaseChange
