import Langlands.Representation.Smooth.RenardTensorHomStatements
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.Tactic.Group

noncomputable section

universe u v

open MeasureTheory

namespace Langlands.Renard.Smooth

/-- Uniform bi-invariance is preserved by both regular actions, which are smooth on tests. -/
theorem regularRepresentationSmooth : RegularRepresentationSmoothStatement.{u} := by
  classical
  intro G _ _ _ _ _ _
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g f hf
    obtain ⟨K, hK, hf⟩ := hf
    constructor
    · let c : G →* G := (MulAut.conj g⁻¹).toMonoidHom
      let L := K ⊓ K.comap c (IsTopologicalGroup.continuous_conj g⁻¹)
      refine ⟨L, hK.of_isClosed_subset L.isClosed inf_le_left, ?_⟩
      intro k hk k' hk' x
      have hk₁ : g⁻¹ * k * g ∈ K := by
        simpa [c] using hk.2
      convert hf _ hk₁ k' hk'.1 (g⁻¹ * x) using 1
      congr 1
      group
    · let c : G →* G := (MulAut.conj g⁻¹).toMonoidHom
      let L := K ⊓ K.comap c (IsTopologicalGroup.continuous_conj g⁻¹)
      refine ⟨L, hK.of_isClosed_subset L.isClosed inf_le_left, ?_⟩
      intro k hk k' hk' x
      have hk₂ : g⁻¹ * k' * g ∈ K := by
        simpa [c] using hk'.2
      convert hf k hk.1 _ hk₂ (x * g) using 1
      congr 1
      group
  · intro f hf
    obtain ⟨K, _, hf⟩ := hf
    refine ⟨K, ?_⟩
    intro k hk
    constructor
    · funext x
      simpa using hf k⁻¹ (K.inv_mem hk) 1 K.one_mem x
    · funext x
      simpa using hf 1 K.one_mem k hk x
  · intro f
    obtain ⟨K, _, _, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
    have hf := hK f (Finset.mem_singleton_self f)
    refine ⟨K, ?_⟩
    intro k
    apply Hecke.TestFunction.ext
    intro x
    exact hf.1 k⁻¹ x
  · intro f
    obtain ⟨K, _, _, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
    have hf := hK f (Finset.mem_singleton_self f)
    refine ⟨K, ?_⟩
    intro k
    apply Hecke.TestFunction.ext
    intro x
    change HarmonicAnalysis.GroupAction.rightTests (k : G) f x = f x
    rw [HarmonicAnalysis.GroupAction.rightTests_apply]
    exact hf.2 k x

/-- The integrated left regular Hecke action is the actual convolution product. -/
theorem leftRegularHeckeAction : LeftRegularHeckeActionStatement.{u} := by
  intro G _ _ _ _ _ _ _ _ μ _ hl T f
  apply Hecke.TestFunction.ext
  intro x
  let L : HarmonicAnalysis.SchwartzBruhat G →ₗ[ℂ] ℂ :=
    { toFun := fun F => F x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Hecke.integratedAction_dual μ HarmonicAnalysis.GroupAction.leftTests hl T f L

end Langlands.Renard.Smooth
