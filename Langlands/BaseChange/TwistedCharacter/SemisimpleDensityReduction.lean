import Langlands.BaseChange.TwistedCharacter.SemisimpleLocalReduction
import Langlands.BaseChange.TwistedCharacterRegularValues
import Langlands.BaseChange.RegularOrbitParameters
import Langlands.HarmonicAnalysis.Distribution.LocalValuesDensity

/-! # Reduction to density near semisimple points of the cyclic extensions -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands Set Function _root_.Topology
open scoped SemidirectProduct

/-- The local density assertion for ordinary characters near adjoint semisimple points of
actual cyclic `GL_n` extensions. -/
def CyclicGLSemisimpleLocalDensityStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    haveI := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
    let H := CyclicGLSemidirect σ hE.pow_eq_one n
    ∀ {W : Type w} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ H W) (hπ : IsAdmissible π), π.IsIrreducible →
      ∀ s : H, IsCyclicGLSemisimple s →
        ∃ U : Set H, IsOpen U ∧ s ∈ U ∧ ∃ Θ : H → ℂ, IsCharacterDensityOn π hπ Θ U

/-- The published twisted integrability statement follows from the local density assertion.
Regular local constancy comes from the local values on the generator component. -/
def TwistedCharacterFromSemisimpleDensityStatement.{u, v, w} : Prop :=
  CyclicGLSemisimpleLocalDensityStatement.{u, v, w} → TwistedCharacterLocalIntegrabilityStatement.{u, v, w}

theorem twistedCharacterFromSemisimpleDensity.{u, v, w} :
    TwistedCharacterFromSemisimpleDensityStatement.{u, v, w} := by
  intro hDensity F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : NeZero l := ⟨hE.pos.ne'⟩
  have : Module.Finite F E := hE.1
  have : IsReduced E := hE.2.2.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  have := LocalFieldTopology.t2Space F
  have := LocalFieldTopology.secondCountableTopology F
  have := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  have := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  have := (SemidirectProduct.homeomorphProd (cyclicGLAction σ hE.pow_eq_one n)).secondCountableTopology
  intro W _ _ τ hτ hirr A
  let G := GeneralLinear n E
  let H := CyclicGLSemidirect σ hE.pow_eq_one n
  let θ := entrywiseAut σ n
  let hθ := entrywiseAut_pow_eq_one σ hE.pow_eq_one n
  obtain ⟨c, _, B, hB, hA⟩ := exists_normalizedCyclicIntertwiner hE.pos θ hθ τ hτ hirr A
  have hcov (g : G) : B.toLinearMap * τ g = τ (θ g) * B.toLinearMap := B.isIntertwining' g
  let π : Representation ℂ H W := cyclicExtension θ hθ τ B.toLinearMap hB hcov
  let i : G →* H := SemidirectProduct.inl
  let t : H := SemidirectProduct.inr (cyclicGenerator l)
  have hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
  have hres : π.comp i = τ := MonoidHom.ext (cyclicExtension_inl θ hθ τ B.toLinearMap hB hcov)
  have hτ' : IsAdmissible (π.comp i) := hres.symm ▸ hτ
  have hπ := isAdmissible_of_comp_openEmbedding i hi π hτ'
  have hπirr := cyclicExtension_irreducible θ hθ τ B.toLinearMap hB hcov hirr
  have hclosure (x : H) : ∃ y ∈ closure (range fun a : H => a * x * a⁻¹), IsCyclicGLSemisimple y := by
    let := LocalGalois.localNormedField F
    have := LocalGalois.localNormedField_complete F
    exact exists_isCyclicGLSemisimple_mem_conjugacyClosure hE.pos x
  obtain ⟨Ξ, hΞ, _⟩ := exists_characterFunction_of_conjugacyClosure (G := H) (ρ := π) (hρ := hπ)
    {s : H | IsCyclicGLSemisimple s} (∅ : Set H) (by simp) hclosure (by
      intro s hs
      obtain ⟨U, hU, hsU, ξ, hξ⟩ := hDensity F E σ l n hE π hπ hπirr s hs
      exact ⟨U, hU, hsU, ξ, hξ, by simp⟩)
  have hgen : π t = B.toLinearMap := by
    change τ 1 * cyclicPowerHom B.toLinearMap hB (cyclicGenerator l) = B.toLinearMap
    rw [map_one, cyclicPowerHom_generator, one_mul]
  let Θ : G → ℂ := fun g => c * Ξ (i g * t)
  have hΘ : IsTwistedCharacterFunction τ hτ A.toLinearMap Θ := by
    have hrestrict := hΞ.twisted_of_openEmbedding i hi π hπ hτ' t
    have htransport (ρ₀ ρ₁ : Representation ℂ G W)
        (h₀ : IsAdmissible ρ₀) (h₁ : IsAdmissible ρ₁) (heq : ρ₀ = ρ₁)
        (B₀ : Module.End ℂ W) (f : G → ℂ) (hf : IsTwistedCharacterFunction ρ₀ h₀ B₀ f) :
        IsTwistedCharacterFunction ρ₁ h₁ B₀ f := by
      subst ρ₁
      exact hf
    rw [hA, ← hgen]
    exact (htransport _ _ hτ' hτ hres _ _ hrestrict).smul c
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let J := {μ : Measure G // μ.IsHaarMeasure}
  let D (μ : J) : Distribution G :=
    have := μ.property
    twistedDistribution μ.val τ hτ A.toLinearMap
  have hV (x : G) (hx : IsSigmaRegular σ l x) := twistedCharacterRegularValues F E σ l n hE τ hτ hirr A x hx
  obtain ⟨θ', hθ', hreg⟩ := Distribution.regularValuesDensity (fun μ : J => μ.val) D
    {x : G | IsSigmaRegular σ l x} ⟨⟨Measure.haar, inferInstance⟩⟩ (fun μ => by
      have := μ.property
      infer_instance) (fun μ => by
      have := μ.property
      infer_instance) (isOpen_sigmaRegular hE n) ⟨Θ, fun μ => by
      have := μ.property
      exact hΘ μ.val⟩ (fun x hx => by
      obtain ⟨val, hval⟩ := hV x hx
      exact ⟨val, fun μ => by
        have := μ.property
        exact hval μ.val⟩)
  exact ⟨θ', fun μ hμ => hθ' ⟨μ, hμ⟩, hreg⟩

end Langlands.BaseChange
