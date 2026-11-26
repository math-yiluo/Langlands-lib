import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.TwistedCharacter.CyclicExtension
import Langlands.BaseChange.TwistedCharacter.OpenCoset
import Langlands.BaseChange.TwistedCharacter.SemidirectTopology
import Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement
import Langlands.BaseChange.TwistedTriangularDifferential

/-! # The cyclic semidirect reduction for twisted character integrability -/

noncomputable section

namespace Langlands.BaseChange

open Filter _root_.Topology
open scoped SemidirectProduct

section Semidirect

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {l : ℕ} [NeZero l] (σ : E ≃ₐ[F] E) (hσ : σ ^ l = 1) (n : ℕ)

scoped instance cyclicComponentTopology (l : ℕ) : TopologicalSpace (CyclicComponent l) := ⊥

scoped instance cyclicComponentDiscrete (l : ℕ) : DiscreteTopology (CyclicComponent l) := ⟨rfl⟩

include hσ in
omit [NeZero l] in
theorem entrywiseAut_pow_eq_one : (entrywiseAut σ n) ^ l = 1 := by
  change (entrywiseAutHom n σ) ^ l = 1
  rw [← map_pow, hσ, map_one]

/-- The cyclic action on the group of matrices. -/
def cyclicGLAction : CyclicComponent l →* MulAut (GeneralLinear n E) :=
  cyclicPowerHom (entrywiseAut σ n) (entrywiseAut_pow_eq_one σ hσ n)

/-- The group of matrices with the cyclic group of entrywise automorphisms adjoined. -/
abbrev CyclicGLSemidirect :=
  GeneralLinear n E ⋊[cyclicGLAction σ hσ n] CyclicComponent l

/-- The component map for the distinguished generator. -/
def cyclicGeneratorSlice (δ : GeneralLinear n E) : CyclicGLSemidirect σ hσ n :=
  ⟨δ, cyclicGenerator l⟩

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

theorem cyclicGLSemidirect_isTopologicalGroup : IsTopologicalGroup (CyclicGLSemidirect σ hσ n) :=
  SemidirectProduct.isTopologicalGroup_of_continuous _ fun c => by
    change Continuous ⇑((entrywiseAutHom n σ) ^ c.toAdd.val)
    rw [← map_pow]
    exact continuous_entrywiseAut (σ ^ c.toAdd.val) n

end Semidirect

section Regular

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] [Module.Finite F E]
  {l : ℕ} [NeZero l] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1} {n : ℕ}

/-- The adjoint operator on the matrix Lie algebra at a cyclic semidirect element. -/
def cyclicGLAdjoint (x : CyclicGLSemidirect σ hσ n) :
    Module.End F (Matrix (Fin n) (Fin n) E) :=
  (twistedMatrixConj (cyclicPowerHom σ hσ x.right) x.left).toLinearMap

/-- Regularity in Clozel's sense: the multiplicity of the eigenvalue `1` of the
adjoint operator is minimal on the same component. -/
def IsCyclicGLRegular (x : CyclicGLSemidirect σ hσ n) : Prop :=
  ∀ y : CyclicGLSemidirect σ hσ n, y.right = x.right →
    (cyclicGLAdjoint x).charpoly.rootMultiplicity 1 ≤
      (cyclicGLAdjoint y).charpoly.rootMultiplicity 1

end Regular

/-- Clozel's character regularity on the cyclic semidirect models, with the product
topology on their rational points. -/
def CyclicGLCharacterRegularityStatement.{u, v, uW} : Prop :=
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
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (CyclicGLSemidirect σ hE.pow_eq_one n) W)
      (hπ : IsAdmissible π), π.IsIrreducible →
      ∃ Θ : CyclicGLSemidirect σ hE.pow_eq_one n → ℂ, IsCharacterFunction π hπ Θ ∧
        ∀ x, IsCyclicGLRegular x → ∀ᶠ y in nhds x, Θ y = Θ x

/-- The Library's σ-regular points give regular elements of the generator component. -/
def SigmaRegularCyclicGLComparisonStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (E : Type v) [CommRing E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ →
      IsCyclicGLRegular (cyclicGeneratorSlice σ hE.pow_eq_one n δ)

/-- Semidirect character regularity and the regular-locus comparison imply the published
twisted character integrability statement. -/
def TwistedCharacterSemidirectReductionStatement.{u, v, uW} : Prop :=
  CyclicGLCharacterRegularityStatement.{u, v, uW} →
    SigmaRegularCyclicGLComparisonStatement.{u, v} →
      TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}

theorem twistedCharacterSemidirectReduction.{u, v, uW} :
    TwistedCharacterSemidirectReductionStatement.{u, v, uW} := by
  intro hClozel hcompare F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : NeZero l := ⟨hE.pos.ne'⟩
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  have := LocalFieldTopology.secondCountableTopology F
  have := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  have := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  intro W _ _ τ hτ hirr A
  let θ := entrywiseAut σ n
  let hθ := entrywiseAut_pow_eq_one σ hE.pow_eq_one n
  obtain ⟨c, _, B, hB, hA⟩ := exists_normalizedCyclicIntertwiner hE.pos θ hθ τ hτ hirr A
  have hcov (g : GeneralLinear n E) :
      B.toLinearMap * τ g = τ (θ g) * B.toLinearMap :=
    B.isIntertwining' g
  let π := cyclicExtension θ hθ τ B.toLinearMap hB hcov
  let i : GeneralLinear n E →* CyclicGLSemidirect σ hE.pow_eq_one n := SemidirectProduct.inl
  let t : CyclicGLSemidirect σ hE.pow_eq_one n := SemidirectProduct.inr (cyclicGenerator l)
  have hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
  have hres : π.comp i = τ :=
    MonoidHom.ext (cyclicExtension_inl θ hθ τ B.toLinearMap hB hcov)
  have hτ' : IsAdmissible (π.comp i) := hres.symm ▸ hτ
  have hπ := isAdmissible_of_comp_openEmbedding i hi π hτ'
  have hπirr := cyclicExtension_irreducible θ hθ τ B.toLinearMap hB hcov hirr
  obtain ⟨Θ, hΘ, hloc⟩ := hClozel F E σ l n hE π hπ hπirr
  have hgen : π t = B.toLinearMap := by
    change τ 1 * cyclicPowerHom B.toLinearMap hB (cyclicGenerator l) = B.toLinearMap
    rw [map_one, cyclicPowerHom_generator, one_mul]
  have hj (g : GeneralLinear n E) : i g * t = cyclicGeneratorSlice σ hE.pow_eq_one n g :=
    (SemidirectProduct.mk_eq_inl_mul_inr _ _).symm
  have hrestrict := hΘ.twisted_of_openEmbedding i hi π hπ hτ' t
  simp only [hj] at hrestrict
  have htransport (ρ₀ ρ₁ : Representation ℂ (GeneralLinear n E) W)
      (h₀ : IsAdmissible ρ₀) (h₁ : IsAdmissible ρ₁) (heq : ρ₀ = ρ₁)
      (B₀ : Module.End ℂ W) (f : GeneralLinear n E → ℂ)
      (hf : IsTwistedCharacterFunction ρ₀ h₀ B₀ f) :
      IsTwistedCharacterFunction ρ₁ h₁ B₀ f := by
    subst ρ₁
    exact hf
  have hBfun := htransport _ _ hτ' hτ hres _ _ hrestrict
  have hs : Continuous (cyclicGeneratorSlice σ hE.pow_eq_one n) :=
    (SemidirectProduct.isOpenEmbedding_slice (cyclicGLAction σ hE.pow_eq_one n)
      (cyclicGenerator l)).continuous
  refine ⟨fun g => c * Θ (cyclicGeneratorSlice σ hE.pow_eq_one n g), ?_, fun δ hδ => ?_⟩
  · rw [hA, ← hgen]
    exact hBfun.smul c
  · have hreg := hcompare F E σ l n hE δ hδ
    filter_upwards [(hs.tendsto δ).eventually (hloc _ hreg)] with x hx
    exact congrArg (c * ·) hx

end Langlands.BaseChange
