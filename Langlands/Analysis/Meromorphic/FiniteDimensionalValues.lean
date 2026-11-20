import Langlands.Analysis.Meromorphic.LinearCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Meromorphic functions with values in a finite-dimensional space of functions

Images of holomorphic and meromorphic functions (in the sense of Bernstein–Lapid §3.1, as in
`Langlands.Analysis.Meromorphic.AnalyticSystems`) under continuous linear maps, and the
passage from a meromorphic family of functions `X → ℂ` (topology of pointwise convergence)
whose values on a set `S` lie in the span of finitely many functions `ψ i` to a finite
expansion `∑ i, coeff i λ * ψ' i x` with meromorphic scalar coefficients, where `ψ'` is a
linearly independent subfamily of `ψ`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

section Image

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

/-- The image of a holomorphic function under a continuous linear map is holomorphic. -/
theorem IsHolomorphicOn.continuousLinearMap_comp {f : M → V} {U : Set M}
    (hf : IsHolomorphicOn I f U) (L : V →L[ℂ] W) :
    IsHolomorphicOn I (fun s => L (f s)) U :=
  fun μ => hf (μ.comp L)

/-- The image of a meromorphic function under a continuous linear map is meromorphic, with the
same domain of holomorphy and the same local scalar denominators. -/
theorem IsMeromorphicOn.continuousLinearMap_comp {f : M → V} {U : Set M}
    (hf : IsMeromorphicOn I f U) (L : V →L[ℂ] W) :
    IsMeromorphicOn I (fun s => L (f s)) U := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  refine ⟨hUo, hUd, hhol.continuousLinearMap_comp L, fun s₀ => ?_⟩
  obtain ⟨Wn, hWo, hWc, hs₀, g, h, hg, hne, hh, heq⟩ := hloc s₀
  refine ⟨Wn, hWo, hWc, hs₀, g, fun s => L (h s), hg, hne,
    hh.continuousLinearMap_comp L, fun s hs => ?_⟩
  rw [← L.map_smul, heq s hs]

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The image of a function that is meromorphic in linear coordinates under a continuous linear
map is meromorphic in linear coordinates, with the same domain of holomorphy. -/
theorem IsMeromorphicInCoordinatesOn.continuousLinearMap_comp {f : X → V} {U : Set X}
    (hf : IsMeromorphicInCoordinatesOn f U) (L : V →L[ℂ] W) :
    IsMeromorphicInCoordinatesOn (fun s => L (f s)) U :=
  ⟨hf.1, fun n e => (hf.2 n e).continuousLinearMap_comp L⟩

end Image

section Expansion

/-- A linearly independent finite family `b` of complex functions on a type `X` admits a
continuous linear left inverse of `c ↦ ∑ i, c i • b i` on the space of all functions `X → ℂ`
with the topology of pointwise convergence: it factors through evaluation at finitely many
points of `X`. -/
theorem exists_continuousLinearMap_leftInverse {X : Type*} {ι : Type*} [Fintype ι]
    (b : ι → X → ℂ) (hb : LinearIndependent ℂ b) :
    ∃ Φ : (X → ℂ) →L[ℂ] (ι → ℂ), ∀ c : ι → ℂ, Φ (∑ i, c i • b i) = c := by
  classical
  set T : (ι → ℂ) →ₗ[ℂ] (X → ℂ) := Fintype.linearCombination ℂ b with hT
  have hTinj : Function.Injective T := hb.fintypeLinearCombination_injective
  -- the evaluation functionals `c ↦ (∑ i, c i • b i) x`
  let L : X → Module.Dual ℂ (ι → ℂ) := fun x => (LinearMap.proj x).comp T
  have hL : ∀ x c, L x c = T c x := fun _ _ => rfl
  -- they span the dual space, since their common kernel is trivial
  have hspan : Submodule.span ℂ (Set.range L) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range L)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Submodule.mem_dualCoannihilator] at hc
      have hzero : T c = 0 := by
        funext x
        rw [← hL]
        exact hc _ (Submodule.subset_span ⟨x, rfl⟩)
      have : c = 0 := hTinj (by rw [hzero, map_zero])
      rw [this]
      exact Submodule.zero_mem _
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range L)),
      hco, Submodule.dualAnnihilator_bot]
  -- finitely many of them already span the dual space
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' ℂ L
  have : Finite κ := hli.finite_of_isNoetherian
  let rS : (X → ℂ) →ₗ[ℂ] (κ → ℂ) := LinearMap.funLeft ℂ ℂ a
  have hker : LinearMap.ker (rS ∘ₗ T) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hvan : ∀ k : κ, L (a k) c = 0 := fun k => by
      rw [hL]
      exact congrFun hc k
    have hall : ∀ f : Module.Dual ℂ (ι → ℂ), f c = 0 := by
      intro f
      have hf : f ∈ Submodule.span ℂ (Set.range (L ∘ a)) := by
        rw [hsp, hspan]
        exact Submodule.mem_top
      have hle : Submodule.span ℂ (Set.range (L ∘ a)) ≤
          LinearMap.ker (Module.Dual.eval ℂ (ι → ℂ) c) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact hvan k
      exact hle hf
    rw [Submodule.mem_bot]
    exact (Module.forall_dual_apply_eq_zero_iff ℂ c).1 hall
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (rS ∘ₗ T) hker
  have hcont : Continuous (ψ ∘ₗ rS) := by
    have hr : Continuous rS := continuous_pi fun k => continuous_apply (a k)
    exact ψ.continuous_of_finiteDimensional.comp hr
  refine ⟨⟨ψ ∘ₗ rS, hcont⟩, fun c => ?_⟩
  have h1 : (ψ ∘ₗ (rS ∘ₗ T)) c = c := by rw [hψ]; rfl
  exact h1

/-- Finite expansions with meromorphic coefficients. Let `E : Λ → (X → ℂ)` be meromorphic in
linear coordinates with domain of holomorphy `D`, for the topology of pointwise convergence on
`X → ℂ`, and suppose that `E λ` lies in the span of finitely many functions `ψ i` for `λ ∈ S`.
Then there are a subfamily `ψ'` of `ψ` (so every property `Pr` of all `ψ i` holds for all
`ψ' i`) and scalar coefficients `coeff i`, meromorphic in linear coordinates with the same
domain `D`, such that `E λ x = ∑ i, coeff i λ * ψ' i x` for `λ ∈ S`. -/
theorem exists_meromorphic_expansion_of_mem_span {X Λ : Type*} [AddCommGroup Λ] [Module ℂ Λ]
    (Pr : (X → ℂ) → Prop) {k : ℕ} (ψ : Fin k → X → ℂ) (hψ : ∀ i, Pr (ψ i))
    {E : Λ → X → ℂ} {D : Set Λ} (hE : IsMeromorphicInCoordinatesOn E D)
    {S : Set Λ} (hS : ∀ lam ∈ S, E lam ∈ Submodule.span ℂ (Set.range ψ)) :
    ∃ (m : ℕ) (ψ' : Fin m → X → ℂ) (coeff : Fin m → Λ → ℂ),
      (∀ i, Pr (ψ' i)) ∧ (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
      ∀ lam ∈ S, ∀ x, E lam x = ∑ i, coeff i lam * ψ' i x := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ ψ
  have : Finite κ := Finite.of_injective a ha
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  let ψ' : Fin (Nat.card κ) → X → ℂ := fun i => ψ (a (eκ.symm i))
  have hli' : LinearIndependent ℂ ψ' := hli.comp _ eκ.symm.injective
  have hrange : Set.range ψ' = Set.range (ψ ∘ a) :=
    eκ.symm.surjective.range_comp (ψ ∘ a)
  obtain ⟨Φ, hΦ⟩ := exists_continuousLinearMap_leftInverse ψ' hli'
  refine ⟨Nat.card κ, ψ', fun i lam => Φ (E lam) i, fun i => hψ _, fun i => ?_, ?_⟩
  · exact hE.continuousLinearMap_comp ((ContinuousLinearMap.proj i).comp Φ)
  · intro lam hlam x
    have hmem : E lam ∈ Submodule.span ℂ (Set.range ψ') := by
      rw [hrange, hsp]
      exact hS lam hlam
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    show E lam x = ∑ i, Φ (E lam) i * ψ' i x
    rw [← hc, hΦ c, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]

end Expansion

end Langlands.Analysis.Meromorphic
