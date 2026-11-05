import Langlands.Representation.CompactCoefficient.UniformSupportStatement
import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finiteness of compact classes from one common coefficient support -/

noncomputable section

namespace Langlands.CompactCoefficientClass

open MeasureTheory ComplexConjugate Hecke
open HarmonicAnalysis (SchwartzBruhat)

universe uG uV

section SupportedFunctions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The common coefficient space at a fixed level and a fixed support bound. -/
def supportedBiInvariant (K : Subgroup G) (C : Set G) :
    Submodule ℂ (SchwartzBruhat G) where
  carrier := {f | f ∈ TestFunction.biInvariant K K ∧ Function.support f ⊆ C}
  zero_mem' := ⟨(TestFunction.biInvariant K K).zero_mem, by simp⟩
  add_mem' {f g} hf hg := ⟨(TestFunction.biInvariant K K).add_mem hf.1 hg.1,
    fun x hx => by
      by_contra h
      have hf0 : f x = 0 := not_not.mp (fun hx => h (hf.2 hx))
      have hg0 : g x = 0 := not_not.mp (fun hx => h (hg.2 hx))
      exact hx (by change f x + g x = 0; rw [hf0, hg0, zero_add])⟩
  smul_mem' c f hf := ⟨(TestFunction.biInvariant K K).smul_mem c hf.1,
    fun x hx => by
      apply hf.2
      intro h
      exact hx (by change c • f x = 0; rw [h, smul_zero])⟩

/-- Finitely many right cosets cover a compact set, so evaluations at their
representatives inject this entire support-bounded space into a finite product. -/
theorem finiteDimensional_supportedBiInvariant (K : OpenSubgroup G)
    {C : Set G} (hC : IsCompact C) :
    FiniteDimensional ℂ (supportedBiInvariant K.toSubgroup C) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun r : G => {x | r⁻¹ * x ∈ K})
    (fun r => K.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp⟩)
  let ev : supportedBiInvariant K.toSubgroup C →ₗ[ℂ] (t → ℂ) :=
    { toFun := fun f r => f.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective (V₂ := t → ℂ) ev ?_
  intro f g hfg
  apply Subtype.ext
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hf := f.2.1.2 ⟨r⁻¹ * x, hxr⟩ r
    have hg := g.2.1.2 ⟨r⁻¹ * x, hxr⟩ r
    have he := congrFun hfg ⟨r, hr⟩
    change f.1 r = g.1 r at he
    simpa only [mul_inv_cancel_left] using hf.trans (he.trans hg.symm)
  · have hf0 : f.1 x = 0 := not_not.mp (fun h => hx (f.2.2 h))
    have hg0 : g.1 x = 0 := not_not.mp (fun h => hx (g.2.2 h))
    exact hf0.trans hg0.symm

end SupportedFunctions

section SupportedSeparation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

/-- The published separation construction retains the prescribed common support:
its test function is an inverse coefficient against an N-invariant functional. -/
theorem exists_separating_corner_element_supported (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
    (hD : fixedVectors D.obj.representation N.toSubgroup ≠ ⊥)
    (C : Set G)
    (hC : ∀ (v : D.obj), v ∈ fixedVectors D.obj.representation N.toSubgroup →
      ∀ Λ : Module.Dual ℂ D.obj,
        (∀ k ∈ N, ∀ y, Λ (D.obj.representation k y) = Λ y) →
        Function.support (fun g : G => Λ (D.obj.representation g⁻¹ v)) ⊆ C) :
    ∃ f : HeckeAlgebra.Corner μ N hN,
      Function.support (f : G → ℂ) ⊆ C ∧
      cornerAction μ D.obj.representation D.obj.isSmooth N hN f ≠ 0 ∧
      ∀ E : IrreducibleCompactCoefficientRep.{uG, uV} G, ofRep D ≠ ofRep E →
        cornerAction μ E.obj.representation E.obj.isSmooth N hN f = 0 := by
  classical
  let ρ := D.obj.representation
  have hρ : IsSmooth ρ := D.obj.isSmooth
  have hc : HasCompactSmoothDualCoefficients ρ := D.property.2
  obtain ⟨v₀, hv₀N, hv₀⟩ := (Submodule.ne_bot_iff _).mp hD
  have hex : ¬ ∀ ℓ₀ : Module.Dual ℂ D.obj, ℓ₀ v₀ = 0 := fun h =>
    hv₀ ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  obtain ⟨ℓ₀, hℓ₀⟩ := not_forall.mp hex
  let ℓ := dualAverage μ ρ hρ N hN ℓ₀
  have hℓ : IsSmoothVector ρ.dual ℓ := dualAverage_isSmoothVector μ ρ hρ N hN ℓ₀
  have hℓv : ℓ v₀ ≠ 0 := by
    rw [dualAverage_apply_of_fixed μ ρ hρ N hN ℓ₀ hv₀N]
    exact hℓ₀
  let Λ := invariantForm μ ρ hρ hc ℓ hℓ v₀
  have hΛN : ∀ k ∈ N, ∀ y, Λ (ρ k y) = Λ y := by
    intro k hk y
    change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ k y) = invariantForm μ ρ hρ hc ℓ hℓ v₀ y
    conv_lhs => rw [← apply_eq_of_mem_fixedVectors hv₀N hk]
    exact invariantForm_rho μ ρ hρ hc ℓ hℓ k y v₀
  have hΛ : IsSmoothVector ρ.dual Λ := isSmoothVector_dual_of_invariant ρ N hΛN
  let φ := inverseCoefficient ρ hρ hc Λ hΛ v₀
  have hφ : φ ∈ TestFunction.biInvariant N.toSubgroup N.toSubgroup :=
    inverseCoefficient_mem_biInvariant hΛN hv₀N
  let f : HeckeAlgebra.Corner μ N hN := ⟨(HeckeAlgebra.toTestFunction μ).symm φ, hφ⟩
  have hφconj : ∀ g, Λ (ρ g v₀) = conj (φ g) := by
    intro g
    change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ g v₀) =
      conj (invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ g⁻¹ v₀))
    rw [← invariantForm_rho μ ρ hρ hc ℓ hℓ g⁻¹ (ρ g v₀) v₀, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply, invariantForm_conj]
  refine ⟨f, hC v₀ hv₀N Λ hΛN, fun hf => ?_, fun E hDE => ?_⟩
  · have h1 : (cornerAction μ ρ hρ N hN f ⟨v₀, hv₀N⟩ : D.obj) = 0 := by
      rw [hf]
      rfl
    rw [cornerAction_apply, heckeAction_apply] at h1
    have h2 := congrArg Λ h1
    rw [integratedAction_dual, map_zero] at h2
    refine integral_mul_conj_ne_zero μ φ.continuous φ.hasCompactSupport (x := 1) ?_ ?_
    · change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ 1⁻¹ v₀) ≠ 0
      rw [inv_one, map_one, Module.End.one_apply]
      exact invariantForm_self_ne_zero μ ρ hρ hc ℓ hℓ hℓv
    · rw [← h2]
      congr 1
      funext g
      rw [hφconj]
      rfl
  · let σ := E.obj.representation
    have hσ : IsSmooth σ := E.obj.isSmooth
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [cornerAction_apply, heckeAction_apply]
    change integratedAction μ σ hσ φ w = 0
    let S : ρ.IntertwiningMap σ := LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
      (LinearMap.applyₗ (w : E.obj) ∘ₗ integratedAction μ σ hσ ∘ₗ
        inverseCoefficient ρ hρ hc Λ hΛ)
      (fun h v => by
        simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
        rw [inverseCoefficient_apply_rho, integratedAction_leftTranslate])
    have hS : S = 0 := intertwiningMap_eq_zero_of_ne hDE S
    exact congrArg (fun T : ρ.IntertwiningMap σ => T v₀) hS


/-- Regard a supported bi-invariant test function as an element of the actual
Haar Hecke corner. This only changes the convolution wrapper. -/
def supportedToCorner (C : Set G) :
    supportedBiInvariant N.toSubgroup C →ₗ[ℂ] HeckeAlgebra.Corner μ N hN where
  toFun f := ⟨(HeckeAlgebra.toTestFunction μ).symm f.1, f.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include μ hN in
/-- One common compact support implies finiteness of the actual fixed-level
compact-coefficient isomorphism classes. -/
theorem fixedStratum_finite_of_uniformSupport
    (hU : HasUniformFixedLevelCoefficientSupport.{uG, uV} N.toSubgroup) :
    (fixedStratum.{uG, uV} N.toSubgroup).Finite := by
  classical
  obtain ⟨C, hC, hsupport⟩ := hU
  let S := fixedStratum.{uG, uV} (G := G) N.toSubgroup
  have hout : ∀ c : CompactCoefficientClass.{uG, uV} G, ofRep c.out = c := Quotient.out_eq
  have hfix : ∀ c ∈ S, fixedVectors c.out.obj.representation N.toSubgroup ≠ ⊥ := by
    intro c hc
    rw [← hasFixedVector_ofRep, hout]
    exact hc
  let ι := {c // c ∈ S}
  have hsep : ∀ i : ι, ∃ f : HeckeAlgebra.Corner μ N hN,
      Function.support (f : G → ℂ) ⊆ C ∧
      cornerAction μ i.1.out.obj.representation i.1.out.obj.isSmooth N hN f ≠ 0 ∧
      ∀ E : IrreducibleCompactCoefficientRep.{uG, uV} G, ofRep i.1.out ≠ ofRep E →
        cornerAction μ E.obj.representation E.obj.isSmooth N hN f = 0 := fun i =>
    exists_separating_corner_element_supported μ N hN i.1.out (hfix i.1 i.2) C
      (hsupport i.1.out)
  choose f hfs hfself hfother using hsep
  let F : ι → supportedBiInvariant N.toSubgroup C := fun i =>
    ⟨(HeckeAlgebra.Corner.toBiInvariant μ N hN (f i)).1, (f i).property, hfs i⟩
  have hF : ∀ i, supportedToCorner μ N hN C (F i) = f i := fun _ => rfl
  have hlin : LinearIndependent ℂ F := by
    rw [linearIndependent_iff'ₛ]
    intro t a b ha i hi
    let A := (cornerAction μ i.1.out.obj.representation i.1.out.obj.isSmooth N hN).toLinearMap
      ∘ₗ supportedToCorner μ N hN C
    have h := congrArg A ha
    simp only [A, map_sum, map_smul, LinearMap.comp_apply, hF] at h
    have hz : ∀ (c : ι → ℂ) j, j ∈ t → j ≠ i →
        c j • cornerAction μ i.1.out.obj.representation i.1.out.obj.isSmooth N hN (f j) = 0 := by
      intro c j _ hji
      have hne : ofRep j.1.out ≠ ofRep i.1.out := by
        rw [hout, hout]
        exact fun h => hji (Subtype.ext h)
      rw [hfother j i.1.out hne, smul_zero]
    erw [Finset.sum_eq_single i (fun j hj hji => hz a j hj hji) (fun h => (h hi).elim),
      Finset.sum_eq_single i (fun j hj hji => hz b j hj hji) (fun h => (h hi).elim)] at h
    exact smul_left_injective ℂ (hfself i) h
  have := finiteDimensional_supportedBiInvariant N hC
  have : Finite ι := hlin.finite
  exact Set.finite_coe_iff.mp this

end SupportedSeparation

/-- The exact generic reduction statement, with independent group and carrier
universes and only a left Haar measure. -/
theorem uniformSupportFixedLevelFiniteness :
    UniformSupportFixedLevelFinitenessStatement.{uG, uV} := by
  intro G _ _ _ _ _ μ _ N hN hU
  exact fixedStratum_finite_of_uniformSupport μ N hN hU

end Langlands.CompactCoefficientClass
