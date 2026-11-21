import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation

/-! Compact differentiation on linear spans and subrepresentations. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Automorphic

open Global ArchimedeanGL _root_.Representation

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type*} [Field F] {n : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (standardInfiniteCompact F n) V)
  (L : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The vectors for which the compact action differentiates to the given Lie
action against every algebraic linear functional. -/
def compactDifferentiableVectors : Submodule ℂ V where
  carrier := {v | ∀ (X : RealLieAlgebra F n) (c : ℝ → standardInfiniteCompact F n),
    c 0 = 1 →
    HasDerivAt
      (fun t : ℝ => (archimedeanGLCoordinates F n (c t).val : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0 →
    ∀ μ : V →ₗ[ℂ] ℂ,
      HasDerivAt (fun t : ℝ => μ (ρ (c t) v)) (μ (L (complexify F n X) v)) 0}
  zero_mem' := by
    intro X c hc0 hc μ
    simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  add_mem' := by
    intro v w hv hw X c hc0 hc μ
    simpa only [map_add] using (hv X c hc0 hc μ).fun_add (hw X c hc0 hc μ)
  smul_mem' := by
    intro a v hv X c hc0 hc μ
    simpa only [map_smul] using (hv X c hc0 hc μ).fun_const_smul a

namespace CompactDualDerivative

/-- Compact differentiation passes to a carrier spanned by the images of
maps intertwining both the compact and the complex Lie actions. -/
theorem of_spanning_ranges
    {J : Type*} {U : J → Type*} [∀ j, AddCommGroup (U j)] [∀ j, Module ℂ (U j)]
    (σ : ∀ j, Representation ℂ (standardInfiniteCompact F n) (U j))
    (D : ∀ j, ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (U j))
    (hD : ∀ j, CompactDualDerivative (σ j) (D j))
    (f : ∀ j, (σ j).IntertwiningMap ρ)
    (hf : ∀ j X x, f j (D j X x) = L X (f j x))
    (hspan : (⨆ j, (f j).toLinearMap.range) = ⊤) :
    CompactDualDerivative ρ L := by
  have hle : (⨆ j, (f j).toLinearMap.range) ≤ compactDifferentiableVectors ρ L := by
    refine iSup_le fun j => ?_
    intro v hv
    obtain ⟨x, rfl⟩ := hv
    intro X c hc0 hc μ
    have hd := hD j X c hc0 hc (μ.comp (f j).toLinearMap) x
    simpa only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
      IntertwiningMap.isIntertwining, hf] using hd
  rw [hspan] at hle
  intro X c hc0 hc μ v
  exact (hle (Submodule.mem_top (x := v))) X c hc0 hc μ

/-- Compact differentiation restricts to an injective intertwiner for
the compact and Lie actions. Every algebraic functional on the
subrepresentation extends across the inclusion. -/
theorem of_injective_intertwiner {U : Type*} [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ (standardInfiniteCompact F n) U}
    {D : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ U}
    (hL : CompactDualDerivative ρ L) (f : σ.IntertwiningMap ρ)
    (hf : Function.Injective f) (hLie : ∀ X x, f (D X x) = L X (f x)) :
    CompactDualDerivative σ D := by
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hinv (x : U) : g (f x) = x := LinearMap.congr_fun hg x
  intro X c hc0 hc μ x
  have hd := hL X c hc0 hc (μ.comp g) (f x)
  simpa only [LinearMap.comp_apply, ← IntertwiningMap.isIntertwining σ ρ f, ← hLie, hinv]
    using hd

end CompactDualDerivative

end Langlands.Automorphic
