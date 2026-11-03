import Langlands.GroupScheme.Rational.RootAnnihilatorBaseChange

/-! # Integral criteria for real annihilator range comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

/-- Real common annihilators of finite selections of actual characters are
spanned by the real images of their integral common annihilators. -/
def IntegralRootAnnihilatorSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (J : Set (characterLattice T)) [Finite J],
    rootAnnihilator T J = Submodule.span ℝ
      (Set.range fun ν : rootAnnihilatorInt T J => ((1 : ℝ) ⊗ₜ[ℤ] ν.1 : V T))

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A finite-character real annihilator is spanned by the corresponding actual
integral annihilating cocharacters. -/
theorem rootAnnihilator_eq_span_integral (J : Set (characterLattice T)) [Finite J] :
    rootAnnihilator T J = Submodule.span ℝ
      (Set.range fun ν : rootAnnihilatorInt T J => ((1 : ℝ) ⊗ₜ[ℤ] ν.1 : V T)) := by
  rw [← rootAnnihilatorInt_baseChange J, Submodule.baseChange_eq_span]
  congr 1
  ext v
  simp only [Set.mem_range]
  exact ⟨fun ⟨ν, hν, h⟩ => ⟨⟨ν, hν⟩, h⟩,
    fun ⟨ν, h⟩ => ⟨ν.1, ν.2, h⟩⟩

/-- Containment of a finite-character real annihilator can be checked on the
images of actual integral annihilating cocharacters. -/
theorem rootAnnihilator_le_iff_integral (J : Set (characterLattice T)) [Finite J]
    (W : Submodule ℝ (V T)) :
    rootAnnihilator T J ≤ W ↔
      ∀ ν : cocharacterLattice T, (∀ α ∈ J, latticePairing T α ν = 0) →
        (1 : ℝ) ⊗ₜ[ℤ] ν ∈ W := by
  rw [rootAnnihilator_eq_span_integral, Submodule.span_le]
  constructor
  · intro h ν hν
    exact h ⟨⟨ν, (mem_rootAnnihilatorInt J ν).mpr hν⟩, rfl⟩
  · rintro h _ ⟨ν, rfl⟩
    exact h ν.1 ((mem_rootAnnihilatorInt J ν.1).mp ν.2)

/-- Vanishing of integral pairings is equivalent to containment of the entire
real cocharacter image in a character annihilator. -/
theorem range_cocharacterMapReal_le_rootAnnihilator_iff (f : A ⟶ T)
    (J : Set (characterLattice T)) :
    (cocharacterMapReal f).range ≤ rootAnnihilator T J ↔
      ∀ μ : cocharacterLattice A, ∀ α ∈ J,
        latticePairing T α (cocharacterMapInt f μ) = 0 := by
  constructor
  · intro h μ α hα
    have hv := (mem_rootAnnihilator J _).mp (h
      (LinearMap.mem_range_self (cocharacterMapReal f) ((1 : ℝ) ⊗ₜ[ℤ] μ))) α hα
    simp only [cocharacterMapReal_tmul, eval_tmul, one_mul] at hv
    exact_mod_cast hv
  · intro h v hv
    obtain ⟨x, rfl⟩ := hv
    rw [mem_rootAnnihilator]
    intro α hα
    induction x using TensorProduct.inductionOn with
    | tmul r μ =>
      change r * (latticePairing T α (cocharacterMapInt f μ) : ℝ) = 0
      rw [h μ α hα, Int.cast_zero, mul_zero]
    | add x y hx hy => simp [map_add, hx, hy]

/-- Integral factorization of annihilating cocharacters implies containment of
the real annihilator in the real cocharacter image. -/
theorem rootAnnihilator_le_range_cocharacterMapReal (f : A ⟶ T)
    (J : Set (characterLattice T)) [Finite J]
    (h : rootAnnihilatorInt T J ≤ (cocharacterMapInt f).range) :
    rootAnnihilator T J ≤ (cocharacterMapReal f).range := by
  rw [rootAnnihilator_le_iff_integral]
  intro ν hν
  obtain ⟨μ, hμ⟩ := h ((mem_rootAnnihilatorInt J ν).mpr hν)
  refine ⟨(1 : ℝ) ⊗ₜ[ℤ] μ, ?_⟩
  change (1 : ℝ) ⊗ₜ[ℤ] cocharacterMapInt f μ = (1 : ℝ) ⊗ₜ[ℤ] ν
  rw [hμ]

/-- Equality of the actual integral cocharacter image with the common
annihilator implies the corresponding exact real range equality. -/
theorem range_cocharacterMapReal_eq_rootAnnihilator (f : A ⟶ T)
    (J : Set (characterLattice T)) [Finite J]
    (h : (cocharacterMapInt f).range = rootAnnihilatorInt T J) :
    (cocharacterMapReal f).range = rootAnnihilator T J := by
  apply le_antisymm
  · rw [range_cocharacterMapReal_le_rootAnnihilator_iff]
    intro μ
    exact (mem_rootAnnihilatorInt J _).mp
      (h ▸ LinearMap.mem_range_self (cocharacterMapInt f) μ)
  · exact rootAnnihilator_le_range_cocharacterMapReal f J h.ge

/-- The integral-span statement holds without splitness or independence. -/
theorem integralRootAnnihilatorSpanStatement :
    IntegralRootAnnihilatorSpanStatement.{u} := by
  intro k _ T J _
  exact rootAnnihilator_eq_span_integral J

end Langlands.GroupScheme.RealTorusSpace
