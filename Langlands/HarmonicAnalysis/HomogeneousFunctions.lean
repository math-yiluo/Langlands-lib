import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.Group.LeftQuotient

/-! # Renard II.3.9: twisted compact-mod-subgroup functions -/

noncomputable section

open scoped Pointwise NNReal

namespace Langlands.HarmonicAnalysis.HomogeneousFunctions

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The source's literal compact-support-modulo-H condition. -/
def CompactModulo (H : Subgroup G) (f : LocallyConstant G ℂ) : Prop :=
  ∃ K : Set G, IsCompact K ∧ Function.support f ⊆ (H : Set G) * K

/-- Actual locally constant functions, with scalar covariance and support
bounded by H times an actual compact subset of the original group. -/
def space (H : Subgroup G) (χ : H →* ℝ≥0) : Submodule ℂ (LocallyConstant G ℂ) where
  carrier := {f | (∀ (h : H) (x : G),
    f (h.val * x) = ((χ h : ℝ) : ℂ) * f x) ∧ CompactModulo H f}
  zero_mem' := by
    refine ⟨by simp, ∅, isCompact_empty, ?_⟩
    simp [Function.support]
  add_mem' := by
    rintro f g ⟨hf, K, hK, hsK⟩ ⟨hg, L, hL, hsL⟩
    refine ⟨?_, K ∪ L, hK.union hL, ?_⟩
    · intro h x
      change f (h.val * x) + g (h.val * x) = _
      rw [hf, hg]
      exact (mul_add _ _ _).symm
    · intro x hx
      have hx' : f x ≠ 0 ∨ g x ≠ 0 := by
        by_contra hn
        simp only [not_or, not_not] at hn
        exact hx (by change f x + g x = 0; rw [hn.1, hn.2, add_zero])
      rcases hx' with hx' | hx'
      · obtain ⟨h, hh, k, hk, he⟩ := hsK hx'
        exact ⟨h, hh, k, Or.inl hk, he⟩
      · obtain ⟨h, hh, k, hk, he⟩ := hsL hx'
        exact ⟨h, hh, k, Or.inr hk, he⟩
  smul_mem' := by
    rintro c f ⟨hf, K, hK, hs⟩
    refine ⟨?_, K, hK, ?_⟩
    · intro h x
      change c * f (h.val * x) = ((χ h : ℝ) : ℂ) * (c * f x)
      rw [hf]
      exact mul_left_comm _ _ _
    · intro x hx
      apply hs
      intro hz
      exact hx (by change c * f x = 0; rw [hz, mul_zero])

omit [IsTopologicalGroup G] in
@[simp]
theorem mem_space (H : Subgroup G) (χ : H →* ℝ≥0) (f : LocallyConstant G ℂ) :
    f ∈ space H χ ↔ (∀ (h : H) (x : G),
      f (h.val * x) = ((χ h : ℝ) : ℂ) * f x) ∧ CompactModulo H f := Iff.rfl

/-- Right translation on the original functions, restricted to this subspace. -/
def rightTranslate (H : Subgroup G) (χ : H →* ℝ≥0) (g : G) :
    Module.End ℂ (space H χ) where
  toFun f :=
    ⟨⟨fun x => f.val (x * g),
        f.val.isLocallyConstant.comp_continuous (continuous_id.mul continuous_const)⟩, by
      refine ⟨?_, ?_⟩
      · intro h x
        change f.val (h.val * x * g) = ((χ h : ℝ) : ℂ) * f.val (x * g)
        rw [mul_assoc]
        exact f.property.1 h (x * g)
      · obtain ⟨K, hK, hs⟩ := f.property.2
        refine ⟨(fun x : G => x * g⁻¹) '' K,
          hK.image (continuous_id.mul continuous_const), ?_⟩
        intro x hx
        obtain ⟨h, hh, k, hk, he⟩ := hs hx
        refine ⟨h, hh, k * g⁻¹, ⟨k, hk, rfl⟩, ?_⟩
        calc
          h * (k * g⁻¹) = (h * k) * g⁻¹ := (mul_assoc _ _ _).symm
          _ = (x * g) * g⁻¹ := congrArg (· * g⁻¹) he
          _ = x := mul_inv_cancel_right x g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rightTranslate_apply (H : Subgroup G) (χ : H →* ℝ≥0) (g : G)
    (f : space H χ) (x : G) :
    (rightTranslate H χ g f).val x = f.val (x * g) := rfl

/-- The actual right-translation representation. -/
def rightAction (H : Subgroup G) (χ : H →* ℝ≥0) : Representation ℂ G (space H χ) where
  toFun := rightTranslate H χ
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

variable [LocallyCompactSpace G]

/-- Renard's character δ_(H\G) = δ_G|_H / δ_H, using the actual closed
subgroup with its induced topology. -/
def relativeModular (H : Subgroup G) (hH : IsClosed (H : Set G)) : H →* ℝ≥0 := by
  letI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact
    { toFun := fun h => Distribution.renardModular h.val /
        Distribution.renardModular (G := H) h
      map_one' := by simp
      map_mul' := fun h k => by
        simp only [Subgroup.coe_mul, map_mul, div_mul_div_comm] }

/-- The source's actual twisted function space, with no independent carrier. -/
abbrev renardSpace (H : Subgroup G) (hH : IsClosed (H : Set G)) :=
  space H (relativeModular H hH)

end Langlands.HarmonicAnalysis.HomogeneousFunctions
