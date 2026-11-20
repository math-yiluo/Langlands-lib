import Langlands.Algebra.EnvelopingPositiveIdealBasis

/-! # The Lie algebra of positive adjoint weights -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.Algebra.UniversalEnveloping

variable {k : Type u} [Field k] [CharZero k] {L : Type v} [LieRing L] [LieAlgebra k L]
  {I : Type w} (b : Module.Basis I k L) (d : I → ℤ)

/-- An eigenvector of an integral adjoint grading lies in the span of the
basis vectors of its eigenvalue. -/
theorem mem_weightSpan_of_ad (H : L) (hH : ∀ a, ⁅H, b a⁆ = (d a : k) • b a)
    (s : Set ℤ) (m : ℤ) (hm : m ∈ s) {x : L} (hx : ⁅H, x⁆ = (m : k) • x) :
    x ∈ Submodule.span k (b '' {a | d a ∈ s}) := by
  classical
  let ad : L →ₗ[k] L :=
    { toFun := fun y => ⁅H, y⁆
      map_add' := fun y z => lie_add H y z
      map_smul' := fun t y => lie_smul t H y }
  have hc (a : I) : b.coord a ∘ₗ ad = (d a : k) • b.coord a := by
    refine b.ext fun q => ?_
    change b.coord a ⁅H, b q⁆ = (d a : k) • b.coord a (b q)
    rw [hH, map_smul]
    by_cases h : a = q
    · rw [h]
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, h]
  have hs (a : I) (ha : a ∈ (b.repr x).support) : d a ∈ s := by
    have h : b.repr (⁅H, x⁆) a = (d a : k) * b.repr x a := LinearMap.congr_fun (hc a) x
    rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have he : m = d a := Int.cast_injective (mul_right_cancel₀ (Finsupp.mem_support_iff.mp ha) h)
    exact he ▸ hm
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun a ha =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hs a ha, rfl⟩)

private theorem lie_mem_positiveWeightSpan (H : L) (hH : ∀ a, ⁅H, b a⁆ = (d a : k) • b a)
    {x y : L} (hx : x ∈ Submodule.span k (b '' {a | 0 < d a}))
    (hy : y ∈ Submodule.span k (b '' {a | 0 < d a})) :
    ⁅x, y⁆ ∈ Submodule.span k (b '' {a | 0 < d a}) := by
  let P := Submodule.span k (b '' {a | 0 < d a})
  change x ∈ P at hx
  change y ∈ P at hy
  change ⁅x, y⁆ ∈ P
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      have h : d a + d q ∈ {z : ℤ | 0 < z} := add_pos (show 0 < d a from ha)
        (show 0 < d q from hq)
      apply mem_weightSpan_of_ad b d H hH _ _ h
      rw [leibniz_lie, hH, hH, smul_lie (d a : k), lie_smul (d q : k), ← add_smul, Int.cast_add]
    | zero => simpa only [lie_zero] using P.zero_mem
    | add y z _ _ hy hz => rw [lie_add]; exact P.add_mem hy hz
    | smul t y _ hy => rw [lie_smul]; exact P.smul_mem t hy
  | zero => simpa only [zero_lie] using P.zero_mem
  | add x z _ _ hx hz => rw [add_lie]; exact P.add_mem hx hz
  | smul t x _ hx => rw [smul_lie]; exact P.smul_mem t hx

/-- The span of the positive weight directions is a Lie subalgebra. -/
def positiveWeightLieSubalgebra (H : L) (hH : ∀ a, ⁅H, b a⁆ = (d a : k) • b a) :
    LieSubalgebra k L where
  __ := Submodule.span k (b '' {a | 0 < d a})
  lie_mem' := lie_mem_positiveWeightSpan b d H hH

variable (H : L) (hH : ∀ a, ⁅H, b a⁆ = (d a : k) • b a)

/-- The restricted basis of the positive Lie subalgebra. -/
def positiveWeightLieBasis : Module.Basis {a : I // 0 < d a} k
    (positiveWeightLieSubalgebra b d H hH) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by
      change Submodule.span k (Set.range (fun a : {a : I // 0 < d a} => b a.val)) =
        Submodule.span k (b '' {a | 0 < d a})
      congr 1
      ext x
      exact ⟨fun ⟨a, h⟩ => ⟨a.val, a.property, h⟩,
        fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩))

@[simp]
theorem positiveWeightLieSubalgebra_incl_basis (a : {a : I // 0 < d a}) :
    (positiveWeightLieSubalgebra b d H hH).incl (positiveWeightLieBasis b d H hH a) = b a.val := by
  rw [positiveWeightLieBasis, Module.Basis.map_apply, Module.Basis.span_apply]
  rfl

end Langlands.Algebra.UniversalEnveloping
