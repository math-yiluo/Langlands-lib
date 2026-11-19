import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Products along a finite involution -/

universe u v

namespace Langlands.Algebra

/-- In an equivariant product over a finite involution, the nonfixed pairs
contribute a single factor of the form `x * τ x`. -/
def QuadraticOrbitProductStatement : Prop := by
  classical
  exact ∀ (I : Type u) [Fintype I] (G : Type v) [CommGroup G]
    (s : I → I), Function.Involutive s → ∀ (τ : G →* G) (f : I → G),
    (∀ i, f (s i) = τ (f i)) →
    ∃ x : G, (∏ i, f i) = (∏ i ∈ Finset.univ with s i = i, f i) * (x * τ x)

theorem quadraticOrbitProduct : QuadraticOrbitProductStatement.{u, v} := by
  intro I _ G _ s hs τ f hf
  classical
  let N := MonoidHom.id G * τ
  let π := QuotientGroup.mk' N.range
  let S := Finset.univ.filter fun i => s i ≠ i
  have hp : π (∏ i ∈ S, f i) = 1 := by
    rw [map_prod]
    refine Finset.prod_involution (fun i _ => s i) (fun i _ => ?_)
      (fun i hi _ => ?_) (fun i hi => ?_) (fun i _ => hs i)
    · rw [← map_mul]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨f i, by change f i * τ (f i) = _; rw [hf]⟩
    · exact (Finset.mem_filter.mp hi).2
    · have hne := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ (s i), by rw [hs]; exact Ne.symm hne⟩
  have hm : (∏ i ∈ S, f i) ∈ N.range := (QuotientGroup.eq_one_iff _).mp hp
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  change x * τ x = ∏ i ∈ S, f i at hx
  rw [hx]
  exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => s i = i) f).symm

end Langlands.Algebra
