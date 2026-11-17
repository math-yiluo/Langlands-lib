import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-! # Continuous descent through a closed-subgroup times compact-subgroup factorization -/

noncomputable section
open scoped Classical
open Topology
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def compactShear (K : Subgroup G) : G × K ≃ₜ G × K where
  toFun p := (p.1 * (p.2 : G), p.2)
  invFun p := (p.1 * (p.2 : G)⁻¹, p.2)
  left_inv p := by simp only [mul_inv_cancel_right]
  right_inv p := by simp only [inv_mul_cancel_right]
  continuous_toFun :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd).inv).prodMk continuous_snd

/-- Multiplication of a closed subgroup by a compact subgroup is a closed map. -/
theorem isClosedMap_subgroup_mul_compact (B K : Subgroup G)
    (hB : IsClosed (B : Set G)) (hK : IsCompact (K : Set G)) :
    IsClosedMap (fun p : B × K => (p.1 : G) * (p.2 : G)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hi : IsClosedMap (Prod.map (Subtype.val : B → G) (id : K → K)) :=
    (hB.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id).isClosedMap
  exact isClosedMap_fst_of_compactSpace.comp ((compactShear K).isClosedMap.comp hi)

/-- A closed-subgroup times compact-subgroup factorization gives a quotient map. -/
theorem isQuotientMap_subgroup_mul_compact (B K : Subgroup G)
    (hB : IsClosed (B : Set G)) (hK : IsCompact (K : Set G))
    (hsurj : Function.Surjective (fun p : B × K => (p.1 : G) * (p.2 : G))) :
    IsQuotientMap (fun p : B × K => (p.1 : G) * (p.2 : G)) :=
  (isClosedMap_subgroup_mul_compact B K hB hK).isQuotientMap
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) hsurj

/-- Continuous data constant on the factorization fibers descend continuously. -/
theorem exists_continuous_compact_factor_descent
    {X : Type*} [TopologicalSpace X] (B K : Subgroup G)
    (hB : IsClosed (B : Set G)) (hK : IsCompact (K : Set G))
    (hsurj : Function.Surjective (fun p : B × K => (p.1 : G) * (p.2 : G)))
    (f : B → X) (hf : Continuous f)
    (hcompat : ∀ b c : B, (b : G)⁻¹ * (c : G) ∈ K → f b = f c) :
    ∃ F : G → X, Continuous F ∧
      ∀ (b : B) (k : K), F ((b : G) * (k : G)) = f b := by
  let q : B × K → G := fun p => (p.1 : G) * (p.2 : G)
  have hq := isQuotientMap_subgroup_mul_compact B K hB hK hsurj
  let F : G → X := fun g => f (Function.surjInv hsurj g).1
  have heq (p : B × K) : F (q p) = f p.1 := by
    apply hcompat
    have he := Function.surjInv_eq hsurj (q p)
    change ((Function.surjInv hsurj (q p)).1 : G) *
      ((Function.surjInv hsurj (q p)).2 : G) = (p.1 : G) * (p.2 : G) at he
    have hz :
        ((Function.surjInv hsurj (q p)).1 : G)⁻¹ * (p.1 : G) =
          ((Function.surjInv hsurj (q p)).2 : G) * (p.2 : G)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← he, inv_mul_cancel_left]
    rw [hz]
    exact K.mul_mem (Function.surjInv hsurj (q p)).2.property (K.inv_mem p.2.property)
  refine ⟨F, hq.continuous_iff.mpr ?_, fun b k => heq (b, k)⟩
  have hcomp : F ∘ q = f ∘ Prod.fst := funext heq
  rw [hcomp]
  exact hf.comp continuous_fst

end Langlands.Global.RankinSelbergGlobal.GaugeDescent
