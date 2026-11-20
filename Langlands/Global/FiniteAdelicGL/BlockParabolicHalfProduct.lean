import Langlands.Global.AdelicBlockCompactProjection
import Langlands.Global.FiniteAdelicGL.BlockInductionNormalization
import Langlands.Global.FiniteAdelicGL.CompactProduct

/-!
# Finite-place product of the adelic parabolic half character

The restriction of the adelic positive half character to a finite parabolic
element equals the product of the canonical local halves over any finite set
outside which the matrix is integral.
-/

noncomputable section

open scoped BigOperators Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open Langlands.GeneralLinear AdelicBlockParabolic CompletionPadic PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

private def finitePlacePart (v : FinitePlace F) (p : Finite F B) : Finite F B :=
  AdelicBlockParabolic.finite F B
    (finitePlaceParabolicInclusion F B v (FiniteAdelicGL.localParabolicProjection F B v p))

private theorem finitePlacePart_val (v : FinitePlace F) (p : Finite F B) :
    (finitePlacePart F B v p).val =
      FiniteAdelicGL.localInclusion F n v (FiniteAdelicGL.localProjection F n v p.val) := by
  change AdelicGL.finite F n (finitePlaceParabolicInclusion F B v
    (FiniteAdelicGL.localParabolicProjection F B v p)).val = _
  rw [finitePlaceParabolicInclusion_val]
  change AdelicGL.finite F n (AdelicGL.pair F n 1
    (FiniteAdelicGL.localInclusion F n v (FiniteAdelicGL.localProjection F n v p.val))) = _
  rw [AdelicGL.finite_pair]

private theorem ofFinite_finitePlacePart (v : FinitePlace F) (p : Finite F B) :
    AdelicBlockParabolic.ofFinite F B (finitePlacePart F B v p) =
      finitePlaceParabolicInclusion F B v (FiniteAdelicGL.localParabolicProjection F B v p) := by
  apply Subtype.ext
  change AdelicGL.pair F n 1 (finitePlacePart F B v p).val = _
  rw [finitePlacePart_val, finitePlaceParabolicInclusion_val]
  rfl

private theorem localProjection_remove_finitePlacePart (v w : FinitePlace F) (p : Finite F B) :
    FiniteAdelicGL.localProjection F n w ((finitePlacePart F B v p)⁻¹ * p).val =
      if w = v then 1 else FiniteAdelicGL.localProjection F n w p.val := by
  classical
  change FiniteAdelicGL.localProjection F n w ((finitePlacePart F B v p).val⁻¹ * p.val) = _
  rw [map_mul, map_inv, finitePlacePart_val]
  by_cases h : w = v
  · subst w
    rw [FiniteAdelicGL.localProjection_localInclusion, inv_mul_cancel, ite_eq_left rfl]
  · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w h,
      inv_one, one_mul, ite_eq_right h]

private theorem parabolicHalfCharacter_ofFinite_eq_one_of_integral (p : Finite F B)
    (hp : p.val ∈ FiniteAdelicGL.standardIntegral F n) :
    parabolicHalfCharacter F B (AdelicBlockParabolic.ofFinite F B p) = 1 := by
  apply parabolicHalfCharacter_eq_one_of_mem_standardCompact B F
  change AdelicGL.pair F n 1 p.val ∈ standardCompact F n
  rw [mem_standardCompact_iff, AdelicGL.infinite_pair, AdelicGL.finite_pair]
  exact ⟨one_mem _, hp⟩

/-- The positive half character of an actual finite adelic parabolic is the
product of the canonical local positive halves on a set containing all its
nonintegral coordinates. -/
theorem parabolicHalfCharacter_ofFinite_eq_prod (S : Finset (FinitePlace F))
    (p : Finite F B)
    (hp : ∀ v ∉ S, FiniteAdelicGL.localProjection F n v p.val ∈
      FiniteAdelicGL.localIntegral F n v) :
    parabolicHalfCharacter F B (AdelicBlockParabolic.ofFinite F B p) =
      ∏ v ∈ S, (padicField v).canonicalTopologicalData.parabolicHalfModulus B
        (FiniteAdelicGL.localParabolicProjection F B v p) := by
  classical
  induction S using Finset.induction_on generalizing p with
  | empty =>
    rw [Finset.prod_empty]
    apply parabolicHalfCharacter_ofFinite_eq_one_of_integral F B p
    exact (FiniteAdelicGL.mem_standardIntegral_iff_local F n _).mpr
      fun v => hp v (Finset.notMem_empty v)
  | insert v S hv ih =>
    let a := finitePlacePart F B v p
    let q := a⁻¹ * p
    have hq (w : FinitePlace F) :
        FiniteAdelicGL.localProjection F n w q.val =
          if w = v then 1 else FiniteAdelicGL.localProjection F n w p.val :=
      localProjection_remove_finitePlacePart F B v w p
    have hqint (w : FinitePlace F) (hw : w ∉ S) :
        FiniteAdelicGL.localProjection F n w q.val ∈ FiniteAdelicGL.localIntegral F n w := by
      rw [hq]
      by_cases he : w = v
      · rw [ite_eq_left he]
        exact one_mem _
      · rw [ite_eq_right he]
        exact hp w (by simp [he, hw])
    have hsplit : AdelicBlockParabolic.ofFinite F B p =
        AdelicBlockParabolic.ofFinite F B a * AdelicBlockParabolic.ofFinite F B q := by
      rw [← map_mul, show a * q = p from mul_inv_cancel_left a p]
    rw [hsplit, map_mul, ofFinite_finitePlacePart, parabolicHalfCharacter_finitePlaceParabolicInclusion,
      ih q hqint, Finset.prod_insert hv]
    congr 1
    refine Finset.prod_congr rfl fun w hw => congrArg _ ?_
    apply Subtype.ext
    change FiniteAdelicGL.localProjection F n w q.val = FiniteAdelicGL.localProjection F n w p.val
    rw [hq, ite_eq_right (fun h : w = v => hv (h ▸ hw))]

end Langlands.Global.AdelicBlockDeterminantCharacter
