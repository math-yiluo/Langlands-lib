import Langlands.Algebra.NonUnitalModuleDualCompletionStatement

/-! # Proof that the completion of the nondegenerate dual is the full dual (Renard I.4.3)

For a complex algebra with idempotents `A` and a nondegenerate `A`-module `M`, the published
maps `toCompletion : M^* → completion(M̃)` and `toFullDual : completion(M̃) → M^*` are inverse
to each other. The proof is direct: it evaluates both composites at a vector, using a fixing
idempotent for `toFullDual` and the fixation law of compatible families.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualCompletion

open MulOpposite
open NonUnitalModuleDual (FullDual Dual)
open NonUnitalModuleDualFixedPartMaps (oppositeIdempotent)

universe uA uM

attribute [local instance] NonUnitalModuleDual.fullAction NonUnitalModuleDual.dualAction

section Inverse

/-- The idempotent of `A` underlying an idempotent of `Aᵐᵒᵖ`. -/
private def unopIdempotent {A : Type uA} [NonUnitalRing A] (e : Idempotent Aᵐᵒᵖ) :
    Idempotent A :=
  ⟨e.val.unop, congrArg MulOpposite.unop e.property.eq⟩

/-- Taking the opposite of the underlying idempotent recovers the given idempotent. -/
private theorem oppositeIdempotent_unopIdempotent {A : Type uA} [NonUnitalRing A]
    (e : Idempotent Aᵐᵒᵖ) : oppositeIdempotent (unopIdempotent e) = e := rfl

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The first composite: `toFullDual (toCompletion φ) = φ`. At `m`, with `e` fixing `m`, the
value is `(e · φ)(m) = φ(e · m) = φ(m)`. -/
theorem toFullDual_toCompletion (φ : FullDual hA hM) :
    toFullDual hA hM (toCompletion hA hM φ) = φ := by
  let _ := NondegenerateScalars.complexModule hA hM
  apply LinearMap.ext
  intro m
  obtain ⟨e, he⟩ := hM m
  rw [toFullDual_apply hA hM _ m e he]
  change φ ((e : A) • m) = φ m
  rw [he]

/-- The second composite: `toCompletion (toFullDual x) = x`. The `e`-coordinate evaluated at
`m` is `toFullDual x (e · m)`; since `e` fixes `e · m`, this is `x(e)(e · m) = (e · x(e))(m)`,
which is `x(e)(m)` by the fixation law of the compatible family `x`. -/
theorem toCompletion_toFullDual (x : NonUnitalModuleLeftLimit Aᵐᵒᵖ (Dual hA hM)) :
    toCompletion hA hM (toFullDual hA hM x) = x := by
  let _ := NondegenerateScalars.complexModule hA hM
  apply Subtype.ext
  funext e
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  have hfix : (unopIdempotent e).val • ((unopIdempotent e).val • m) =
      (unopIdempotent e).val • m := by
    rw [← mul_smul, (unopIdempotent e).property.eq]
  change toFullDual hA hM x ((unopIdempotent e).val • m) = (x.val e).val m
  rw [toFullDual_apply hA hM x _ (unopIdempotent e) hfix,
    oppositeIdempotent_unopIdempotent]
  change ((e.val : Aᵐᵒᵖ) • x.val e).val m = (x.val e).val m
  rw [x.property.1 e]

/-- Renard I.4.3: the published maps `toCompletion` and `toFullDual` between the full dual
`M^*` and the completion of the nondegenerate dual `M̃` are inverse to each other. -/
theorem dualCompletionStatement : DualCompletionStatement.{uA, uM} := by
  intro A _ _ _ _ M _ _ hA hM
  exact ⟨toFullDual_toCompletion hA hM, toCompletion_toFullDual hA hM⟩

end Inverse

end Langlands.Algebra.NonUnitalModuleDualCompletion
