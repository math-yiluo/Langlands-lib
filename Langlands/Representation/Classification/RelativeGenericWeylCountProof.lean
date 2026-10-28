import Langlands.Representation.Classification.RelativeGenericWeylCountStatement
import Langlands.Representation.Classification.UnitaryWeylRigidityProof

/-!
# Generic fine-twist Weyl self-association counts

Apply unitary real-exponent rigidity to the actual minimal self-association
witnesses, then use the insertion/forgetful equivalence of finite subtypes.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- The coarse Weyl restriction preserves the actual generic fine-twist
self-association count. -/
theorem glRelativeGenericWeylCount :
    GLRelativeGenericWeylCountStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B S V _ _ ω hωi hωa hωu v₀ t hgen C σ
  have hs : ∀ w : CuspidalSupport.AssociatingPermutations C C σ σ,
      w.val.val.val ∈ blockWeyl B := by
    intro w
    exact (glUnitaryWeylRealExponentRigidity.{uF, uV, uV} p F T n hn B).2.2
      S V ω hωi hωa hωu v₀ t hgen w.val.val.val w.val.property w.property
  refine ⟨hs, ?_⟩
  exact Nat.card_congr
    { toFun := fun w => w.val
      invFun := fun w => ⟨w, hs w⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }

end Langlands
