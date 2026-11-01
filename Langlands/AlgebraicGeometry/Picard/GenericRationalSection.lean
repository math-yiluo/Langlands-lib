import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Langlands.AlgebraicGeometry.Picard.GenericFractionField

/-! # Generic residue-field maps as rational sections -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {S X : Scheme.{u}} [IsIntegral S] (p : X ⟶ S)

/-- Change from the actual generic residue-field spectrum to the generic
stalk spectrum, retaining the equation over the base. -/
def genericResidueFunctionFieldEquiv :
    {sη : Spec (S.residueField (genericPoint S)) ⟶ X //
      sη ≫ p = S.fromSpecResidueField (genericPoint S)} ≃
    {sη : Spec S.functionField ⟶ X //
      sη ≫ p = S.fromSpecStalk (genericPoint S) ≫ 𝟙 S} := by
  have := isIso_genericPoint_residue S
  let q := Spec.map (S.residue (genericPoint S))
  have hq : IsIso q := inferInstance
  refine
    { toFun := fun sη => ⟨inv q ≫ sη.val, ?_⟩
      invFun := fun sη => ⟨q ≫ sη.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Category.assoc, sη.property, Scheme.fromSpecResidueField]
    simp [q]
  · rw [Category.assoc, sη.property, Category.comp_id]
    rfl
  · intro sη
    apply Subtype.ext
    simp
  · intro sη
    apply Subtype.ext
    simp

/-- Actual generic residue-field maps over an integral base correspond to
rational sections when the target is locally of finite type over the base. -/
def genericRationalSectionEquiv [LocallyOfFiniteType p] :
    {sη : Spec (S.residueField (genericPoint S)) ⟶ X //
      sη ≫ p = S.fromSpecResidueField (genericPoint S)} ≃
    {s : S.RationalMap X //
      s.compHom p = Scheme.Hom.toRationalMap (𝟙 S)} :=
  (genericResidueFunctionFieldEquiv p).trans
    (Scheme.RationalMap.equivFunctionField (𝟙 S) p)

end Langlands.AlgebraicGeometry
