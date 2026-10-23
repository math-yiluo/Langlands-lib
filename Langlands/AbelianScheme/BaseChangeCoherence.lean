import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.AbelianScheme.RationalBaseChange

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u
namespace Langlands.AbelianScheme
variable {S S' S'' : Scheme.{u}}

/-- Identity pullback of an abelian scheme is canonically isomorphic to itself. -/
def baseChangeIdIso (A : AbelianScheme S) : (baseChange (𝟙 S)).obj A ≅ A where
  hom := Additive.ofMul (GroupScheme.baseChangeIdIso A.toGrp).hom
  inv := Additive.ofMul (GroupScheme.baseChangeIdIso A.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul (GroupScheme.baseChangeIdIso A.toGrp).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (GroupScheme.baseChangeIdIso A.toGrp).inv_hom_id

/-- Direct pullback is canonically isomorphic to successive pullback. -/
def baseChangeCompIso (b : S' ⟶ S) (c : S'' ⟶ S') (A : AbelianScheme S) :
    (baseChange (c ≫ b)).obj A ≅ (baseChange c).obj ((baseChange b).obj A) where
  hom := Additive.ofMul (GroupScheme.baseChangeCompIso b c A.toGrp).hom
  inv := Additive.ofMul (GroupScheme.baseChangeCompIso b c A.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul (GroupScheme.baseChangeCompIso b c A.toGrp).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (GroupScheme.baseChangeCompIso b c A.toGrp).inv_hom_id

/-- The identity comparison is natural in the abelian scheme. -/
def baseChangeIdNatIso : baseChange (𝟙 S) ≅ 𝟭 (AbelianScheme S) :=
  NatIso.ofComponents baseChangeIdIso (by
    intro A B f
    exact congrArg Additive.ofMul
      ((Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso).hom.naturality
        (groupHom f)))

/-- The composition comparison is natural in the abelian scheme. -/
def baseChangeCompNatIso (b : S' ⟶ S) (c : S'' ⟶ S') :
    baseChange (c ≫ b) ≅ baseChange b ⋙ baseChange c :=
  NatIso.ofComponents (baseChangeCompIso b c) (by
    intro A B f
    exact congrArg Additive.ofMul
      ((Functor.mapGrpNatIso (Over.pullbackComp c b) ≪≫
        Functor.mapGrpCompIso).hom.naturality (groupHom f)))

/-- The identity comparison in the category of actual rational homomorphisms. -/
def rationalBaseChangeIdIso (A : AbelianScheme S) :
    Rationalization.of ((baseChange (𝟙 S)).obj A) ≅ Rationalization.of A :=
  Rationalization.inclusion.mapIso (baseChangeIdIso A)

/-- The composition comparison in the category of actual rational homomorphisms. -/
def rationalBaseChangeCompIso (b : S' ⟶ S) (c : S'' ⟶ S') (A : AbelianScheme S) :
    Rationalization.of ((baseChange (c ≫ b)).obj A) ≅
      Rationalization.of ((baseChange c).obj ((baseChange b).obj A)) :=
  Rationalization.inclusion.mapIso (baseChangeCompIso b c A)

/-- Identity pullback on Hom0 agrees with the original map under the comparison. -/
theorem rationalBaseChangeHom_id {A B : AbelianScheme S} (f : Hom0 A B) :
    comp0 _ _ _ (rationalBaseChangeHom (𝟙 S) f) (homToHom0 (baseChangeIdIso B).hom) =
      comp0 _ _ _ (homToHom0 (baseChangeIdIso A).hom) f := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalBaseChangeHom_tmul, homToHom0_apply, comp0_tmul, mul_one, one_mul]
    exact congrArg (fun g => q ⊗ₜ[ℤ] g) (baseChangeIdNatIso.hom.naturality f)
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

/-- Successive pullback on Hom0 agrees with direct pullback under the comparison. -/
theorem rationalBaseChangeHom_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    {A B : AbelianScheme S} (f : Hom0 A B) :
    comp0 _ _ _ (rationalBaseChangeHom (c ≫ b) f)
        (homToHom0 (baseChangeCompIso b c B).hom) =
      comp0 _ _ _ (homToHom0 (baseChangeCompIso b c A).hom)
        (rationalBaseChangeHom c (rationalBaseChangeHom b f)) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalBaseChangeHom_tmul, homToHom0_apply, comp0_tmul, mul_one, one_mul]
    exact congrArg (fun g => q ⊗ₜ[ℤ] g) ((baseChangeCompNatIso b c).hom.naturality f)
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

/-- Identity base change is naturally the identity on the rationalized category. -/
def rationalBaseChangeIdNatIso : rationalBaseChange (𝟙 S) ≅ 𝟭 (RationalCategory S) :=
  NatIso.ofComponents (fun A => rationalBaseChangeIdIso A.obj) (by
    intro A B f
    exact rationalBaseChangeHom_id f)

/-- Direct and successive pullback are naturally isomorphic on the rationalized category. -/
def rationalBaseChangeCompNatIso (b : S' ⟶ S) (c : S'' ⟶ S') :
    rationalBaseChange (c ≫ b) ≅ rationalBaseChange b ⋙ rationalBaseChange c :=
  NatIso.ofComponents (fun A => rationalBaseChangeCompIso b c A.obj) (by
    intro A B f
    exact rationalBaseChangeHom_base_comp b c f)

end Langlands.AbelianScheme
