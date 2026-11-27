import Langlands.AbelianScheme.LieBaseChange
import Langlands.AbelianScheme.PointedMorphismRigidityProof
import Langlands.AlgebraicGeometry.Picard.TranslationBaseChange
import Langlands.GroupScheme.TranslationLaws

/-! # Normalizing a lift of an abelian scheme homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

variable {S T : Scheme.{u}} {A B : AbelianScheme S}

/-- Translate the value of a scheme morphism at the source identity back to the
identity of the target. The resulting pointed morphism is a homomorphism. -/
def normalizeSchemeMorphism (p : A.X ⟶ B.X) : A ⟶ B := by
  let σ : Over.mk (𝟙 S) ⟶ B.X := η[A.X] ≫ p
  let q := p ≫ GroupScheme.translation B.toGrp σ⁻¹
  have hq : η[A.X] ≫ q = η[B.X] := by
    change (η[A.X] ≫ p ≫ GroupScheme.translation B.toGrp σ⁻¹) = _
    rw [← Category.assoc, GroupScheme.CommonAffine.section_comp_translation, inv_mul_cancel]
    rfl
  letI : IsMonHom q := pointedMorphismRigidity S A.toGrp B.toGrp A.isAbelian
    inferInstance inferInstance inferInstance q hq
  exact Additive.ofMul (Grp.homMk'' q (IsMonHom.one_hom q) (IsMonHom.mul_hom q))

/-- A scheme morphism over the thicker base that reduces to an abelian scheme
homomorphism can be translated to a homomorphism with that same reduction. -/
theorem exists_hom_of_baseChange_scheme_lift (b : T ⟶ S)
    (f : (baseChange b).obj A ⟶ (baseChange b).obj B)
    (g₁ : A.X.left ⟶ B.X.left) (hg₁ : g₁ ≫ B.X.hom = A.X.hom)
    (hg₁₀ : pullback.fst A.X.hom b ≫ g₁ = hom f ≫ pullback.fst B.X.hom b) :
    ∃ u : A ⟶ B, (baseChange b).map u = f := by
  let p : A.X ⟶ B.X := Over.homMk g₁ hg₁
  let σ : Over.mk (𝟙 S) ⟶ B.X := η[A.X] ≫ p
  let u := normalizeSchemeMorphism p
  let a := pullback.fst A.X.hom b
  let c := pullback.fst B.X.hom b
  let T₁ := Over.mk (𝟙 T)
  let E := GroupScheme.baseChangePointsEquiv b B.toGrp T₁
  have hσ : (Over.mkIdTerminal.from ((Over.map b).obj T₁) ≫ σ) = 1 := by
    have hunit : (1 : (Over.map b).obj T₁ ⟶ B.X) =
        Over.mkIdTerminal.from ((Over.map b).obj T₁) ≫ η[B.X] := by
      change CartesianMonoidalCategory.toUnit ((Over.map b).obj T₁) ≫ η[B.X] = _
      exact congrArg (· ≫ η[B.X]) (Over.mkIdTerminal.hom_ext _ _)
    rw [hunit]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.mkIdTerminal_from_left, Over.map_obj_hom, T₁,
      Over.mk_hom]
    change b ≫ (GroupScheme.identitySection A.toGrp ≫ g₁) = b ≫ GroupScheme.identitySection B.toGrp
    rw [← GroupScheme.identitySection_baseChange_fst_assoc b A.toGrp, hg₁₀,
      ← Category.assoc, GroupScheme.identitySection_naturality (groupHom f),
      GroupScheme.identitySection_baseChange_fst]
  have hσ' : GroupScheme.baseChangeSection b B.toGrp σ⁻¹ = 1 := by
    change E.symm (Over.mkIdTerminal.from ((Over.map b).obj T₁) ≫ σ⁻¹) = 1
    rw [GrpObj.comp_inv, hσ, inv_one, map_one]
  refine ⟨u, ?_⟩
  suffices h : groupHom ((baseChange b).map u) = groupHom f by
    exact congrArg Additive.ofMul h
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (((baseChange b).map u).toMul.hom.hom.left) ≫ c = hom f ≫ c
    have hbu : hom ((baseChange b).map u) ≫ c = a ≫ hom u := by
      exact pullback.lift_fst _ _ _
    rw [hbu]
    change a ≫ g₁ ≫ (GroupScheme.translation B.toGrp σ⁻¹).left = hom f ≫ c
    rw [← Category.assoc, hg₁₀, Category.assoc,
      ← GroupScheme.translation_baseChangeSection b B.toGrp σ⁻¹, hσ',
      GroupScheme.translation_one, Over.id_left, Category.id_comp]
  · exact (groupHom ((baseChange b).map u)).hom.hom.w.trans (groupHom f).hom.hom.w.symm

end Langlands.AbelianScheme
