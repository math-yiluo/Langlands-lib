/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SmallCechFreeExact
public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Free Yoneda comparison with the categorical Čech cochains

Source: Stacks Project, Cohomology on Sites, Tag 03AS.
-/

@[expose] public section

universe u v

namespace CategoryTheory.SmallCech

open CategoryTheory Limits Opposite

variable {C : Type u} [Category.{v} C] (X : C)

/-- Extend sections on summands by the free abelian group universal property.
Source: Stacks 03AS. 
(blueprint: lem-sc-small-cech-free-comparison)
-/
noncomputable def freeDesc (Y : FormalCoproduct.{v} (Over X))
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (b : ∀ i, P.obj (op (Y.obj i).left)) :
    (freePresheaf X).obj Y ⟶ P where
  app Z := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift fun a ↦ P.map a.2.op (b a.1))
  naturality Z W g := by
    apply AddCommGrpCat.homAddEquiv.injective
    apply FreeAbelianGroup.lift_ext
    intro a
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.map _ (FreeAbelianGroup.of a)) =
      P.map g (FreeAbelianGroup.lift _ (FreeAbelianGroup.of a))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    change P.map (g.unop ≫ a.2).op (b a.1) = P.map g (P.map a.2.op (b a.1))
    rw [op_comp, P.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Free Yoneda identifies maps out of the representable sum with sections on its summands.
Source: Stacks 03AS. 
(blueprint: lem-sc-small-cech-free-comparison)
-/
noncomputable def freeHomEquiv (Y : FormalCoproduct.{v} (Over X))
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((freePresheaf X).obj Y ⟶ P) ≃+ (∀ i, P.obj (op (Y.obj i).left)) where
  toFun a i := a.app (op (Y.obj i).left) (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)
  invFun := freeDesc X Y P
  left_inv a := by
    apply NatTrans.ext
    funext Z
    apply AddCommGrpCat.homAddEquiv.injective
    apply FreeAbelianGroup.lift_ext
    intro x
    obtain ⟨i, g⟩ := x
    change FreeAbelianGroup.lift _
      (FreeAbelianGroup.of (⟨i, g⟩ : (tupleRepresentables X Y).obj Z)) =
      a.app Z (FreeAbelianGroup.of ⟨i, g⟩)
    rw [FreeAbelianGroup.lift_apply_of]
    have h := NatTrans.naturality_apply a g.op (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)
    change a.app Z (FreeAbelianGroup.map
      (fun x : (tupleRepresentables X Y).obj (op (Y.obj i).left) ↦
        (⟨x.1, g ≫ x.2⟩ : (tupleRepresentables X Y).obj Z))
      (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)) = _ at h
    rw [FreeAbelianGroup.map_of_apply, Category.comp_id] at h
    exact h.symm
  right_inv b := by
    funext i
    change FreeAbelianGroup.lift _ (FreeAbelianGroup.of
      (⟨i, 𝟙 _⟩ : (tupleRepresentables X Y).obj (op (Y.obj i).left))) = b i
    rw [FreeAbelianGroup.lift_apply_of]
    simp
  map_add' a b := by
    funext i
    rfl

/-- The categorical product is the group of dependent functions.
Source: the product universal property, as used in Stacks 03AS. 
(blueprint: lem-sc-small-cech-free-comparison)
-/
noncomputable def productIso {J : Type v} (F : J → AddCommGrpCat.{v}) :
    (∏ᶜ F) ≅ AddCommGrpCat.of (∀ j, F j) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor F))
    (AddCommGrpCat.HasLimit.productLimitCone F).isLimit

private theorem hom_sum_apply {J : Type*} [Fintype J] {A B : AddCommGrpCat.{v}}
    (f : J → (A ⟶ B)) (x : A) : (∑ j, f j) x = ∑ j, f j x := by
  change (AddCommGrpCat.homAddEquiv (∑ j, f j)) x = _
  rw [map_sum]
  simp only [AddMonoidHom.finsetSum_apply, AddCommGrpCat.homAddEquiv_apply]

private theorem hom_map_sum {J : Type*} [Fintype J] {A B : AddCommGrpCat.{v}}
    (f : A ⟶ B) (x : J → A) : f (∑ j, x j) = ∑ j, f (x j) := map_sum f.hom _ _

private theorem hom_map_zsmul {A B : AddCommGrpCat.{v}} (f : A ⟶ B) (r : ℤ)
    (x : A) : f (r • x) = r • f x := f.hom.map_zsmul _ _

private theorem hom_zsmul_apply {A B : AddCommGrpCat.{v}} (r : ℤ)
    (f : A ⟶ B) (x : A) : (r • f) x = r • f x := rfl

/-- Free Yoneda followed by the universal property of the categorical product.
Source: Stacks 03AS. 
(blueprint: lem-sc-small-cech-free-comparison)
-/
noncomputable def sectionsEquiv (Y : FormalCoproduct.{v} (Over X))
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    ((freePresheaf X).obj Y ⟶ P) ≃+
      ((∏ᶜ fun i ↦ P.obj (op (Y.obj i).left)) : AddCommGrpCat.{v}) :=
  (freeHomEquiv X Y P).trans (productIso _).addCommGroupIsoToAddEquiv.symm

private theorem sectionsEquiv_π (Y : FormalCoproduct.{v} (Over X))
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (a : (freePresheaf X).obj Y ⟶ P) (i : Y.I) :
    Pi.π (fun i ↦ P.obj (op (Y.obj i).left)) i (sectionsEquiv X Y P a) =
      freeHomEquiv X Y P a i := by
  exact ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit (Discrete.functor (fun i ↦ P.obj (op (Y.obj i).left))))
      (AddCommGrpCat.HasLimit.productLimitCone _).isLimit (Discrete.mk i))
    (freeHomEquiv X Y P a)

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable [HasFiniteWidePullbacks C] {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/-- The free Yoneda and product comparison in each Čech degree.
Source: Stacks 03AS. 
(blueprint: lem-sc-small-cech-free-comparison)
-/
noncomputable def cochainEquiv (n : ℕ) :
    ((freeComplex X U π).X n ⟶ P) ≃+
      ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
        ((Over.forget X).op ⋙ P)).X n :=
  sectionsEquiv X _ P

set_option backward.isDefEq.respectTransparency false in
omit [HasFiniteWidePullbacks C] in
private theorem freeHomEquiv_map {Y Y' : FormalCoproduct.{v} (Over X)}
    (f : Y ⟶ Y') (a : (freePresheaf X).obj Y' ⟶ P) (i : Y.I) :
    freeHomEquiv X Y P ((freePresheaf X).map f ≫ a) i =
      P.map (f.φ i).left.op (freeHomEquiv X Y' P a (f.f i)) := by
  change a.app _ (FreeAbelianGroup.map
    (fun x : (tupleRepresentables X Y).obj (op (Y.obj i).left) ↦
      (⟨f.f x.1, x.2 ≫ (f.φ x.1).left⟩ :
        (tupleRepresentables X Y').obj (op (Y.obj i).left)))
    (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)) = _
  rw [FreeAbelianGroup.map_of_apply, Category.id_comp]
  have h := NatTrans.naturality_apply a (f.φ i).left.op
    (FreeAbelianGroup.of ⟨f.f i, 𝟙 _⟩)
  change a.app _ (FreeAbelianGroup.map
    (fun x : (tupleRepresentables X Y').obj (op (Y'.obj (f.f i)).left) ↦
      (⟨x.1, (f.φ i).left ≫ x.2⟩ :
        (tupleRepresentables X Y').obj (op (Y.obj i).left)))
    (FreeAbelianGroup.of ⟨f.f i, 𝟙 _⟩)) = _ at h
  rw [FreeAbelianGroup.map_of_apply, Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The comparison takes the alternating projection boundary to the Čech differential.
Source: Stacks Project, Cohomology on Sites, Tags 03AS and 03AT.
(blueprint: lem-sc-small-cech-free-comparison)

Proof: The free representable adjunction sends a natural transformation to its
value on the generator given by the identity of the represented product. For each
face, naturality identifies precomposition by the projection with restriction of
that value along the projection. The product universal property identifies the
family of these values with the categorical product used in cechComplexFunctor.
Both differentials are the sum of these face maps with coefficient (-1)^j,
so the additive degreewise comparison intertwines their differentials. -/
theorem cochainEquiv_boundary (n : ℕ) (a : (freeComplex X U π).X n ⟶ P) :
    cochainEquiv X U π P (n + 1) ((freeComplex X U π).d (n + 1) n ≫ a) =
      (((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
        ((Over.forget X).op ⋙ P)).d n (n + 1)) (cochainEquiv X U π P n a) := by
  apply Concrete.limit_ext
  intro ⟨t⟩
  change Pi.π (fun i ↦ P.obj (op
    (((FormalCoproduct.mk ι (fun i ↦ Over.mk (π i))).cech.obj
      (op (SimplexCategory.mk (n + 1)))).obj i).left))
    t (sectionsEquiv X _ P _) = _
  rw [sectionsEquiv_π]
  simp only [freeComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.zsmul_comp, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  simp only [SimplicialObject.δ, Functor.comp_map, freeHomEquiv_map]
  simp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    Functor.comp_obj, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [hom_sum_apply]
  simp only [hom_zsmul_apply]
  rw [hom_map_sum]
  simp only [hom_map_zsmul]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor,
    Functor.comp_obj]
  dsimp only [Functor.whiskeringLeft, Functor.comp_map]
  simp only [FormalCoproduct.evalOp_obj_map, Functor.rightOp_map]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  conv_rhs => erw [← AddCommGrpCat.comp_apply, Pi.lift_comp_π, AddCommGrpCat.comp_apply]
  dsimp only [cochainEquiv]
  erw [sectionsEquiv_π]
  rfl

end CategoryTheory.SmallCech
