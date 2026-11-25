/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorDefinitions
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-!
# Tensor counit squares with a coefficient in degree zero

Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-tensor-single-cochain-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem tensorSingleRepresentative_eq
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (M : C) (P : CochainComplex C ℤ) :
    tensorSingleRepresentative M P =
      Functor.LaxMonoidal.μ DerivedCategory.Q P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P).hom := rfl

attribute [local irreducible] tensorSingleRepresentative

private theorem ordinary_tensor_single_base
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    {M : C} {N : D} (k : F.obj M ≅ N) (P : CochainComplex C ℤ) :
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj P ◁
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map k.hom)) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) N
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom =
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P).hom ≫
      (NatTrans.mapHomologicalComplex
        (Functor.OplaxMonoidal.δRightNatTrans F M ≫
          Functor.whiskerLeft F ((curriedTensor D).flip.map k.hom)) (.up ℤ)).app P := by
  let X := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hn :
      (X ◁ (HomologicalComplex.single _ (.up ℤ) 0).map k.hom) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) N X).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj M) X).hom ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor D).flip.map k.hom) (.up ℤ)).app X := by
    apply (cancel_epi
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) (F.obj M) X).inv).1
    rw [Iso.inv_hom_id_assoc]
    change _ ≫ HomologicalComplex.mapBifunctorMap (𝟙 X)
      ((HomologicalComplex.single _ (.up ℤ) 0).map k.hom) _ _ ≫ _ = _
    rw [← CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have h := CochainComplex.mapBifunctorComparison_δNatTrans_single₂ F P M
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P).inv)).1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [hn]
  erw [reassoc_of% h]
  rfl

private theorem ordinary_tensor_single
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Additive] [F.Monoidal] [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    {M : C} {N : D} (k : F.obj M ≅ N)
    (t : tensorRight M ⋙ F ≅ F ⋙ tensorRight N)
    (ht : Functor.OplaxMonoidal.δRightNatTrans F M ≫
      Functor.whiskerLeft F ((curriedTensor D).flip.map k.hom) = t.hom)
    (P : CochainComplex C ℤ) :
    Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj P ◁
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map k.hom)) ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor D) N
        ((F.mapHomologicalComplex (.up ℤ)).obj P)).hom =
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P).hom ≫
      ((Functor.mapHomologicalComplexCompIso t (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorRight N))
          (.up ℤ)).symm).hom.app P) := by
  rw [Functor.mapCochainComplex_δ]
  have h := ordinary_tensor_single_base F k P
  rw [ht, complex_square_hom] at h
  exact h

private theorem tensorCounitSingleDiagram
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (Q : C ⥤ D) [Q.LaxMonoidal] (R : E ⥤ H) [R.LaxMonoidal]
    (F : C ⥤ E) [F.OplaxMonoidal] (L : D ⥤ H) (P S V : C) (T V' : E)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ H).obj L).obj L).obj (curriedTensor H))
    (g : ∀ X, L.obj (Q.obj X) ⟶ R.obj (F.obj X))
    (q : P ⊗ S ⟶ V) (q' : F.obj P ⊗ T ⟶ V')
    (c : F.obj S ⟶ T) (s : L.obj (Q.obj S) ⟶ R.obj T)
    (t : F.obj V ⟶ V')
    (qM : Q.obj P ⊗ Q.obj S ⟶ Q.obj V)
    (qN : R.obj (F.obj P) ⊗ R.obj T ⟶ R.obj V')
    (hs : s = g S ≫ R.map c)
    (hδ : LaxSquareHδ (Q₁ := Q) (Q₂ := R) (F := F) δ g)
    (hq : Functor.OplaxMonoidal.δ F P S ≫ (F.obj P ◁ c) ≫ q' = F.map q ≫ t)
    (hn : L.map (Q.map q) ≫ g V = g (P ⊗ S) ≫ R.map (F.map q))
    (hM : qM = Functor.LaxMonoidal.μ Q P S ≫ Q.map q)
    (hN : qN = Functor.LaxMonoidal.μ R (F.obj P) T ≫ R.map q') :
    (δ.app (Q.obj P)).app (Q.obj S) ≫ (L.obj (Q.obj P) ◁ s) ≫ (g P ▷ R.obj T) ≫ qN =
    L.map qM ≫ g V ≫ R.map t := by
  rw [hM, hN]
  have hδ' := hδ P S
  rw [hs, ← Functor.LaxMonoidal.whiskerRight_whiskerLeft_μ_map_whiskerLeft_assoc]
  rw [← tensorHom_def_assoc, reassoc_of% hδ']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have h := congrArg
    (fun z ↦ L.map (Functor.LaxMonoidal.μ Q P S) ≫ g (P ⊗ S) ≫ R.map z) hq
  simpa only [Functor.map_comp, Category.assoc] using h

/-- The tensor counit square after fixing a coefficient in degree zero.
Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-tensor-single-cochain-counit). -/
def TensorSingleCounitSquare
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj L).obj L).obj
        (curriedTensor (DerivedCategory D)))
    (g : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (M : C) (N : D)
    (s : L.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N)
    (t : tensorRight M ⋙ F ≅ F ⋙ tensorRight N) (P : CochainComplex C ℤ) : Prop :=
    (δ.app (DerivedCategory.Q.obj P)).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (L.obj (DerivedCategory.Q.obj P) ◁ s.hom) ≫
        (g P ▷ (DerivedCategory.singleFunctor _ 0).obj N) ≫
        tensorSingleRepresentative N ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      L.map (tensorSingleRepresentative M P) ≫
        g (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso t (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ tensorRight N))
              (.up ℤ)).symm).hom.app P)

/-- The cochain tensor counit square implies its single-coefficient specialization.
Source: Stacks Project, Tags 07A4 and 0FPH
(blueprint: lem-pur-tensor-single-cochain-counit).
Proof: write the single-coefficient comparison as its geometric representative
followed by localization of the ordinary single-complex comparison and k. Lax
monoidal naturality moves this latter morphism through the tensorator. Apply the
cochain tensor counit square to P and single M. The ordinary bifunctor comparison
on a single complex, and naturality of its single-complex iso with respect to k,
identify the remaining map with the degreewise tensor comparison t. Naturality
of the geometric representative moves the total-tensor/single iso to the other
side; functoriality of Q and associativity finish the equation. -/
theorem tensor_single_cochain_counit
    {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
    [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.Monoidal] [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj L).obj L).obj
        (curriedTensor (DerivedCategory D)))
    (g : ∀ P : CochainComplex C ℤ, L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    {M : C} {N : D} (k : F.obj M ≅ N)
    (s : L.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N)
    (t : tensorRight M ⋙ F ≅ F ⋙ tensorRight N)
    (hs : s.hom = g ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map k.hom))
    (ht : Functor.OplaxMonoidal.δRightNatTrans F M ≫
      Functor.whiskerLeft F ((curriedTensor D).flip.map k.hom) = t.hom)
    (hd : LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := F.mapHomologicalComplex (.up ℤ)) δ g)
    (hn : ∀ {P R : CochainComplex C ℤ} (a : P ⟶ R),
      L.map (DerivedCategory.Q.map a) ≫ g R =
        g P ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a))
    (P : CochainComplex C ℤ) : TensorSingleCounitSquare F L δ g M N s t P := by
  let S := (HomologicalComplex.single _ (.up ℤ) 0).obj M
  let T := (HomologicalComplex.single _ (.up ℤ) 0).obj N
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let V := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P
  let V' := ((tensorRight N).mapHomologicalComplex (.up ℤ)).obj FP
  let c := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
    (HomologicalComplex.single _ (.up ℤ) 0).map k.hom
  exact tensorCounitSingleDiagram DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) L P S V T V' δ g
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) M P).hom
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) N FP).hom c s.hom _
    (tensorSingleRepresentative M P) (tensorSingleRepresentative N FP)
    hs hd (ordinary_tensor_single F k t ht P) (hn _)
    (tensorSingleRepresentative_eq M P) (tensorSingleRepresentative_eq N FP)

end AlgebraicGeometry.Etale
