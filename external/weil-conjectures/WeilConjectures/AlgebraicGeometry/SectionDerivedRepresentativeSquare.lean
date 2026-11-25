/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.AlgebraicGeometry.SectionKFlatTensorComparison
public import WeilConjectures.AlgebraicGeometry.SectionOplaxTotalComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.Topology.ProfiniteCondensedRing
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.InternalOplaxResolvingComponents
import WeilConjectures.AlgebraicGeometry.SectionResolutionConjugationIdentities
import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintDiagrams

/-! # The actual internal derived tensor arrow on section representatives

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
the internal/section normalization argument
(auxiliary; not a blueprint node).

The component below is a conjugate of `internalDelta`, never a definition by its
representative square. The other helpers expose precisely the square's two sides,
its naturality, and the localized associator and unitor paths.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u₁ v₁ u₂ v₂ a b c d va vb vc vd
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace DerivedRepresentativeSquare

private def uncurryPostIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u} [Category E]
    (B : C ⥤ C ⥤ D) (F : D ⥤ E) :
    Functor.uncurry.obj B ⋙ F ≅
      Functor.uncurry.obj ((Functor.postcompose₂.obj F).obj B) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N k
    simp [Functor.uncurry, Functor.map_comp])

section GenericSquare
variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  (B₁ : C₁ × C₁ ⥤ C₁) (B₂ : C₂ × C₂ ⥤ C₂)
  (e : C₁ ≌ D₁) (H : C₂ ⥤ D₂) (F : C₁ ⥤ C₂) (L : D₁ ⥤ D₂)
  (TY : D₁ × D₁ ⥤ D₁) (TX : D₂ × D₂ ⥤ D₂)
  (θY : B₁ ⋙ e.functor ≅
    (e.functor.prod e.functor) ⋙ TY)
  (θX : B₂ ⋙ H ≅ (H.prod H) ⋙ TX)
  (γ : F ⋙ H ≅ e.functor ⋙ L)
  (di : B₁ ⋙ F ≅
    (F.prod F) ⋙ B₂)
  (d : TY ⋙ L ≅ (L.prod L) ⋙ TX)

private def conjugatedIso :
    TY ⋙ L ≅
      ((L).prod (L)) ⋙ TX := by
  let G := e.inverse
  let E := H
  let a := e.counitIso
  exact
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod a.symm a.symm) (TY)) L ≪≫
    Functor.isoWhiskerLeft (G.prod G)
      (Functor.isoWhiskerRight (θY).symm L) ≪≫
    Functor.isoWhiskerLeft ((G.prod G) ⋙
      B₁)
      (γ).symm ≪≫
    Functor.isoWhiskerLeft (G.prod G) (Functor.isoWhiskerRight di E) ≪≫
    Functor.isoWhiskerLeft ((G.prod G) ⋙ (F.prod F)) (θX) ≪≫
    Functor.isoWhiskerLeft (G.prod G)
      (Functor.isoWhiskerRight
        (NatIso.prod (γ) (γ))
        (TX)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Functor.isoWhiskerRight a L) (Functor.isoWhiskerRight a L))
      (TX)

private theorem conjugatedIso_hom (M N : D₁) :
    (conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di).hom.app (M, N) =
      L.map (TY.map (Prod.mkHom (e.counitIso.inv.app M) (e.counitIso.inv.app N))) ≫
      L.map (θY.inv.app (e.inverse.obj M, e.inverse.obj N)) ≫
      γ.inv.app (B₁.obj (e.inverse.obj M, e.inverse.obj N)) ≫
      H.map (di.hom.app (e.inverse.obj M, e.inverse.obj N)) ≫
      θX.hom.app (F.obj (e.inverse.obj M), F.obj (e.inverse.obj N)) ≫
      TX.map (Prod.mkHom (γ.hom.app (e.inverse.obj M)) (γ.hom.app (e.inverse.obj N))) ≫
      TX.map (Prod.mkHom (L.map (e.counitIso.hom.app M))
        (L.map (e.counitIso.hom.app N))) := by
  rfl

private def genericSquareLeft :
    B₁ ⋙
        F ⋙ H ≅
      (e.functor.prod e.functor) ⋙
        ((L).prod (L)) ⋙ TX := by
  exact Functor.isoWhiskerRight di H ≪≫
    Functor.isoWhiskerLeft
      ((F).prod (F))
      (θX) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (γ) (γ)) (TX)

private def genericSquareRight :
    B₁ ⋙
        F ⋙ H ≅
      (e.functor.prod e.functor) ⋙
        ((L).prod (L)) ⋙ TX :=
  Functor.isoWhiskerLeft (B₁)
      (γ) ≪≫
    Functor.isoWhiskerRight (θY) (L) ≪≫
    Functor.isoWhiskerLeft
      (e.functor.prod e.functor)
      (d)

private instance isIso_prod_mkHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {M N : C} {P Q : D} (a : M ⟶ N) (b : P ⟶ Q) [IsIso a] [IsIso b] :
    IsIso (Prod.mkHom a b) :=
  (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩

private theorem genericSquare_eq
    (ha : conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di = d) :
    genericSquareLeft B₁ B₂ e H F L TX θX γ di = genericSquareRight B₁ e H F L TY TX θY γ d := by
  have : (e.inverse.prod
      e.inverse).IsEquivalence :=
    (e.symm.prod e.symm).isEquivalence_functor
  apply Iso.ext
  apply ((Functor.whiskeringLeft _ _ _).obj
    (e.inverse.prod e.inverse)).map_injective
  ext ⟨M, N⟩
  change (genericSquareLeft B₁ B₂ e H F L TX θX γ di).hom.app
    (e.inverse.obj M, e.inverse.obj N) =
    (genericSquareRight B₁ e H F L TY TX θY γ d).hom.app
      (e.inverse.obj M, e.inverse.obj N)
  let E := e
  let V := TX
  let c := E.counitIso
  let p := L.map ((TY).map (Prod.mkHom (c.inv.app M) (c.inv.app N))) ≫
    L.map ((θY).inv.app (E.inverse.obj M, E.inverse.obj N)) ≫
    (γ).inv.app (B₁.obj (E.inverse.obj M, E.inverse.obj N))
  let z := V.map (Prod.mkHom (L.map (c.hom.app M)) (L.map (c.hom.app N)))
  have : IsIso p := by dsimp [p]; infer_instance
  have : IsIso z := by dsimp [z]; infer_instance
  apply (cancel_epi p).1
  apply (cancel_mono z).1
  have h := NatTrans.congr_app (congrArg Iso.hom ha) (M, N)
  have hl : p ≫ (genericSquareLeft B₁ B₂ e H F L TX θX γ di).hom.app
      (E.inverse.obj M, E.inverse.obj N) ≫ z =
      (conjugatedIso B₁ B₂ e H F L TY TX θY θX γ di).hom.app (M, N) := by
    simp only [p, z, E, V, c, genericSquareLeft, conjugatedIso, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    rfl
  have hr : p ≫ (genericSquareRight B₁ e H F L TY TX θY γ d).hom.app
      (E.inverse.obj M, E.inverse.obj N) ≫ z =
      (d).hom.app (M, N) := by
    dsimp only [p, z, genericSquareRight]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    have hn := (d).hom.naturality
      (Prod.mkHom (c.hom.app M) (c.hom.app N))
    simp only [Functor.map_comp, Category.assoc]
    change L.map ((TY).map (Prod.mkHom (c.hom.app M) (c.hom.app N))) ≫
      (d).hom.app (M, N) =
      (d).hom.app (E.functor.obj (E.inverse.obj M),
        E.functor.obj (E.inverse.obj N)) ≫
      V.map (Prod.mkHom (L.map (c.hom.app M)) (L.map (c.hom.app N))) at hn
    erw [CategoryTheory.Functor.map_id, Category.id_comp, ← hn]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, prod_comp,
      Iso.inv_hom_id_app, ← prod_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using hl.trans (h.trans hr.symm)

private theorem genericSquare_hom
    (h : genericSquareLeft B₁ B₂ e H F L TX θX γ di =
      genericSquareRight B₁ e H F L TY TX θY γ d) (M N : C₁) :
    H.map (di.hom.app (M, N)) ≫ θX.hom.app (F.obj M, F.obj N) ≫
      TX.map (Prod.mkHom (γ.hom.app M) (γ.hom.app N)) =
        γ.hom.app (B₁.obj (M, N)) ≫ L.map (θY.hom.app (M, N)) ≫
          d.hom.app (e.functor.obj M, e.functor.obj N) := by
  exact NatTrans.congr_app (congrArg Iso.hom h) (M, N)

end GenericSquare

private def tensorIsoFromCurried {C D : Type*} [Category C] [Category D]
    (B : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj B ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T) [IsIso δ] :
    Functor.uncurry.obj B ⋙ F ≅ (F.prod F) ⋙ Functor.uncurry.obj T :=
  uncurryPostIso B F ≪≫ Functor.uncurry.mapIso (asIso δ)

private theorem tensorIsoFromCurried_hom {C D : Type*} [Category C] [Category D]
    (B : C ⥤ C ⥤ C) (T : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj B ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T) [IsIso δ] (M N : C) :
    (tensorIsoFromCurried B T F δ).hom.app (M, N) = (δ.app M).app N := by
  simp only [tensorIsoFromCurried, uncurryPostIso, Iso.trans_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp]
  rfl

/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.regularLeft {E : Type*} [Category E] [MonoidalCategory E]
    {U : E} (e : 𝟙_ E ≅ U) (M : E) :=
  (MonoidalCategory.tensor E).map (Prod.mkHom e.inv (𝟙 M)) ≫ (λ_ M).hom

/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.regularRight {E : Type*} [Category E] [MonoidalCategory E]
    {U : E} (e : 𝟙_ E ≅ U) (M : E) :=
  (MonoidalCategory.tensor E).map (Prod.mkHom (𝟙 M) e.inv) ≫ (ρ_ M).hom

section GenericConstraints
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategoryStruct A] [MonoidalCategoryStruct B]
  [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ≅ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B)) (P0 : ObjectProperty A)

/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.input (P Q : A) := L.map (s P Q) ≫ ε.app (P ⊗ Q)
/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.output (P Q : A) :=
  (MonoidalCategory.tensor D).map (Prod.mkHom (ε.app P) (ε.app Q)) ≫
    t (F.obj P) (F.obj Q)
/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.tripleInput (P Q H : A) :=
  L.map ((MonoidalCategory.tensor C).map (Prod.mkHom (s P Q) (𝟙 (q.obj H)))) ≫
    ConstraintData.input F L q r s ε (P ⊗ Q) H
/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.tripleOutput (P Q H : A) :=
  (MonoidalCategory.tensor D).map (Prod.mkHom (ε.app P) (ConstraintData.output F L q r t ε Q H)) ≫
    t (F.obj P) (F.obj Q ⊗ F.obj H)

/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.AssociatorNormalization : Prop :=
  ∀ P Q H : P0.FullSubcategory,
    (L.map
        (@MonoidalCategoryStruct.associator _ _
          (inferInstance : MonoidalCategoryStruct C)
          (q.obj P.obj) (q.obj Q.obj)
          (q.obj H.obj)).hom ≫
      μ (q.obj P.obj)
        ((MonoidalCategory.tensor C).obj (q.obj Q.obj, q.obj H.obj)) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom
        (𝟙 (L.obj (q.obj P.obj)))
        (μ (q.obj Q.obj) (q.obj H.obj))) ≫
      ConstraintData.tripleOutput F L q r t ε P.obj Q.obj H.obj =
      ConstraintData.tripleInput F L q r s ε P.obj Q.obj H.obj ≫ r.map
        (F.map (α_ P.obj Q.obj H.obj).hom ≫
          (β P.obj (Q.obj ⊗ H.obj)).hom ≫
          F.obj P.obj ◁ (β Q.obj H.obj).hom)) ∧
    (μ
        ((MonoidalCategory.tensor C).obj (q.obj P.obj, q.obj Q.obj))
        (q.obj H.obj) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom
        (μ (q.obj P.obj) (q.obj Q.obj))
        (𝟙 (L.obj (q.obj H.obj)))) ≫
      (@MonoidalCategoryStruct.associator _ _
        (inferInstance : MonoidalCategoryStruct D)
        (L.obj (q.obj P.obj))
        (L.obj (q.obj Q.obj))
        (L.obj (q.obj H.obj))).hom ≫
      ConstraintData.tripleOutput F L q r t ε P.obj Q.obj H.obj =
      ConstraintData.tripleInput F L q r s ε P.obj Q.obj H.obj ≫ r.map
        ((β (P.obj ⊗ Q.obj) H.obj).hom ≫
          (β P.obj Q.obj).hom ▷ F.obj H.obj ≫
          (α_ (F.obj P.obj) (F.obj Q.obj)
            (F.obj H.obj)).hom))

/-- Generic representative constraint data, with the specified vertex comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ConstraintData.UnitorNormalization : Prop :=
  ∀ P : P0.FullSubcategory,
    (μ
        (q.obj (𝟙_ A))
        (q.obj P.obj) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom (v)
        (𝟙 (L.obj (q.obj P.obj)))) ≫
      ConstraintData.regularLeft eB (L.obj (q.obj P.obj)) ≫
      ε.app P.obj =
      ConstraintData.input F L q r s ε (𝟙_ A) P.obj ≫
        r.map
          ((β (𝟙_ A) P.obj).hom ≫
            unit ▷ F.obj P.obj ≫
            (λ_ (F.obj P.obj)).hom)) ∧
    (L.map (ConstraintData.regularLeft eA (q.obj P.obj)) ≫
      ε.app P.obj =
      ConstraintData.input F L q r s ε (𝟙_ A) P.obj ≫
        r.map (F.map (λ_ P.obj).hom)) ∧
    (μ (q.obj P.obj)
        (q.obj (𝟙_ A)) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom
        (𝟙 (L.obj (q.obj P.obj))) (v)) ≫
      ConstraintData.regularRight eB (L.obj (q.obj P.obj)) ≫
      ε.app P.obj =
      ConstraintData.input F L q r s ε P.obj (𝟙_ A) ≫
        r.map
          ((β P.obj (𝟙_ A)).hom ≫
            F.obj P.obj ◁ unit ≫
            (ρ_ (F.obj P.obj)).hom)) ∧
    (L.map (ConstraintData.regularRight eA (q.obj P.obj)) ≫
      ε.app P.obj =
      ConstraintData.input F L q r s ε P.obj (𝟙_ A) ≫
        r.map (F.map (ρ_ P.obj).hom))

end GenericConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- Conjugate the actual internal derived arrow by gamma, theta and the fixed counit.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def actualTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (derivedPullback Λ f).obj ((tensor Λ Y).obj (M, N)) ⟶
      (tensor Λ X).obj ((derivedPullback Λ f).obj M, (derivedPullback Λ f).obj N) :=
  (derivedPullback Λ f).map ((tensor Λ Y).map (Prod.mkHom
      ((derivedEquivalence Λ Y).counitIso.inv.app M)
      ((derivedEquivalence Λ Y).counitIso.inv.app N))) ≫
    (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app
      ((derivedEquivalence Λ Y).inverse.obj M, (derivedEquivalence Λ Y).inverse.obj N)) ≫
    (derivedPullComparison Λ f).inv.app
      ((derivedEquivalence Λ Y).inverse.obj M ⊗ (derivedEquivalence Λ Y).inverse.obj N) ≫
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app
      ((derivedEquivalence Λ Y).inverse.obj M)).app
      ((derivedEquivalence Λ Y).inverse.obj N)) ≫
    (tensorComparison Λ X).hom.app
      ((internalDerivedPullback Λ f).obj ((derivedEquivalence Λ Y).inverse.obj M),
        (internalDerivedPullback Λ f).obj ((derivedEquivalence Λ Y).inverse.obj N)) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullComparison Λ f).hom.app ((derivedEquivalence Λ Y).inverse.obj M))
      ((derivedPullComparison Λ f).hom.app ((derivedEquivalence Λ Y).inverse.obj N))) ≫
    (tensor Λ X).map (Prod.mkHom
      ((derivedPullback Λ f).map ((derivedEquivalence Λ Y).counitIso.hom.app M))
      ((derivedPullback Λ f).map ((derivedEquivalence Λ Y).counitIso.hom.app N)))

/-- The prescribed input comparison a: LF(r_Y inverse), followed by epsilon at the total.
Here qTensor is r inverse on resolving representatives, by the fixed K-flat normalization.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def input {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (derivedPullback Λ f).obj
      ((tensor Λ Y).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj (P ⊗ Q)) :=
  (derivedPullback Λ f).map ((qTensor Λ Y).app (P, Q)) ≫
    (pullback Λ f).mapDerivedCategoryFactors.hom.app (P ⊗ Q)

/-- The prescribed output comparison c: epsilon on each factor, followed by r_X inverse.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def output {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    (tensor Λ X).obj ((derivedPullback Λ f).obj (DerivedCategory.Q.obj P),
      (derivedPullback Λ f).obj (DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P ⊗ (totalSectionPull Λ f).obj Q) :=
  (tensor Λ X).map (Prod.mkHom
      ((pullback Λ f).mapDerivedCategoryFactors.hom.app P)
      ((pullback Λ f).mapDerivedCategoryFactors.hom.app Q)) ≫
    (qTensor Λ X).app ((totalSectionPull Λ f).obj P, (totalSectionPull Λ f).obj Q)

/-- The actual derived arrow followed by the prescribed output comparison.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def actualPath {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :=
  actualTensor Λ f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫ output Λ f P Q

/-- The other side of the square, using the fixed ordinary arrow b.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def cochainPath {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :=
  input Λ f P Q ≫ DerivedCategory.Q.map (sectionTotalIso Λ f P Q).hom

/-- The fixed regular-unit comparison e, using kappa and the ordinary unit comparison.
Source: Stacks 06YU, 07A4 (auxiliary; not a blueprint node). -/
def regular (T : Scheme.{u}) :
    tensorUnit Λ T ≅ DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ T) ℤ)) :=
  sectionLocalizationComparison Λ T (𝟙_ (CochainComplex (internalModules Λ T) ℤ)) ≪≫
    DerivedCategory.Q.mapIso (totalUnitComparison Λ T)

/-- The actual derived unit conjugated by gamma and the specified regular-unit maps.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def actualUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj
      (DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ Y) ℤ))) ⟶
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (modules Λ X) ℤ)) :=
  (derivedPullback Λ f).map (regular Λ Y).inv ≫
    (cast (by rfl)
      ((derivedPullComparison Λ f).inv.app (𝟙_ (DerivedCategory (internalModules Λ Y))) ≫
        (derivedEquivalence Λ X).functor.map (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom) :
      (derivedPullback Λ f).obj (tensorUnit Λ Y) ⟶ tensorUnit Λ X) ≫
    (regular Λ X).hom

/-- Naturality of the very square under arbitrary representative maps.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def Naturality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (P Q P' Q' : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory)
    (a : P.obj ⟶ P'.obj) (b : Q.obj ⟶ Q'.obj),
    (derivedPullback Λ f).map ((tensor Λ Y).map
        (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) ≫
        actualPath Λ f P'.obj Q'.obj =
      actualPath Λ f P.obj Q.obj ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b)

/-- Compatibility with inverses in the localized representative categories.
The hypotheses identify the inverse maps by both inverse equations, so no arbitrary
choice of an inverse or extra invertibility assumption is introduced.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def InverseNaturality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (P Q P' Q' : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory)
    (a : P.obj ⟶ P'.obj) (b : Q.obj ⟶ Q'.obj),
    QuasiIso a → QuasiIso b →
    ∀ (s : DerivedCategory.Q.obj P'.obj ⟶ DerivedCategory.Q.obj P.obj)
      (t : DerivedCategory.Q.obj Q'.obj ⟶ DerivedCategory.Q.obj Q.obj)
      (v : DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P'.obj ⊗
          (totalSectionPull Λ f).obj Q'.obj) ⟶
        DerivedCategory.Q.obj ((totalSectionPull Λ f).obj P.obj ⊗
          (totalSectionPull Λ f).obj Q.obj)),
      DerivedCategory.Q.map a ≫ s = 𝟙 _ → s ≫ DerivedCategory.Q.map a = 𝟙 _ →
      DerivedCategory.Q.map b ≫ t = 𝟙 _ → t ≫ DerivedCategory.Q.map b = 𝟙 _ →
      DerivedCategory.Q.map ((totalSectionPull Λ f).map a ⊗ₘ
        (totalSectionPull Λ f).map b) ≫ v = 𝟙 _ →
      v ≫ DerivedCategory.Q.map ((totalSectionPull Λ f).map a ⊗ₘ
        (totalSectionPull Λ f).map b) = 𝟙 _ →
      (derivedPullback Λ f).map ((tensor Λ Y).map (Prod.mkHom s t)) ≫
          actualPath Λ f P.obj Q.obj = actualPath Λ f P'.obj Q'.obj ≫ v

/-- Both actual derived associator paths become exactly the two localized cochain paths.
All intermediate tensor factors are compared using qTensor and epsilon, as in a and c.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def AssociatorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI := transportedDerivedMonoidal Λ X
  letI := transportedDerivedMonoidal Λ Y
  ConstraintData.AssociatorNormalization (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q
    (fun P Q ↦ (qTensor Λ Y).app (P, Q))
    (fun P Q ↦ (qTensor Λ X).app (P, Q))
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (actualTensor Λ f) (KFlatSectionComparison.sectionResolving Λ Y)

/-- Both derived unitor paths reduce through the same a, c and e to the cochain paths.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def UnitorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI := transportedDerivedMonoidal Λ X
  letI := transportedDerivedMonoidal Λ Y
  ConstraintData.UnitorNormalization (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (fun P Q ↦ (qTensor Λ Y).app (P, Q))
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (sectionTotalUnit Λ f) (cast (by rfl) (regular Λ Y)) (cast (by rfl) (regular Λ X))
    (actualTensor Λ f) (actualUnit Λ f) (KFlatSectionComparison.sectionResolving Λ Y)

attribute [local instance 3000] CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000] CondensedRing.projectionModuleAbelian
  CondensedRing.projectionModuleMonoidal CondensedRing.projectionModuleHasDerived
attribute [local instance 5000] CondensedRing.projectionSheafMonoidal
  CondensedRing.projectionCoefficientMonObj CondensedRing.projectionModuleCategory

set_option allowUnsafeReducibility true in
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CondensedRing.upperStar CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapHomologicalComplex

attribute [-instance] compactInternalDerivedCategory in
omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreDerivedCategory (T : Scheme.{u}) :
    Category.{u + 1} (DerivedCategory (internalModules Λ T)) := inferInstance

attribute [local instance 20000] coreDerivedCategory

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreModuleClosed (T : Scheme.{u}) :
    MonoidalClosed (internalModules Λ T) := inferInstance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreModuleBraided (T : Scheme.{u}) :
    BraidedCategory (internalModules Λ T) := inferInstance

attribute [-instance] compactInternalDerivedMonoidal in
omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreDerivedMonoidal (T : Scheme.{u}) :
    MonoidalCategory (DerivedCategory (internalModules Λ T)) := inferInstance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
@[instance_reducible] private def coreDerivedMonoidalStruct (T : Scheme.{u}) :
    MonoidalCategoryStruct (DerivedCategory (internalModules Λ T)) :=
  (coreDerivedMonoidal Λ T).toMonoidalCategoryStruct

attribute [local instance 20000] coreDerivedMonoidalStruct

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreTensorPreservesLeft (T : Scheme.{u}) (M : internalModules Λ T) :
    PreservesColimitsOfShape ℤ ((curriedTensor (internalModules Λ T)).obj M) := by
  infer_instance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreTensorPreservesRight (T : Scheme.{u}) (M : internalModules Λ T) :
    PreservesColimitsOfShape ℤ ((curriedTensor (internalModules Λ T)).flip.obj M) := by
  infer_instance

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem coreModuleFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (internalModules Λ T) := by
  infer_instance

attribute [local instance 20000] coreModuleClosed coreModuleBraided coreModuleFlatResolution
  coreTensorPreservesLeft coreTensorPreservesRight
attribute [local instance 3000] coreDerivedMonoidal

section NativeModels

private def internalTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y) ⋙ internalDerivedPullback Λ f ≅
      ((internalDerivedPullback Λ f).prod (internalDerivedPullback Λ f)) ⋙
        Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem internalTensorIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (internalTensorIso Λ f).hom.app (M, N) = ((internalDelta Λ f).app M).app N := by
  have : IsIso (internalDelta Λ f) := by
    dsimp only [internalDelta]
    infer_instance
  exact tensorIsoFromCurried_hom (CondensedRing.derivedTensor Λ Y)
    (CondensedRing.derivedTensor Λ X) (internalDerivedPullback Λ f) (internalDelta Λ f) M N

private def actualComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ≅
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  conjugatedIso (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f)

private theorem actualComparisonIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (actualComparisonIso Λ f).hom.app (M, N) =
      actualTensor Λ f M N := by
  have h := conjugatedIso_hom (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) M N
  simp only [internalTensorIso_hom] at h
  exact h

private def actualComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ⟶
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X where
  app M := actualTensor Λ f M.1 M.2
  naturality := by
    intro ⟨M, N⟩ ⟨M', N'⟩ a
    simpa only [actualComparisonIso_hom] using
      (actualComparisonIso Λ f).hom.naturality a

attribute [local irreducible] tensorComparison qTensor totalComparison tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  actualTensor actualUnit regular input output actualPath cochainPath
  actualComparisonIso derivedPullComparison
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedFunctorCounit
  internalPullMonoidal CondensedRing.monoidal_upperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

section CoreModels
section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
private abbrev cachedComplexMonoidal : MonoidalCategory (CochainComplex C ℤ) := inferInstance
private abbrev cachedHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private abbrev cachedDerivedMonoidal : MonoidalCategory (DerivedCategory C) := inferInstance
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem tensorator_Q_generic
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ Q) := by
  unfold Functor.LaxMonoidal.μ
  unfold DerivedCategory.laxMonoidalQ
  unfold inferInstance
  unfold DerivedCategory.instLaxMonoidalQ
  unfold Functor.LaxMonoidal.ofIso
  dsimp only
  rw [Functor.LaxMonoidal.comp_μ]
  change (_ ⊗ₘ _) ≫ (_ ≫ (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫ _ = _
  rw [(DerivedCategory.Qh (C := C)).map_id, Category.comp_id]
  rfl

private theorem tensorator_Q_strict {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) := by
  rw [tensorator_Q_generic]
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ _ ≫ 𝟙 _ = _
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

private theorem cochain_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj (P ⊗ Q)) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  erw [tensorator_Q_strict ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q),
    tensorator_Q_strict P Q]
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q
  have hδ := DerivedCategory.quotientCompQhIso_hom_naturality δ
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map δ) ≫ 𝟙 _ =
    𝟙 _ ≫ DerivedCategory.Q.map δ at hδ
  simp only [Category.comp_id, Category.id_comp] at hδ
  have h := G.leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)
  rw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app] at h
  erw [hδ] at h
  exact h

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem ordinaryMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullMonoidal Λ f = CondensedRing.monoidal_upperStar Λ f := by
  apply Functor.Monoidal.toOplaxMonoidal_injective
  unfold internalPullMonoidal
  exact totalInternalOplax_eq Λ f

private theorem delta_model {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDelta Λ f =
      (letI := CondensedRing.monoidal_upperStar Λ f
       (CondensedRing.upperStar Λ f).leftDerivedTensorComparison) := by
  unfold internalDelta
  rw [ordinaryMonoidal_eq Λ f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem internal_pair {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ) :
    ((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B) ≫
      ResolutionConjugation.cInternal Λ f A B =
    ResolutionConjugation.aInternal Λ f A B ≫
      DerivedCategory.Q.map (actualInternalTotalIso Λ f A B).hom := by
  letI := CondensedRing.monoidal_upperStar Λ f
  rw [delta_model, actualInternalTotalIso_hom, totalInternalOplax_eq]
  with_unfolding_all
    simpa only [ResolutionConjugation.cInternal, ResolutionConjugation.aInternal,
      ResolutionConjugation.eta, internalQTensorArrow,
      internalDerivedPullback, internalDerivedPullFunctor,
      internalLocalizationFunctor, comparisonSource, retainedCochainObject, cast_eq,
      Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app, Category.assoc] using
      cochain_tensor_comparison (CondensedRing.upperStar Λ f) A B

end CoreModels
end NativeModels

set_option allowUnsafeReducibility true in
attribute [local irreducible] Functor.Monoidal.toLaxMonoidal
  Functor.Monoidal.toOplaxMonoidal Mod.monoidalCategoryStruct

attribute [local irreducible] tensorComparison qTensor totalComparison tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  actualTensor actualUnit regular input output actualPath cochainPath
  actualComparisonIso derivedPullComparison
  CategoryTheory.Localization.Monoidal.tensorBifunctor
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison
  CategoryTheory.Functor.leftDerivedFunctorCounit
  internalPullMonoidal CondensedRing.monoidal_upperStar

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem actual_conjugation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (internalModules Λ Y)) :
    (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
      (tensorComparison Λ X).hom.app
        ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
      (tensor Λ X).map (Prod.mkHom ((derivedPullComparison Λ f).hom.app M)
        ((derivedPullComparison Λ f).hom.app N)) =
    (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
      (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
      actualTensor Λ f ((derivedEquivalence Λ Y).functor.obj M)
        ((derivedEquivalence Λ Y).functor.obj N) := by
  have h := genericSquare_hom
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ Y))
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (derivedEquivalence Λ Y) (derivedEquivalence Λ X).functor
    (internalDerivedPullback Λ f) (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (tensorComparison Λ Y) (tensorComparison Λ X) (derivedPullComparison Λ f)
    (internalTensorIso Λ f) (actualComparisonIso Λ f)
    (genericSquare_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by unfold actualComparisonIso; rfl)) M N
  simp only [internalTensorIso_hom, actualComparisonIso_hom] at h
  exact h

private theorem actualComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (modules Λ Y)) :
    (actualComparison Λ f).app (M, N) = actualTensor Λ f M N := by
  unfold actualComparison
  rfl

private theorem extend_conjugation
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (S : C × C ⥤ C) (T : D × D ⥤ D)
    (μ : S ⋙ L ⟶ (L.prod L) ⋙ T)
    {A B A' B' P Q R : C} {I O : D}
    (δ : I ⟶ O) (out : O ⟶ T.obj (L.obj A, L.obj B))
    (a : I ⟶ L.obj R) (b : R ⟶ S.obj (A, B))
    (x : A ⟶ A') (y : B ⟶ B') (s : A' ⟶ P) (t : B' ⟶ Q)
    (h : δ ≫ out = a ≫ L.map b ≫ μ.app (A, B)) :
    δ ≫ (out ≫ T.map (Prod.mkHom (L.map x) (L.map y))) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) =
      a ≫ L.map (b ≫ S.map (Prod.mkHom x y)) ≫
        L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) := by
  have h₀ := μ.naturality (Prod.mkHom x y)
  change L.map (S.map (Prod.mkHom x y)) ≫ μ.app (A', B') =
    μ.app (A, B) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) at h₀
  have h₁ := μ.naturality (Prod.mkHom s t)
  change L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) =
    μ.app (A', B') ≫ T.map (Prod.mkHom (L.map s) (L.map t)) at h₁
  have hn : μ.app (A, B) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) =
      L.map (S.map (Prod.mkHom x y)) ≫ L.map (S.map (Prod.mkHom s t)) ≫
        μ.app (P, Q) := by
    rw [← Category.assoc, ← h₀, Category.assoc, ← h₁]
  calc
    _ = (δ ≫ out) ≫ T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) := by simp only [Category.assoc]
    _ = (a ≫ L.map b ≫ μ.app (A, B)) ≫
        T.map (Prod.mkHom (L.map x) (L.map y)) ≫
        T.map (Prod.mkHom (L.map s) (L.map t)) := by rw [h]
    _ = a ≫ L.map b ≫ L.map (S.map (Prod.mkHom x y)) ≫
        L.map (S.map (Prod.mkHom s t)) ≫ μ.app (P, Q) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ a ≫ L.map b ≫ z) hn
    _ = _ := by rw [Functor.map_comp]; simp only [Category.assoc]

private theorem conjugation_on_models {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : CochainComplex (internalModules Λ Y) ℤ)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (σ : (totalSectionEquivalence Λ Y).obj A ≅ P)
    (τ : (totalSectionEquivalence Λ Y).obj B ≅ Q) :
    (derivedEquivalence Λ X).functor.map
        (((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B)) ≫
      ResolutionConjugation.kTensor Λ f A B ≫
      (tensor Λ X).map (Prod.mkHom
        ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
        ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) =
    ResolutionConjugation.jTensor Λ f A B ≫
      (derivedPullback Λ f).map ((tensor Λ Y).map
        (Prod.mkHom (DerivedCategory.Q.map σ.hom) (DerivedCategory.Q.map τ.hom))) ≫
      actualTensor Λ f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) := by
  have h := extend_conjugation (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
    (actualComparison Λ f)
    ((derivedEquivalence Λ X).functor.map
      (((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B)))
    ((tensorComparison Λ X).hom.app
        ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A),
          (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B)) ≫
      (tensor Λ X).map (Prod.mkHom
        ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A))
        ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj B))))
    ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B))
    ((tensorComparison Λ Y).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B))
    (sectionLocalizationComparison Λ Y A).hom (sectionLocalizationComparison Λ Y B).hom
    (DerivedCategory.Q.map σ.hom) (DerivedCategory.Q.map τ.hom)
    (by simpa only [actualComparison_app, Category.assoc] using
      actual_conjugation Λ f (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B))
  with_unfolding_all
    unfold ResolutionConjugation.kTensor ResolutionConjugation.jTensor
      derivedPullSquare cochainLocalizationIso derivedSectionTensorIso
    change
      (derivedEquivalence Λ X).functor.map
          (((internalDelta Λ f).app (DerivedCategory.Q.obj A)).app (DerivedCategory.Q.obj B)) ≫
        ((tensorComparison Λ X).hom.app
            ((internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj A),
              (internalDerivedPullback Λ f).obj (DerivedCategory.Q.obj B)) ≫
          (tensor Λ X).map (Prod.mkHom
            ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A))
            ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj B))) ≫
          (tensor Λ X).map (Prod.mkHom
            ((derivedPullback Λ f).map (sectionLocalizationComparison Λ Y A).hom)
            ((derivedPullback Λ f).map (sectionLocalizationComparison Λ Y B).hom))) ≫
        (tensor Λ X).map (Prod.mkHom
          ((derivedPullback Λ f).map (DerivedCategory.Q.map σ.hom))
          ((derivedPullback Λ f).map (DerivedCategory.Q.map τ.hom))) =
      ((derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj B) ≫
        (derivedPullback Λ f).map
          ((tensorComparison Λ Y).hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
            (tensor Λ Y).map (Prod.mkHom (sectionLocalizationComparison Λ Y A).hom
              (sectionLocalizationComparison Λ Y B).hom))) ≫
        (derivedPullback Λ f).map ((tensor Λ Y).map
          (Prod.mkHom (DerivedCategory.Q.map σ.hom) (DerivedCategory.Q.map τ.hom))) ≫
        actualTensor Λ f (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    simpa only [actualComparison_app, Category.assoc] using h

private theorem transport_square {C : Type*} [Category C]
    {I O Z V S T U W : C}
    (δ : I ⟶ O) (ai : I ⟶ Z) (ci : O ⟶ V) (bi : Z ⟶ V)
    (j : I ⟶ S) (k : O ⟶ T) (dz : Z ⟶ U) (dout : V ⟶ W)
    (a : S ⟶ U) (c : T ⟶ W) (b : U ⟶ W) (μ : S ⟶ T)
    (hd : δ ≫ k = j ≫ μ) (ha : ai ≫ dz = j ≫ a)
    (hc : ci ≫ dout = k ≫ c) (hb : bi ≫ dout = dz ≫ b)
    (hi : δ ≫ ci = ai ≫ bi) : j ≫ μ ≫ c = j ≫ a ≫ b := by
  calc
    j ≫ μ ≫ c = δ ≫ k ≫ c := by rw [← Category.assoc, ← hd, Category.assoc]
    _ = δ ≫ ci ≫ dout := by rw [hc]
    _ = ai ≫ bi ≫ dout := by rw [← Category.assoc, hi, Category.assoc]
    _ = ai ≫ dz ≫ b := by rw [hb]
    _ = j ≫ a ≫ b := by rw [← Category.assoc, ha, Category.assoc]

private theorem transport_square_cancel {C : Type*} [Category C]
    {I O Z V J S K T Z' U V' W : C}
    (δ : I ⟶ O) (ai : I ⟶ Z) (ci : O ⟶ V) (bi : Z ⟶ V)
    (j₁ : I ⟶ J) (j₂ : J ⟶ S) (k₁ : O ⟶ K) (k₂ : K ⟶ T)
    (z₁ : Z ⟶ Z') (z₂ : Z' ⟶ U) (w₁ : V ⟶ V') (w₂ : V' ⟶ W)
    (a : S ⟶ U) (c : T ⟶ W) (b : U ⟶ W) (μ : S ⟶ T)
    [Epi j₁] [Epi j₂]
    (hd : δ ≫ k₁ ≫ k₂ = j₁ ≫ j₂ ≫ μ)
    (ha : ai ≫ z₁ ≫ z₂ = j₁ ≫ j₂ ≫ a)
    (hc : ci ≫ w₁ ≫ w₂ = k₁ ≫ k₂ ≫ c)
    (hb : bi ≫ w₁ ≫ w₂ = z₁ ≫ z₂ ≫ b)
    (hi : δ ≫ ci = ai ≫ bi) : μ ≫ c = a ≫ b := by
  apply (cancel_epi (j₁ ≫ j₂)).1
  have h := transport_square δ ai ci bi (j₁ ≫ j₂) (k₁ ≫ k₂)
    (z₁ ≫ z₂) (w₁ ≫ w₂) a c b μ
    (by simpa only [Category.assoc] using hd)
    (by simpa only [Category.assoc] using ha)
    (by simpa only [Category.assoc] using hc)
    (by simpa only [Category.assoc] using hb) hi
  simpa only [Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_equation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    actualPath Λ f P.obj Q.obj = cochainPath Λ f P.obj Q.obj := by
  let E := (equivalence Λ Y).mapHomologicalComplex (.up ℤ)
  let A := E.inverse.obj P.obj
  let B := E.inverse.obj Q.obj
  let σ := E.counitIso.app P.obj
  let τ := E.counitIso.app Q.obj
  have hs := (ResolutionConjugation.section_resolution_conjugation_identities Λ f).2.2.2.1
    P.obj Q.obj P.property Q.property
  have hsub := hs.2.2
  change ResolutionConjugation.SubstitutionEquations Λ f A B P.obj Q.obj σ τ at hsub
  unfold ResolutionConjugation.SubstitutionEquations at hsub
  obtain ⟨_, ha, hc, hb⟩ := hsub
  have hjT : IsIso (ResolutionConjugation.jTensor Λ f A B) := by
    unfold ResolutionConjugation.jTensor
    infer_instance
  have hδ := conjugation_on_models Λ f A B P.obj Q.obj σ τ
  have hi := congrArg ((derivedEquivalence Λ X).functor.map) (internal_pair Λ f A B)
  simp only [Functor.map_comp] at hi
  have hg := transport_square_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hδ ha hc hb hi
  simp only [actualPath, cochainPath, ResolutionConjugation.aSection,
    ResolutionConjugation.cSection, ResolutionConjugation.epsilon, qTensorArrow,
    input, output] at hg ⊢
  exact hg

private theorem e_eq_regular (T : Scheme.{u}) :
    ResolutionConjugation.e Λ T = (regular Λ T).hom := by
  unfold ResolutionConjugation.e regular
    cochainUnitComparison cochainLocalizationIso
  rfl

private theorem invert_prefix {C : Type*} [Category C] {A B E D : C}
    (a : A ≅ B) (b : B ≅ E) (u : A ⟶ D) (v : E ⟶ D)
    (h : u = a.hom ≫ b.hom ≫ v) : b.inv ≫ a.inv ≫ u = v := by
  rw [h]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_equation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    actualUnit Λ f =
      (pullback Λ f).mapDerivedCategoryFactors.hom.app
          (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map (sectionTotalUnit Λ f) := by
  have h := (ResolutionConjugation.section_resolution_conjugation_identities Λ f).2.1
  have hu := (internal_oplax_resolving_components Λ f).2.2
  with_unfolding_all
    unfold ResolutionConjugation.UnitEquation ResolutionConjugation.eta internalPullUnitArrow
      internalLocalizationFunctor internalCochainUnit at h
    simp only [cast_eq] at h
    simp only [Functor.mapHomotopyCategoryFactors_hom_app, Category.id_comp] at hu
    erw [Category.id_comp] at hu
    erw [← hu] at h
    rw [e_eq_regular Λ X, e_eq_regular Λ Y] at h
    simp only [ResolutionConjugation.epsilon, derivedPullSquare, sectionPullUnitArrow] at h
  unfold actualUnit
  with_unfolding_all
    simp only [cast_eq, Category.assoc]
    exact invert_prefix
      ((derivedPullComparison Λ f).app (𝟙_ (DerivedCategory (internalModules Λ Y))))
      ((derivedPullback Λ f).mapIso (regular Λ Y)) _ _ h

attribute [local semireducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalTensor_map (T : Scheme.{u})
    {P Q P' Q' : CochainComplex (modules Λ T) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (totalTensor Λ T).map (Prod.mkHom a b) = a ⊗ₘ b := by
  change (a ⊗ₘ 𝟙 Q) ≫ (𝟙 P' ⊗ₘ b) = a ⊗ₘ b
  rw [tensorHom_id, id_tensorHom]
  exact (tensorHom_def a b).symm

private theorem generic_path_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
    (TY : C × C ⥤ C) (TX : D × D ⥤ D) (TB : B × B ⥤ B)
    (μ : TY ⋙ L ⟶ (L.prod L) ⋙ TX) (ε : q ⋙ L ⟶ F ⋙ r)
    (t : (r.prod r) ⋙ TX ⟶ TB ⋙ r)
    {P Q P' Q' : A} (a : P ⟶ P') (b : Q ⟶ Q') :
    L.map (TY.map (Prod.mkHom (q.map a) (q.map b))) ≫
        μ.app (q.obj P', q.obj Q') ≫ TX.map (Prod.mkHom (ε.app P') (ε.app Q')) ≫
        t.app (F.obj P', F.obj Q') =
      μ.app (q.obj P, q.obj Q) ≫ TX.map (Prod.mkHom (ε.app P) (ε.app Q)) ≫
        t.app (F.obj P, F.obj Q) ≫ r.map (TB.map (Prod.mkHom (F.map a) (F.map b))) := by
  let τ : (q.prod q) ⋙ TY ⋙ L ⟶ (F.prod F) ⋙ TB ⋙ r :=
    Functor.whiskerLeft (q.prod q) μ ≫
      Functor.whiskerRight (NatTrans.prod ε ε) TX ≫ Functor.whiskerLeft (F.prod F) t
  have h := τ.naturality (Prod.mkHom a b)
  simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, Functor.comp_map, Functor.prod_map,
    Functor.comp_obj, Functor.prod_obj, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem actual_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P Q P' Q' : CochainComplex (modules Λ Y) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (derivedPullback Λ f).map ((tensor Λ Y).map
        (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) ≫
        actualPath Λ f P' Q' =
      actualPath Λ f P Q ≫ DerivedCategory.Q.map
        ((totalSectionPull Λ f).map a ⊗ₘ (totalSectionPull Λ f).map b) := by
  have h := generic_path_naturality (totalSectionPull Λ f) (derivedPullback Λ f)
    DerivedCategory.Q DerivedCategory.Q (tensor Λ Y) (tensor Λ X) (totalTensor Λ X)
    (actualComparison Λ f) (pullback Λ f).mapDerivedCategoryFactors.hom (qTensor Λ X) a b
  simpa only [actualComparison, actualPath, output, totalTensor_map, Category.assoc] using h

private theorem inverse_square {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (s : B ⟶ A) (b : D ⟶ E) (t : E ⟶ D)
    (x : A ⟶ D) (y : B ⟶ E)
    (ha : s ≫ a = 𝟙 B) (hb : b ≫ t = 𝟙 D) (h : a ≫ y = x ≫ b) :
    s ≫ x = y ≫ t := by
  calc
    s ≫ x = s ≫ x ≫ (b ≫ t) := by rw [hb, Category.comp_id]
    _ = s ≫ (a ≫ y) ≫ t := by rw [h]; simp only [Category.assoc]
    _ = y ≫ t := by
      simp only [Category.assoc]
      rw [← Category.assoc s a (y ≫ t), ha, Category.id_comp]

private theorem inverse_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : Naturality Λ f) : InverseNaturality Λ f := by
  intro P Q P' Q' a b _ _ s t v has hsa hbt htb hab hv
  have hi : (Prod.mkHom s t) ≫
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) = 𝟙 _ := by
    ext <;> assumption
  apply inverse_square
    ((derivedPullback Λ f).map ((tensor Λ Y).map
      (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))))
    ((derivedPullback Λ f).map ((tensor Λ Y).map (Prod.mkHom s t)))
    _ v _ _
  · rw [← Functor.map_comp, ← Functor.map_comp, hi,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  · exact hab
  · exact h P Q P' Q' a b

set_option allowUnsafeReducibility true in
attribute [local irreducible] HomologicalComplex.mapBifunctor
  Functor.mapBifunctorHomologicalComplex

attribute [local semireducible] tensor

private theorem constraint_hypotheses {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ResolvingOplaxConstraints.SectionHypotheses Λ f
      (actualComparison Λ f) (actualUnit Λ f) := by
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ X
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ Y
  refine ⟨?_, unit_equation Λ f⟩
  intro P Q
  have hp := pair_equation Λ f P Q
  unfold actualPath cochainPath at hp
  unfold input output at hp
  unfold actualComparison ResolvingOplaxConstraints.modelTensor
    ResolvingOplaxConstraints.pairModel
  exact hp

section GenericConstraints
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
  (F : A ⥤ B) (L : C ⥤ D) (q : A ⥤ C) (r : B ⥤ D)
  (s : ∀ P Q : A, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
  (t : ∀ P Q : B, r.obj P ⊗ r.obj Q ⟶ r.obj (P ⊗ Q))
  (ε : q ⋙ L ⟶ F ⋙ r)
  (β : ∀ P Q : A, F.obj (P ⊗ Q) ≅ F.obj P ⊗ F.obj Q)
  (unit : F.obj (𝟙_ A) ⟶ 𝟙_ B)
  (eA : 𝟙_ C ≅ q.obj (𝟙_ A)) (eB : 𝟙_ D ≅ r.obj (𝟙_ B))
  (μ : ∀ M N : C, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
  (v : L.obj (q.obj (𝟙_ A)) ⟶ r.obj (𝟙_ B)) (P0 : ObjectProperty A)

private theorem GTripleOutput_model (P Q H : A) :
    ConstraintData.tripleOutput F L q r t ε P Q H =
      (ε.app P ⊗ₘ (ε.app Q ⊗ₘ ε.app H)) ≫
        r.obj (F.obj P) ◁ t (F.obj Q) (F.obj H) ≫
        t (F.obj P) (F.obj Q ⊗ F.obj H) := by
  dsimp only [ConstraintData.tripleOutput, ConstraintData.output, MonoidalCategory.tensor]
  rw [← Category.assoc]
  congr 1
  simpa only [Category.comp_id, MonoidalCategory.id_tensorHom, Functor.comp_obj] using
    (MonoidalCategory.tensorHom_comp_tensorHom (ε.app P) (ε.app Q ⊗ₘ ε.app H)
      (𝟙 _) (t (F.obj Q) (F.obj H))).symm

private theorem generic_constraint_normalization
    (ha : ∀ P Q H : P0.FullSubcategory,
      ResolvingOplaxConstraints.AssociativityPaths
        (F := F) (L := L) (q := q) (r := r) (s := s) (t := t) (ε := ε)
        (β := fun P Q ↦ (β P Q).hom) (μ := μ) P.obj Q.obj H.obj)
    (hu : ∀ P : P0.FullSubcategory,
      ResolvingOplaxConstraints.UnitIdentification
        (F := F) (L := L) (q := q) (r := r) (s := s) (t := t) (ε := ε)
        (β := fun P Q ↦ (β P Q).hom) (unit := unit) (eA := eA) (eB := eB)
        (μ := μ) (v := v) P.obj) :
    ConstraintData.AssociatorNormalization F L q r s t ε β μ P0 ∧
      ConstraintData.UnitorNormalization F L q r s ε β unit eA eB μ v P0 := by
  constructor
  · intro P Q H
    obtain ⟨hup, hlo, _⟩ := ha P Q H
    constructor
    · simpa only [ResolvingOplaxConstraints.upperPath,
        ResolvingOplaxConstraints.vertex3, ResolvingOplaxConstraints.rightModel,
        ResolvingOplaxConstraints.vertex0, ResolvingOplaxConstraints.leftModel,
        ConstraintData.tripleInput, ConstraintData.input, GTripleOutput_model,
      MonoidalCategory.tensor,
        MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
        Functor.map_comp, Category.assoc] using hup
    · simpa only [ResolvingOplaxConstraints.lowerPath,
        ResolvingOplaxConstraints.vertex3, ResolvingOplaxConstraints.rightModel,
        ResolvingOplaxConstraints.vertex0, ResolvingOplaxConstraints.leftModel,
        ConstraintData.tripleInput, ConstraintData.input, GTripleOutput_model,
      MonoidalCategory.tensor,
        MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id,
        Functor.map_comp, Category.assoc] using hlo
  · intro P
    obtain ⟨_, _, _, _, _, _, _, hl, hls, _, _, _, _, _, _, _, _, hr, hrs, _⟩ := hu P
    simpa only [ResolvingOplaxConstraints.leftUnitPath,
      ResolvingOplaxConstraints.rightUnitPath, ResolvingOplaxConstraints.regularLeft,
      ResolvingOplaxConstraints.regularRight, ResolvingOplaxConstraints.pairModel,
      ConstraintData.regularLeft, ConstraintData.regularRight, ConstraintData.input,
      MonoidalCategory.tensor,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id, Category.assoc] using
        And.intro hl (And.intro hls (And.intro hr hrs))

end GenericConstraints

private theorem constraint_regular_eq (T : Scheme.{u}) :
    ResolvingOplaxConstraints.regular Λ T = regular Λ T := by
  unfold ResolvingOplaxConstraints.regular regular
  rfl

private theorem constraints_from_hypotheses {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hs : ResolvingOplaxConstraints.SectionHypotheses Λ f
      (actualComparison Λ f) (actualUnit Λ f)) :
    AssociatorNormalization Λ f ∧ UnitorNormalization Λ f := by
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ X
  letI := ResolvingOplaxConstraints.derivedMonoidal Λ Y
  have h := ResolvingOplaxConstraints.section_resolving_oplax_constraint_diagrams Λ f
    (actualComparison Λ f) (actualUnit Λ f) hs
  have hh := generic_constraint_normalization
    (totalSectionPull Λ f) (derivedPullback Λ f) DerivedCategory.Q DerivedCategory.Q
    (ResolvingOplaxConstraints.modelTensor Λ Y)
    (ResolvingOplaxConstraints.modelTensor Λ X)
    (pullback Λ f).mapDerivedCategoryFactors.hom (sectionTotalIso Λ f)
    (sectionTotalUnit Λ f)
    (cast (by rfl) (ResolvingOplaxConstraints.regular Λ Y))
    (cast (by rfl) (ResolvingOplaxConstraints.regular Λ X))
    (fun M N ↦ (actualComparison Λ f).app (M, N)) (actualUnit Λ f)
    (KFlatSectionComparison.sectionResolving Λ Y)
    (fun P Q H ↦ (h.1 P Q H).2.2.2) (fun P ↦ h.2.1 P)
  unfold ResolvingOplaxConstraints.modelTensor at hh
  simpa only [AssociatorNormalization, UnitorNormalization,
    ResolvingOplaxConstraints.derivedMonoidal, ResolvingOplaxConstraints.modelTensor,
    constraint_regular_eq, actualComparison_app] using hh

private theorem constraints {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AssociatorNormalization Λ f ∧ UnitorNormalization Λ f :=
  constraints_from_hypotheses Λ f (constraint_hypotheses Λ f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem input_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    IsIso (input Λ f P.obj Q.obj) := by
  have hq :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, u + 1, u + 1} Λ Y).2.2.2.1.2.1
    P.obj Q.obj (Or.inl P.property.1)
  simp only [input]
  infer_instance

private theorem output_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory) :
    IsIso (output Λ f P.obj Q.obj) := by
  have hi := input_iso Λ f P Q
  have ht : IsIso (actualTensor Λ f (DerivedCategory.Q.obj P.obj)
      (DerivedCategory.Q.obj Q.obj)) := by
    rw [← actualComparisonIso_hom]
    infer_instance
  have he := pair_equation Λ f P Q
  have ho : output Λ f P.obj Q.obj =
      inv (actualTensor Λ f (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)) ≫
        cochainPath Λ f P.obj Q.obj := by
    rw [← he]
    simp only [actualPath, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [ho]
  simp only [cochainPath]
  infer_instance

/-- The actual internal derived arrow satisfies the prescribed resolving square and unit,
with its naturality, inverse-denominator compatibility, and all three constraint diagrams.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E
(auxiliary; not a blueprint node).

Proof, following the five assembly steps of the node.
1. Exactness makes every epsilon invertible. The resolving qTensor is invertible,
   hence so is input. The actual internal tensor arrow and its conjugate are
   isomorphisms; the representative equation then makes output invertible.
2. Apply the internal derived tensor component formula to cochain representatives.
   Normalize the quotient tensor and apply the derived section equivalence.
   The conjugation identities identify both endpoints and the middle total arrow.
   Naturality of the actual conjugate extends the equation through the termwise
   equivalence counits. Cancel the invertible binary input identification.
3. Substitute the internal unit component identity into the unary conjugation
   equation and cancel the comparison isomorphisms.
4. Whisker the natural actual conjugate by the product localization, then compose
   with the tensor of epsilon and qTensor. Naturality of this composite gives
   actualPath naturality, even before restricting to resolving representatives.
   Multiplying this square by the specified inverses gives inverse naturality.
5. Instantiate the resolving constraint theorem with the actual conjugate and
   unit. The pair and unit formulas supply its hypotheses. Convert the transported
   tensor maps to tensor notation and normalize composition to obtain exactly the
   two associator paths and the four unitor paths in the statement.
-/
theorem section_derived_representative_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ P Q : (KFlatSectionComparison.sectionResolving Λ Y).FullSubcategory,
      IsIso (input Λ f P.obj Q.obj) ∧ IsIso (output Λ f P.obj Q.obj) ∧
        actualPath Λ f P.obj Q.obj = cochainPath Λ f P.obj Q.obj) ∧
    Naturality Λ f ∧ InverseNaturality Λ f ∧
    (actualUnit Λ f =
      (pullback Λ f).mapDerivedCategoryFactors.hom.app
          (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
        DerivedCategory.Q.map (sectionTotalUnit Λ f)) ∧
    AssociatorNormalization Λ f ∧ UnitorNormalization Λ f := by
  have hn : Naturality Λ f := by
    intro P Q P' Q' a b
    exact actual_naturality Λ f a b
  exact ⟨fun P Q ↦ ⟨input_iso Λ f P Q, output_iso Λ f P Q, pair_equation Λ f P Q⟩,
    hn, inverse_naturality Λ f hn, unit_equation Λ f,
    (constraints Λ f).1, (constraints Λ f).2⟩

end DerivedRepresentativeSquare
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
