/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFiniteExtend
/-! # Clearing denominators between integral constructible images

The coefficient telescope is tensored with a complex representing the target. Its colimit
is the restriction of ordinary scalar extension, and the zeroth leg is the adjunction unit.
Sequential Hom continuity then supplies a finite-stage lift of the adjoint of a rational map.
-/

@[expose] public section
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
set_option backward.isDefEq.respectTransparency false in
private noncomputable def extendComapTensorIso (M : Mod C R) :
    (comap φ).obj ((extendScalars φ).obj M) ≅ (comap φ).obj (regular S) ⊗ M :=
  isoMk (extendForgetTensorObjIso φ M) (by
    apply (cancel_epi (R ◁ extendπ φ M)).1
    change (R ◁ extendπ φ M) ≫ γ[R,((comap φ).obj
        (extendScalarsObj φ M)).X] ≫ (extendForgetTensorObjIso φ M).hom =
      (R ◁ extendπ φ M) ≫ R ◁ (extendForgetTensorObjIso φ M).hom ≫
        γ[R,((comap φ).obj (regular S) ⊗ M).X]
    rw [comap_obj_smul]
    simp only [Category.assoc]
    erw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
      ← whiskerLeft_comp_assoc, extendπ_extendDescHom]
    erw [whiskerLeft_tensorπ_smul]
    erw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
    rfl)
private noncomputable def extendComapTensorNatIso :
    extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents (extendComapTensorIso φ) (by
    intro M N f
    apply hom_ext
    exact (extendForgetTensorIso φ).hom.naturality f)

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
set_option backward.isDefEq.respectTransparency false in
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem extendUnit_tensor (M : Mod C R)
    (a : regular R ⟶ (comap φ).obj (regular S)) (ha : a.hom = φ) :
    extendUnit φ M ≫ (extendComapTensorIso φ M).hom = (λ_ M).inv ≫ a ▷ M := by
  apply hom_ext
  change extendUnitHom φ M ≫ (extendForgetTensorObjIso φ M).hom =
    (λ_ M).inv.hom ≫ (a ▷ M).hom
  rw [Mod.leftUnitor_inv_hom_eq]
  simp only [Category.assoc, tensorObjπ_whiskerRight, ha]
  erw [← comp_whiskerRight_assoc, IsMonHom.one_hom (f := φ)]
  dsimp only [extendUnitHom, extendForgetTensorObjIso]
  rw [Category.assoc, Category.assoc, extendπ_extendDescHom]
end CategoryTheory.Mod

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
private noncomputable def tensorComplex (K : CochainComplex C ℤ) :
    C ⥤ CochainComplex C ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex _).obj K
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor C).map f) _).app K
  map_id M := by ext n; simp
  map_comp f g := by ext n; simp

private instance tensorComplex_additive (K : CochainComplex C ℤ) :
    (tensorComplex K).Additive where
  map_add := by
    intro M N f g
    ext n
    exact (tensorRight (K.X n)).map_add

private instance tensorComplex_preservesColimitsOfShape {J : Type*} [Category J]
    [∀ M : C, PreservesColimitsOfShape J (tensorRight M)] (K : CochainComplex C ℤ) :
    PreservesColimitsOfShape J (tensorComplex K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  exact inferInstanceAs (PreservesColimitsOfShape J (tensorRight (K.X n)))

private noncomputable def tensorComplex_unitIso (K : CochainComplex C ℤ) :
    (tensorComplex K).obj (𝟙_ C) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ λ_ (K.X n)) (by
    intro i j hij
    exact (leftUnitor_naturality (K.d i j)).symm)
end CategoryTheory

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [Abelian.HasFunctorialFlatResolution C] in
private theorem tensorComplex_extendUnit (K : CochainComplex (Mod C R) ℤ)
    (a : regular R ⟶ (comap φ).obj (regular S)) (ha : a.hom = φ) :
    (tensorComplex_unitIso K).inv ≫ (tensorComplex K).map a ≫
      ((NatIso.mapHomologicalComplex (extendComapTensorNatIso φ)
        (.up ℤ)).app K).inv =
      ((extendRestrictAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app K := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [tensorComplex_unitIso, tensorComplex,
    NatIso.mapHomologicalComplex, extendComapTensorNatIso]
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_inv_f, NatTrans.mapHomologicalComplex_app_f,
    Iso.app_inv, NatIso.ofComponents_inv_app, Adjunction.mapHomologicalComplex_unit_app_f]
  simp only [curriedTensor_map_app]
  change (λ_ (K.X n)).inv ≫ a ▷ K.X n ≫
    (extendComapTensorIso φ (K.X n)).inv =
      extendUnit φ (K.X n) ≫ (comap φ).map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply (cancel_mono (extendComapTensorIso φ (K.X n)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (extendUnit_tensor φ (K.X n) a ha).symm
end CategoryTheory.Mod

private theorem clearDenominator_of_cocone
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (ℓ : ℕ) (A B : C) (N : ℕ ⥤ C) (c : Cocone N)
    (e : ∀ n, N.obj n ≅ B) (p : c.pt ≅ G.obj (F.obj B))
    (hzero : (e 0).inv ≫ c.ι.app 0 ≫ p.hom = adj.unit.app B)
    (hpow : ∀ n : ℕ, ℓ ^ n • ((e n).inv ≫ c.ι.app n) = (e 0).inv ≫ c.ι.app 0)
    (hfactor : ∀ f : A ⟶ c.pt, ∃ (n : ℕ) (g : A ⟶ N.obj n), g ≫ c.ι.app n = f)
    (f : F.obj A ⟶ F.obj B) :
    ∃ (n : ℕ) (g : A ⟶ B), ℓ ^ n • f = F.map g := by
  obtain ⟨n, g, hg⟩ := hfactor ((adj.homEquiv A _ f) ≫ p.inv)
  let u : A ⟶ B := g ≫ (e n).hom
  have hclear : ℓ ^ n • (adj.homEquiv A _ f) = u ≫ adj.unit.app B := by
    apply (cancel_mono p.inv).1
    rw [Preadditive.nsmul_comp, ← hg, ← hzero]
    simp only [u, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← hpow n]
    simp only [Preadditive.comp_nsmul, Iso.hom_inv_id_assoc]
  refine ⟨n, u, (adj.homEquiv A _).injective ?_⟩
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_nsmul,
    Preadditive.comp_nsmul]
  have hu := adj.unit.naturality u
  change u ≫ adj.unit.app B = adj.unit.app A ≫ G.map (F.map u) at hu
  simpa only [Adjunction.homEquiv_unit, Preadditive.nsmul_comp] using hclear.trans hu

private theorem exists_exact_derived_adjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adjC : F.mapHomologicalComplex (.up ℤ) ⊣ G.mapHomologicalComplex (.up ℤ)) :
    ∃ adj : F.mapDerivedCategory ⊣ G.mapDerivedCategory,
      ∀ K : CochainComplex C ℤ,
        adj.unit.app (DerivedCategory.Q.obj K) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.app K).hom ≫
            (G.mapDerivedCategoryFactors.app
              ((F.mapHomologicalComplex (.up ℤ)).obj K)).hom =
        DerivedCategory.Q.map (adjC.unit.app K) := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  let adj := adjC.localization DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory
  refine ⟨adj, fun K ↦ ?_⟩
  dsimp only [adj]
  rw [Adjunction.localization_unit_app]
  simp only [Category.assoc]
  change DerivedCategory.Q.map (adjC.unit.app K) ≫
    (G.mapDerivedCategoryFactors.app _).inv ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.app K).inv ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.app K).hom ≫
          (G.mapDerivedCategoryFactors.app _).hom = _
  rw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem denominator_transfer
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F F' : C ⥤ D) [F'.Additive] (eF : F ≅ F')
    (ℓ : ℕ) (A B Z : C) (eB : Z ≅ B) (f : F.obj A ⟶ F.obj B)
    (hden : ∃ (n : ℕ) (g : A ⟶ Z),
      ℓ ^ n • (((eF.app A).inv ≫ f ≫ (eF.app B).hom) ≫ F'.map eB.inv) = F'.map g) :
    ∃ (n : ℕ) (g : A ⟶ B), ℓ ^ n • f = F.map g := by
  obtain ⟨n, g, hg⟩ := hden
  let f' := (eF.app A).inv ≫ f ≫ (eF.app B).hom
  have hF : ℓ ^ n • f' = F'.map (g ≫ eB.hom) := by
    apply (cancel_mono (F'.map eB.inv)).1
    rw [Preadditive.nsmul_comp]
    rw [show ℓ ^ n • (f' ≫ F'.map eB.inv) = F'.map g from hg, ← F'.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨n, g ≫ eB.hom, ?_⟩
  have h := congrArg (fun v ↦ (eF.app A).hom ≫ v ≫ (eF.app B).inv) hF
  simp only [f', Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
  simp only [Iso.app_hom, Iso.app_inv] at h
  rw [← eF.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id] at h
  exact h

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
set_option backward.isDefEq.respectTransparency false in
/-- Multiplying a rational derived morphism by a power of ℓ gives an integral morphism.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)

Proof. Tensor the coefficient localization telescope with a complex representing B.
Tensor preserves the colimit. Extension followed by restriction is tensor with the
restricted rational regular module; the normalized zeroth leg is its adjunction unit.
Every stage is isomorphic to B and therefore has the same cohomological lower bound.
Sequential Hom continuity factors the adjoint of the given rational morphism through
one stage. Multiplication by the corresponding power of ℓ takes this leg to the zeroth
leg. Naturality and injectivity of the adjunction bijection yield an integral lift.
Finally transport along the representative of B and the canonical isomorphism between
the left derived functor and the derived functor of exact scalar extension. -/
theorem continuousConstructible_clear_denominators (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (A B : integralConstructible ℓ E X)
    (f : (integralScalarExtension ℓ E X).obj A.obj ⟶
      (integralScalarExtension ℓ E X).obj B.obj) :
    ∃ (n : ℕ) (g : A ⟶ B),
      ℓ ^ n • f = (integralScalarExtension ℓ E X).map g.hom := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let ψ : R ⟶ S := coefficientMap (integralScalarMap ℓ E) X
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S := Mod.extendScalars ψ
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R := Mod.comap ψ
  let : F.Additive := inferInstance
  let : G.Additive := inferInstance
  let : PreservesFiniteLimits F := inferInstance
  let : PreservesFiniteColimits F := inferInstance
  let : PreservesFiniteLimits G := inferInstance
  let : PreservesFiniteColimits G := inferInstance
  obtain ⟨D, c, e, p, ⟨hc⟩, hpow, hzero⟩ := integralCoefficient_localization_telescope ℓ E X
  let K := DerivedCategory.Q.objPreimage B.obj
  let eB : DerivedCategory.Q.obj K ≅ B.obj := DerivedCategory.Q.objObjPreimageIso B.obj
  let H := tensorComplex K
  let t := H.mapCocone c
  have ht : IsColimit t := isColimitOfPreserves H hc
  let et : t.pt ≅ ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K :=
    H.mapIso p ≪≫ ((NatIso.mapHomologicalComplex (Mod.extendComapTensorNatIso ψ)
      (.up ℤ)).app K).symm
  let es (n : ℕ) : (D ⋙ H).obj n ≅ K := H.mapIso (e n) ≪≫ tensorComplex_unitIso K
  have hlegs (n : ℕ) : ℓ ^ n • ((es n).inv ≫ t.ι.app n) =
      (es 0).inv ≫ t.ι.app 0 := by
    dsimp only [es, t, Iso.trans_inv, Functor.mapIso_inv, Functor.mapCocone_ι_app]
    simp only [Category.assoc, ← H.map_comp, ← CategoryTheory.Functor.map_nsmul,
      ← Preadditive.comp_nsmul, hpow]
  have hunit : (es 0).inv ≫ t.ι.app 0 ≫ et.hom =
      ((Mod.extendRestrictAdjunction ψ).mapHomologicalComplex (.up ℤ)).unit.app K := by
    dsimp only [es, et, t, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom, Functor.mapCocone_ι_app]
    simp only [Category.assoc]
    rw [← H.map_comp_assoc, ← H.map_comp_assoc]
    exact Mod.tensorComplex_extendUnit ψ K _ hzero
  let FD := F.mapDerivedCategory
  let GD := G.mapDerivedCategory
  let adjC := (Mod.extendRestrictAdjunction ψ).mapHomologicalComplex (.up ℤ)
  obtain ⟨adj, hadj⟩ := exists_exact_derived_adjunction F G adjC
  let ec : GD.obj (FD.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) :=
    GD.mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
      G.mapDerivedCategoryFactors.app (((F.mapHomologicalComplex (.up ℤ)).obj K))
  have hunitQ : adj.unit.app (DerivedCategory.Q.obj K) ≫ ec.hom =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction ψ).mapHomologicalComplex (.up ℤ)).unit.app K) := by
    simpa only [ec, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hadj K
  let eF := F.leftDerivedFunctorIsoMapDerivedCategory
  let f' : FD.obj A.obj ⟶ FD.obj B.obj := (eF.app A.obj).inv ≫ f ≫ (eF.app B.obj).hom
  let fK := f' ≫ FD.map eB.inv
  obtain ⟨a, ha⟩ := B.property.1.1
  have hD : ∃ a : ℤ, ∀ n : ℕ, (DerivedCategory.Q.obj ((D ⋙ H).obj n)).IsGE a := by
    refine ⟨a, fun n ↦ ?_⟩
    have : B.obj.IsGE a := ha
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (DerivedCategory.Q.mapIso (es n) ≪≫ eB).symm a
  have hfactor : ∀ v : A.obj ⟶ DerivedCategory.Q.obj t.pt,
      ∃ (n : ℕ) (g : A.obj ⟶ DerivedCategory.Q.obj ((D ⋙ H).obj n)),
        g ≫ DerivedCategory.Q.map (t.ι.app n) = v := fun v ↦
    integralConstructible_hom_sequential_colimit ℓ E X A (D ⋙ H) t ⟨ht⟩ hD v
  let pD : DerivedCategory.Q.obj t.pt ≅ GD.obj (FD.obj (DerivedCategory.Q.obj K)) :=
    DerivedCategory.Q.mapIso et ≪≫ ec.symm
  have hzD : (DerivedCategory.Q.mapIso (es 0)).inv ≫
      DerivedCategory.Q.map (t.ι.app 0) ≫ pD.hom = adj.unit.app (DerivedCategory.Q.obj K) := by
    apply (cancel_mono ec.hom).1
    simp only [pD, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Functor.mapIso_inv, Functor.mapIso_hom]
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hunit]
    exact hunitQ.symm
  have hpD (n : ℕ) : ℓ ^ n • ((DerivedCategory.Q.mapIso (es n)).inv ≫
      DerivedCategory.Q.map (t.ι.app n)) = (DerivedCategory.Q.mapIso (es 0)).inv ≫
      DerivedCategory.Q.map (t.ι.app 0) := by
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_comp,
      Functor.mapIso_inv] using congrArg DerivedCategory.Q.map (hlegs n)
  obtain ⟨n, g, hg⟩ := denominator_transfer (integralScalarExtension ℓ E X) FD eF ℓ
    A.obj B.obj (DerivedCategory.Q.obj K) eB f
      (clearDenominator_of_cocone FD GD adj ℓ A.obj (DerivedCategory.Q.obj K)
        ((D ⋙ H) ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone t)
          (fun n ↦ DerivedCategory.Q.mapIso (es n)) pD hzD hpD hfactor fK)
  exact ⟨n, ObjectProperty.homMk g, hg⟩
end AlgebraicGeometry.ProEtale.CondensedRing
