/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomDiagram
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain

/-! # KoszulScalarHomNaturality for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-hom-naturality).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private theorem homDiagramComparison_natural (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    {N M : ringedSiteComplex B} (f : N ⟶ M) (m : ℕᵒᵖ) :
    (restrictComplex φ).map
        (((homComplexFunctor (R := B)).obj
          (op ((ringedKoszulDiagram B r (imageSections φ a)).obj m.unop))).map f) ≫
        (homDiagramComparison φ r a e M).hom.app m =
      (homDiagramComparison φ r a e N).hom.app m ≫
        ((homComplexFunctor (R := R)).obj
          (op ((ringedKoszulDiagram R r a).obj m.unop))).map
          ((restrictComplex φ).map f) := by
  have ht := (SheafOfModules.StrictScalarHom.canonicalData.{u, u, u} φ).theta_natural
    ((ringedKoszulDiagram R r a).obj m.unop)
    ((ringedKoszulDiagram R r a).obj m.unop) N M (𝟙 _) f
  simp only [SheafOfModules.StrictScalarHom.homMap, Functor.map_id,
    op_id, NatTrans.id_app] at ht
  erw [Category.id_comp, Category.id_comp] at ht
  exact naturalityCompositionCore (restrictComplex φ) _ _ _ _ _ _ _
    (((homComplexFunctor (R := B)).map (e.hom.app m.unop).op).naturality f) ht

private theorem tensorDiagramComparison_natural (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    {N M : ringedSiteComplex B} (f : N ⟶ M) (m : ℕᵒᵖ) :
    (restrictComplex φ).map
        (((ringedKoszulTensorTower B r (imageSections φ a)).map f).app m) ≫
        (tensorDiagramComparison φ r a e M).hom.app m =
      (tensorDiagramComparison φ r a e N).hom.app m ≫
        ((ringedKoszulTensorTower R r a).map ((restrictComplex φ).map f)).app m := by
  have hr :
      ((ringedKoszulTensorTower R r a).map ((restrictComplex φ).map f)).app m ≫
          (koszulEvaluation R r a ((restrictComplex φ).obj M)).hom.app m =
        (koszulEvaluation R r a ((restrictComplex φ).obj N)).hom.app m ≫
          ((homComplexFunctor (R := R)).obj
            (op ((ringedKoszulDiagram R r a).obj m.unop))).map
            ((restrictComplex φ).map f) :=
    ringedComplexTensorEvaluation_naturality R _ ((restrictComplex φ).map f)
  have hb :
      ((ringedKoszulTensorTower B r (imageSections φ a)).map f).app m ≫
          (koszulEvaluation B r (imageSections φ a) M).hom.app m =
        (koszulEvaluation B r (imageSections φ a) N).hom.app m ≫
          ((homComplexFunctor (R := B)).obj
            (op ((ringedKoszulDiagram B r (imageSections φ a)).obj m.unop))).map f :=
    ringedComplexTensorEvaluation_naturality B _ f
  apply (cancel_mono ((koszulEvaluation R r a ((restrictComplex φ).obj M)).hom.app m)).mp
  simp only [tensorDiagramComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hr, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, hb, Functor.map_comp]
  simp only [Category.assoc]
  rw [homDiagramComparison_natural]

/-- Assemble degreewise tower isomorphisms compatible with structure maps and differentials.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-hom-naturality). -/
def componentNatIso
    {C I D : Type*} [Category C] [Category I] [Category D] [HasZeroMorphisms D]
    (A B : C ⥤ CochainComplex (I ⥤ D) ℤ)
    (e : ∀ (N : C) (m : I) (n : ℤ), ((A.obj N).X n).obj m ≅ ((B.obj N).X n).obj m)
    (hm : ∀ (N : C) (n : ℤ) {m k : I} (f : m ⟶ k),
      ((A.obj N).X n).map f ≫ (e N k n).hom =
        (e N m n).hom ≫ ((B.obj N).X n).map f)
    (hd : ∀ (N : C) (n k : ℤ) (_h : (ComplexShape.up ℤ).Rel n k) (m : I),
      ((A.obj N).d n k).app m ≫ (e N m k).hom =
        (e N m n).hom ≫ ((B.obj N).d n k).app m)
    (hn : ∀ {N M : C} (f : N ⟶ M) (n : ℤ) (m : I),
      ((A.map f).f n).app m ≫ (e M m n).hom =
        (e N m n).hom ≫ ((B.map f).f n).app m) : A ≅ B := by
  refine NatIso.ofComponents (fun N ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ NatIso.ofComponents (fun m ↦ e N m n) (hm N n)) ?_) ?_
  · intro n k h
    apply NatTrans.ext
    funext m
    exact (hd N n k h m).symm
  · intro N M f
    apply HomologicalComplex.hom_ext
    intro n
    apply NatTrans.ext
    funext m
    exact hn f n m

/-- Naturality and transposition of the strict Koszul comparison.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Use target naturality of theta and functoriality of precomposition to show
homDiagramComparison is natural in the coefficient complex. Cancel R evaluation and apply its
target naturality to transfer this identity to tensorDiagramComparison.
Proof step 2: Construct the isomorphism degree by degree using componentNatIso. Naturality in the
tower variable is the diagram isomorphism naturality; differential compatibility is its component
cochain-map identity; coefficient naturality is step 1. These establish all naturality and
cochain conditions of the transposed natural isomorphism.
(blueprint: lem-f5-koszul-scalar-hom-naturality). -/
private def strictComparisonFromPositive (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a)) :
    ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙ restrictTowerComplex φ ≅
      restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a := by
  refine componentNatIso _ _
    (fun N m n ↦ HomologicalComplex.Hom.isoApp
      ((tensorDiagramComparison φ r a e N).app m) n) ?_ ?_ ?_
  · intro N n m k f
    exact congrArg (fun g ↦ g.f n) ((tensorDiagramComparison φ r a e N).hom.naturality f)
  · intro N n k h m
    have hk : n + 1 = k := h
    subst k
    simpa only [ringedKoszulTensorTowerFunctor, ringedKoszulTensorTowerComplex,
      CochainComplex.of_d, NatTrans.comp_app, NatIso.ofComponents_hom_app,
      HomologicalComplex.Hom.isoApp_hom, Functor.comp_obj,
      Functor.mapHomologicalComplex_obj_d, Functor.whiskerLeft_app,
      HomologicalComplex.dNatTrans_app, Functor.whiskerRight_app] using!
      (((tensorDiagramComparison φ r a e N).hom.app m).comm
        n (n + 1)).symm
  · intro N M f n m
    exact congrArg (fun g ↦ g.f n) (tensorDiagramComparison_natural φ r a e f m)

end CategoryTheory.FlatScalarKoszul
