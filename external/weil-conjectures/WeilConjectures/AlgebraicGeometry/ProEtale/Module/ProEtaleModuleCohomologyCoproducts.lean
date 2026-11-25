/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.ComplexExtensionColimits
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverComputesBoundedComplexSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Higher direct images of pro-etale module sheaves commute with sums

The private helpers implement the hypercover calculation and exact evaluation test.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex₂
open AlgebraicGeometry AlgebraicGeometry.Scheme.ProEt
open scoped Simplicial
universe u v w z s u' v'
noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
private theorem alternating_preservesCoproducts (C : Type u) [Category.{v} C] [Preadditive C]
    (I : Type s) [HasCoproducts.{s} C] :
    PreservesColimitsOfShape (Discrete I) (AlgebraicTopology.alternatingCofaceMapComplex C) := by
  constructor
  intro K
  have : HasColimitsOfShape (Discrete I) (CosimplicialObject C) := by
    unfold CosimplicialObject
    infer_instance
  let F := AlgebraicTopology.alternatingCofaceMapComplex C
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro n
  change IsColimit (((CategoryTheory.evaluation SimplexCategory C).obj
    (SimplexCategory.mk n)).mapCocone (colimit.cocone K))
  exact isColimitOfPreserves _ (colimit.isColimit K)

private def total_coproduct_isColimit {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{0} C] [HasCoproducts.{s} C]
    (I : Type s) (E : I → HomologicalComplex₂ C (.up ℤ) (.up ℤ)) :
    IsColimit (Cofan.mk ((∐ E).total (.up ℤ))
      (fun i ↦ total.map (Sigma.ι E i) (.up ℤ))) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  let c := ComplexShape.up ℤ
  have heval (p q : ℤ) : IsColimit
      (Cofan.mk (((∐ E).X p).X q) (fun i ↦ ((Sigma.ι E i).f p).f q)) :=
    (isColimitMapCoconeCofanMkEquiv
      (HomologicalComplex.eval _ c p ⋙ HomologicalComplex.eval C c q) E _).1
      (isColimitOfPreserves _ (coproductIsCoproduct E))
  apply (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval C c n)
    (fun i ↦ (E i).total c) (fun i ↦ total.map (Sigma.ι E i) c)).2
  refine Cofan.IsColimit.mk _ (fun t ↦ (∐ E).totalDesc
    (fun p q h ↦ (heval p q).desc
      (Cofan.mk t.pt (fun i ↦ (E i).ιTotal c p q n h ≫ t.inj i)))) ?_ ?_
  · intro t i
    apply total.hom_ext
    intro p q h
    dsimp only [cofan_mk_inj, HomologicalComplex.eval]
    rw [ιTotal_map_assoc, ι_totalDesc]
    exact (heval p q).fac _ ⟨i⟩
  · intro t m hm
    apply total.hom_ext
    intro p q h
    rw [ι_totalDesc]
    apply (heval p q).hom_ext
    intro i
    dsimp
    erw [(heval p q).fac]
    have hi := congrArg (fun f ↦ (E i.as).ιTotal c p q n h ≫ f) (hm i.as)
    simpa only [cofan_mk_inj, HomologicalComplex.eval_map, Cofan.mk_ι_app,
      ← Category.assoc, ιTotal_map] using hi

private theorem hypercover_sections_preservesCoproducts (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W))
    (haff : ∀ n : ℕ, IsAffine (U _⦋n⦌).left.left)
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (hypercoverSections X R W U) := by
  refine preservesColimitsOfShape_of_evaluation
    (hypercoverSections X R W U) (Discrete I) ?_
  intro n
  let R' := (sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have : IsAffine (U.obj (op n)).left.left := haff n.len
  have hweak' : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U.obj (op n)).left)) := hweak n.len
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.evaluation.{u + 1} R' (op (U.obj (op n)).left)) :=
    (affine_weaklyContractible_evaluation_colimits X R (U.obj (op n)).left hweak').2.2.1
  let ev := (CategoryTheory.evaluation SimplexCategory
    (ModuleCat.{u + 1} (R'.obj.obj (op W)))).obj n
  let G :=
    forget₂ (ModuleCat.{u + 1} (R'.obj.obj (op W))) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfShape (Discrete I) ((hypercoverSections X R W U ⋙ ev) ⋙ G) := by
    change PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.evaluation.{u + 1} R' (op (U.obj (op n)).left) ⋙
        forget₂ (ModuleCat.{u + 1} (R'.obj.obj (op (U.obj (op n)).left))) AddCommGrpCat.{u + 1})
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _ G

private theorem total_preservesCoproducts {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{0} C] [HasCoproducts.{s} C] (I : Type s) :
    PreservesColimitsOfShape (Discrete I)
      (totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)) := by
  constructor
  intro K
  let E : I → HomologicalComplex₂ C (.up ℤ) (.up ℤ) := fun i ↦ K.obj ⟨i⟩
  have he : Discrete.functor E ≅ K := Discrete.natIso (fun _ ↦ Iso.refl _)
  have : PreservesColimit (Discrete.functor E)
      (totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)) := by
    apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct E)
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).2
    exact total_coproduct_isColimit I E
  exact preservesColimit_of_iso_diagram _ he

private theorem flip_preservesCoproducts {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{s} C] (I : Type s) :
    PreservesColimitsOfShape (Discrete I)
      (flipFunctor C (.up ℤ) (.up ℤ)) := by
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply HomologicalComplex.isColimitOfEval
  intro p
  apply HomologicalComplex.isColimitOfEval
  intro q
  exact isColimitOfPreserves
    (HomologicalComplex.eval _ (.up ℤ) q ⋙ HomologicalComplex.eval C (.up ℤ) p)
    (colimit.isColimit K)

private theorem hypercover_total_preservesCoproducts (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) (U : SimplicialObject (Over W))
    (haff : ∀ n : ℕ, IsAffine (U _⦋n⦌).left.left)
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (hypercoverTotal X R W U) := by
  have := hypercover_sections_preservesCoproducts X R W U haff hweak I
  have := alternating_preservesCoproducts
    (ModuleCat.{u + 1} (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) I
  have := extension_preservesColimits ComplexShape.embeddingUpNat (Discrete I)
    (C := ModuleCat.{u + 1} (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))
  have : PreservesColimitsOfShape (Discrete I) (hypercoverSectionRows X R W U) := by
    unfold hypercoverSectionRows
    infer_instance
  have := flip_preservesCoproducts (C := ModuleCat.{u + 1}
    (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) I
  have := total_preservesCoproducts (C := ModuleCat.{u + 1}
    (((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) I
  unfold hypercoverTotal
  infer_instance
private def resolutionHomologyComparison {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (A : C ⥤ CochainComplex D ℤ) (q : ℕ)
    (c : ∀ X : C, (A.obj X).homology q ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj (injectiveResolution X).cochainComplex).homology q)
    (hc : ∀ {X Y : C} (f : X ⟶ Y)
      (φ : (injectiveResolution X).Hom (injectiveResolution Y) f),
      HomologicalComplex.homologyMap (A.map f) q ≫ (c Y).hom =
        (c X).hom ≫ HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex _).map φ.hom') q) :
    A ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) (q : ℤ) ≅ F.rightDerived q := by
  refine NatIso.ofComponents (fun X ↦ c X ≪≫
    ((injectiveResolution X).isoRightDerivedObjCochainComplex F q).symm) ?_
  intro X Y f
  let φ : (injectiveResolution X).Hom (injectiveResolution Y) f :=
    ⟨InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X),
      by simp⟩
  change HomologicalComplex.homologyMap (A.map f) q ≫
      ((c Y).hom ≫ ((injectiveResolution Y).isoRightDerivedObjCochainComplex F q).inv) =
    ((c X).hom ≫ ((injectiveResolution X).isoRightDerivedObjCochainComplex F q).inv) ≫
      (F.rightDerived q).map f
  rw [← Category.assoc, hc f φ, Category.assoc,
    InjectiveResolution.isoRightDerivedObjCochainComplex_inv_naturality, Category.assoc]

private def derivedToHomologyComparison {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (A : C ⥤ CochainComplex D ℤ) (q : ℕ)
    (c : ∀ X : C, DerivedCategory.Q.obj (A.obj X) ≅
      DerivedCategory.Q.obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (injectiveResolution X).cochainComplex))
    (hc : ∀ {X Y : C} (f : X ⟶ Y)
      (φ : (injectiveResolution X).Hom (injectiveResolution Y) f),
      DerivedCategory.Q.map (A.map f) ≫ (c Y).hom =
        (c X).hom ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map φ.hom')) :
    A ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) (q : ℤ) ≅ F.rightDerived q := by
  let H := DerivedCategory.homologyFunctor D (q : ℤ)
  let e := DerivedCategory.homologyFunctorFactors D (q : ℤ)
  apply resolutionHomologyComparison F A q
    (fun X ↦ e.symm.app _ ≪≫ H.mapIso (c X) ≪≫ e.app _)
  intro X Y f φ
  have h := congrArg H.map (hc f φ)
  simp only [Functor.map_comp] at h
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app, Functor.mapIso_hom]
  have ha := e.inv.naturality (A.map f)
  have hb := e.hom.naturality ((F.mapHomologicalComplex _).map φ.hom')
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at ha hb
  dsimp only [H] at h
  simp only [Category.assoc]
  erw [reassoc_of% ha, reassoc_of% h, hb]
  rfl

open Opposite AlgebraicGeometry AlgebraicGeometry.Scheme.ProEt
open scoped Simplicial
private instance (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) : (SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).Additive where
  map_add := by intros; rfl
private theorem hypercover_classical_comparison (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W))
    [HasDerivedCategory.{w} (ModuleCat.{u + 1}
      (((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W)))]
    [EnoughInjectives (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (hweak : ∀ (n : ℕ) (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op (U _⦋n⦌).left)))
    (hzero : Epi ((topology X).yoneda.map (U _⦋0⦌).hom))
    (hone : ∃ c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌), Nonempty (IsLimit c) ∧
      ∃ μ : U _⦋1⦌ ⟶ c.pt,
        (∀ i : Fin 2, μ ≫ c.proj i = U.δ i) ∧
        Epi ((topology X).yoneda.map μ.left))
    (hhigher : ∀ n : ℕ,
      ∃ c : Cone (SimplicialObject.matchingBoundaryIndex U n).multicospan,
        Nonempty (IsLimit c) ∧ ∃ μ : U _⦋n + 2⦌ ⟶ c.pt,
          (∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i) ∧
          Epi ((topology X).yoneda.map μ.left)) (q : ℕ) :
    let C := ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    let ev := SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)
    Nonempty ((CochainComplex.singleFunctor C 0 ⋙ hypercoverTotal X R W U) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ) ≅ ev.rightDerived q) := by
  dsimp only
  let C := ringedSiteModules.{u + 1}
    ((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let ev := SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)
  let A := CochainComplex.singleFunctor C 0 ⋙ hypercoverTotal X R W U
  let E (M : C) : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj M, 0, inferInstance⟩
  let J (M : C) : CochainComplex.Plus C :=
    ⟨(injectiveResolution M).cochainComplex, 0, inferInstance⟩
  obtain ⟨c, hc⟩ :=
    (hypercover_computes_boundedBelow_complex X R W U hweak hzero hone hhigher).1
  let d (M : C) := c (E M) (J M) (fun n ↦ inferInstance)
    (injectiveResolution M).ι' inferInstance
  refine ⟨derivedToHomologyComparison ev A q d ?_⟩
  intro M L f φ
  let g : E M ⟶ E L := ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f)
  let a : J M ⟶ J L := ObjectProperty.homMk φ.hom'
  exact hc (E M) (E L) (J M) (J L) (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    (injectiveResolution M).ι' (injectiveResolution L).ι' inferInstance inferInstance g a
    ⟨Homotopy.ofEq φ.ι'_comp_hom'⟩

private theorem qcqs_evaluation_preservesCoproducts (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    [EnoughInjectives (ringedSiteModules.{u + 1}
      ((sheafCompose (topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (I : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).rightDerived q) := by
  obtain ⟨U, haff, hweak, hzero, hone, hhigher⟩ :=
    exists_affine_weaklyContractible_hypercover X W
  let D := ModuleCat.{u + 1} (((sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))
  let : HasDerivedCategory D := HasDerivedCategory.standard _
  obtain ⟨e⟩ := hypercover_classical_comparison X R W U hweak hzero hone hhigher q
  have := hypercover_total_preservesCoproducts X R W U haff hweak I
  have hs : PreservesColimitsOfShape (Discrete I)
      (CochainComplex.singleFunctor (ringedSiteModules.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) 0) := by
    change PreservesColimitsOfShape (Discrete I) (HomologicalComplex.single _ (.up ℤ) 0)
    infer_instance
  have hh : PreservesColimitsOfShape (Discrete I)
      (HomologicalComplex.homologyFunctor D (.up ℤ) (q : ℤ)) := by
    infer_instance
  exact preservesColimitsOfShape_of_natIso e

private def chainHomologyCompIso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (q : ℕ) : G.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor D (.up ℕ) q ≅
      HomologicalComplex.homologyFunctor C (.up ℕ) q ⋙ G :=
  NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso G) (by
    intro K L f
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (.up ℕ) q).map f) G)

private def homotopyHomologyCompIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (q : ℕ) :
    G.mapHomotopyCategory (.up ℕ) ⋙ HomotopyCategory.homologyFunctor D (.up ℕ) q ≅
      HomotopyCategory.homologyFunctor C (.up ℕ) q ⋙ G := by
  refine Quotient.natIsoLift _ ?_
  exact Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℕ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (G.mapHomologicalComplex (.up ℕ))
      (HomotopyCategory.homologyFunctorFactors D (.up ℕ) q) ≪≫
    chainHomologyCompIso G q ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors C (.up ℕ) q).symm G

private def rightDerivedExactCompIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (q : ℕ) :
    (F ⋙ G).rightDerived q ≅ F.rightDerived q ⋙ G := by
  exact Functor.isoWhiskerLeft (injectiveResolutions C)
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℕ)).symm
        (HomotopyCategory.homologyFunctor E (.up ℕ) q) ≪≫
      Functor.isoWhiskerLeft (F.mapHomotopyCategory (.up ℕ)) (homotopyHomologyCompIso G q))

namespace AlgebraicGeometry.Scheme

private abbrev moduleEvalAb (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (V : X.ProEt) :=
  SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V) ⋙
    forget₂ (ModuleCat.{u + 1} (R.obj.obj (op V))) AddCommGrpCat.{u + 1}

private instance (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (V : X.ProEt) :
    (moduleEvalAb X R V).Additive where
  map_add := by intros; rfl

private theorem isZero_of_weaklyContractible_evaluation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (M : proEtaleRingModules X R)
    (hM : ∀ (V : X.ProEt), IsAffine V.left →
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op V))) →
      IsZero ((moduleEvalAb X R V).obj M)) : IsZero M := by
  let U := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have hU : IsZero (U.obj M) := by
    apply Sheaf.isZero_of_isZero_obj
    intro V
    obtain ⟨I, W, f, hcov, haff, hweak⟩ :=
      exists_affine_weaklyContractible_covering_family X V.unop
    have hcover : Sieve.ofArrows W f ∈ ProEt.topology X V.unop :=
      Precoverage.generate_mem_toGrothendieck hcov
    rw [IsZero.iff_id_eq_zero]
    ext x
    change x = 0
    apply Sheaf.isSeparated (U.obj M) V.unop _ hcover x 0
    rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
    have hzero := (IsZero.iff_id_eq_zero _).1 (hM (W i) (haff i) (hweak i))
    have hx (z : (U.obj M).obj.obj (op (W i))) : z = 0 := by
      exact ConcreteCategory.congr_hom hzero z
    have : Subsingleton ((U.obj M).obj.obj (op (W i))) :=
      ⟨fun z z' ↦ (hx z).trans (hx z').symm⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      Subsingleton.elim ((U.obj M).obj.map (f i).op x) ((U.obj M).obj.map (f i).op 0)]
  rw [IsZero.iff_id_eq_zero]
  apply U.map_injective
  simpa using (IsZero.iff_id_eq_zero _).1 hU

private theorem isIso_of_weaklyContractible_evaluation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N : proEtaleRingModules X R} (f : M ⟶ N)
    (hf : ∀ (V : X.ProEt), IsAffine V.left →
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1))) (g : F ⟶ G),
        Epi g → Function.Surjective (g.hom.app (op V))) →
      IsIso ((moduleEvalAb X R V).map f)) : IsIso f := by
  have hk : IsZero (kernel f) := by
    apply isZero_of_weaklyContractible_evaluation X R
    intro V haff hV
    let : IsAffine V.left := haff
    let ev := SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V)
    have : PreservesFiniteLimits ev :=
      (affine_weaklyContractible_evaluation_colimits X R V hV).1
    have := hf V haff hV
    exact IsZero.of_iso (isZero_kernel_of_mono ((moduleEvalAb X R V).map f))
      (PreservesKernel.iso (moduleEvalAb X R V) f)
  have hc : IsZero (cokernel f) := by
    apply isZero_of_weaklyContractible_evaluation X R
    intro V haff hV
    let : IsAffine V.left := haff
    let ev := SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V)
    have : PreservesFiniteColimits ev :=
      (affine_weaklyContractible_evaluation_colimits X R V hV).2.1
    have := hf V haff hV
    exact IsZero.of_iso (isZero_cokernel_of_epi ((moduleEvalAb X R V).map f))
      (PreservesCokernel.iso (moduleEvalAb X R V) f)
  have := Abelian.mono_of_kernel_ι_eq_zero f (hk.eq_of_src _ _)
  have := Abelian.epi_of_cokernel_π_eq_zero f (hc.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi f

private theorem relative_evaluation_preservesCoproducts
    {T U : Scheme.{u}} (h : T ⟶ U)
    (R : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S)
    [EnoughInjectives (proEtaleRingModules T S)]
    (V : U.ProEt) [IsAffine V.left]
    (hV : ∀ (F G : Sheaf (ProEt.topology U) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op V)))
    [CompactSpace ((proEtaleBaseChange h).obj V).left]
    [QuasiSeparatedSpace ((proEtaleBaseChange h).obj V).left]
    (I : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete I)
      ((proEtaleRingModuleDirectImage h R S c).rightDerived q ⋙
        SheafOfModules.evaluation.{u + 1}
          ((sheafCompose (ProEt.topology U)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op V) ⋙
          forget₂ (ModuleCat.{u + 1} (R.obj.obj (op V))) AddCommGrpCat.{u + 1}) := by
  let RT : Sheaf (ProEt.topology T) RingCat.{u + 1} := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let RU : Sheaf (ProEt.topology U) RingCat.{u + 1} := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let W := (proEtaleBaseChange h).obj V
  let evT : proEtaleRingModules T S ⥤ ModuleCat.{u + 1} (S.obj.obj (op W)) :=
    SheafOfModules.evaluation.{u + 1} RT (op W)
  let evU : proEtaleRingModules U R ⥤ ModuleCat.{u + 1} (R.obj.obj (op V)) :=
    SheafOfModules.evaluation.{u + 1} RU (op V)
  let GT : ModuleCat.{u + 1} (RT.obj.obj (op W)) ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} (RT.obj.obj (op W))) AddCommGrpCat.{u + 1}
  let GU : ModuleCat.{u + 1} (RU.obj.obj (op V)) ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} (RU.obj.obj (op V))) AddCommGrpCat.{u + 1}
  let F := proEtaleRingModuleDirectImage h R S c
  have : evT.Additive := ⟨by intros; rfl⟩
  have : evU.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits evU :=
    (affine_weaklyContractible_evaluation_colimits U R V hV).1
  have : PreservesFiniteColimits evU :=
    (affine_weaklyContractible_evaluation_colimits U R V hV).2.1
  have : PreservesColimitsOfShape (Discrete I) (evT.rightDerived q) :=
    qcqs_evaluation_preservesCoproducts.{u} T S W I q
  have : PreservesFiniteLimits GT := inferInstance
  have : PreservesFiniteColimits GT := by
    exact ⟨fun J _ _ ↦
      ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0}
        (R := S.obj.obj (op W)) J⟩
  have : PreservesFiniteLimits GU := inferInstance
  have : PreservesFiniteColimits GU := by
    exact ⟨fun J _ _ ↦
      ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0}
        (R := R.obj.obj (op V)) J⟩
  let eT : (evT ⋙ GT).rightDerived q ≅ evT.rightDerived q ⋙ GT :=
    rightDerivedExactCompIso (C := proEtaleRingModules T S)
      (D := ModuleCat.{u + 1} (S.obj.obj (op W)))
      (E := AddCommGrpCat.{u + 1}) evT GT q
  have : PreservesColimitsOfShape (Discrete I) GT := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (evT.rightDerived q ⋙ GT) := inferInstance
  have : PreservesColimitsOfShape (Discrete I) ((evT ⋙ GT).rightDerived q) :=
    preservesColimitsOfShape_of_natIso eT.symm
  have : PreservesColimitsOfShape (Discrete I) ((F ⋙ (evU ⋙ GU)).rightDerived q) := by
    change PreservesColimitsOfShape (Discrete I) ((evT ⋙ GT).rightDerived q)
    infer_instance
  exact preservesColimitsOfShape_of_natIso
    (rightDerivedExactCompIso (E := AddCommGrpCat.{u + 1}) F (evU ⋙ GU) q)

end AlgebraicGeometry.Scheme
