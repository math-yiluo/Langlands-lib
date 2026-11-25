/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension

import all WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
import all WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.SixFunctors.EllCohomologicalDimensionComparison
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.Integral.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.Integral.IntegralFiniteLevelDualClassical
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence

/-!
# The sections bound for the integral derived dual on classical torsion sheaves

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), finite-reduction bullets.
(blueprint: lem-route-integral-dual-torsion-heart-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option synthInstance.maxSize 4096

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale
private theorem torsion_map_mono
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    (l : ℕ) (F : A) : Mono (ellPowerKernelColimitMap l (F := F)) := by
  let c := ellPowerKernelCocone l (F := F)
  have : ∀ r, Mono (c.ι.app r) := fun r ↦ inferInstanceAs
    (Mono (kernel.ι ((l ^ r) • 𝟙 F)))
  have : Mono c.ι := NatTrans.mono_of_mono_app _
  exact colim.map_mono' c.ι (colimit.isColimit _) (isColimitConstCocone ℕ F)
    (ellPowerKernelColimitMap l (F := F)) (by
      intro r
      exact (colimit.ι_desc (ellPowerKernelCocone l (F := F)) r).trans
        (Category.comp_id (kernel.ι ((l ^ r) • 𝟙 F))).symm)


private theorem additive_preserves_torsion
    {A : Type u} [Category.{v} A] [Abelian A] [HasColimitsOfShape ℕ A]
    {B : Type w} [Category.{x} B] [Abelian B]
    [HasColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ B]
    (H : A ⥤ B) [H.Additive] [PreservesColimitsOfShape ℕ H]
    (l : ℕ) (hl : l.Prime) (F : A) (hF : IsEllPowerTorsion l hl F) :
    IsEllPowerTorsion l hl (H.obj F) := by
  obtain ⟨hc⟩ := (torsion_iff_colimit l hl F).mp hF
  let c := ellPowerKernelCocone l (F := F)
  let D := ellPowerKernelFunctor l (F := H.obj F)
  let a := ellPowerKernelColimitMap l (F := H.obj F)
  have : Mono a := torsion_map_mono l (H.obj F)
  have hz (r : ℕ) : H.map (c.ι.app r) ≫ ((l ^ r) • 𝟙 (H.obj F)) = 0 := by
    change H.map (kernel.ι ((l ^ r) • 𝟙 F)) ≫ ((l ^ r) • 𝟙 (H.obj F)) = 0
    simpa using congrArg H.map (kernel.condition ((l ^ r) • 𝟙 F))
  let k (r : ℕ) : H.obj ((ellPowerKernelFunctor l (F := F)).obj r) ⟶ D.obj r :=
    kernel.lift _ (H.map (c.ι.app r)) (hz r)
  have hk (r : ℕ) : k r ≫ colimit.ι D r ≫ a = H.map (c.ι.app r) := by
    have hi : colimit.ι D r ≫ a = kernel.ι ((l ^ r) • 𝟙 (H.obj F)) :=
      colimit.ι_desc (ellPowerKernelCocone l (F := H.obj F)) r
    rw [hi]
    exact kernel.lift_ι _ _ _
  let d : Cocone (ellPowerKernelFunctor l (F := F) ⋙ H) :=
    { pt := colimit D
      ι :=
        { app := fun r ↦ k r ≫ colimit.ι D r
          naturality := by
            intro r t f
            change H.map ((ellPowerKernelFunctor l (F := F)).map f) ≫
                (k t ≫ colimit.ι D t) = (k r ≫ colimit.ι D r) ≫ 𝟙 (colimit D)
            rw [Category.comp_id]
            apply (cancel_mono a).1
            simp only [Category.assoc]
            rw [hk, hk, ← H.map_comp]
            exact congrArg H.map (c.w f) } }
  let hd := isColimitOfPreserves H hc
  let b : H.obj F ⟶ colimit D := hd.desc d
  have hb : b ≫ a = 𝟙 (H.obj F) := by
    apply hd.hom_ext
    intro r
    rw [← Category.assoc, hd.fac]
    exact (Category.assoc _ _ _).trans ((hk r).trans (Category.comp_id _).symm)
  have hab : a ≫ b = 𝟙 (colimit D) := (cancel_mono a).1 (by
    rw [Category.assoc, hb, Category.comp_id, Category.id_comp])
  change IsIso a
  exact ⟨⟨b, hab, hb⟩⟩
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
private theorem classical_essImage (S : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) :
    IsClassicalAbelian F ↔ (comparisonUpperStar Ab.{u + 1} S).essImage F :=
  (classical_iff_counit S F).trans
    (comparisonAdjunction Ab.{u + 1} S).isIso_counit_app_iff_mem_essImage
private theorem classical_kernel (S : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (hF : IsClassicalAbelian F) (f : F ⟶ F) : IsClassicalAbelian (kernel f) := by
  apply (classical_essImage S _).2
  exact (comparisonUpperStar Ab.{u + 1} S).essImage.prop_of_isLimit
    (c := Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm))
    (kernelIsKernel f)
    (fun j ↦ by cases j <;> exact (classical_essImage S F).1 hF)
private theorem classical_colimit (S : Scheme.{u})
    (D : ℕ ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ r, IsClassicalAbelian (D.obj r)) : IsClassicalAbelian c.pt := by
  apply (classical_essImage S _).2
  exact (comparisonUpperStar Ab.{u + 1} S).essImage.prop_of_isColimit hc
    (fun r ↦ (classical_essImage S _).1 (hD r))

namespace CondensedRing
private theorem tensor_heart_colimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (D : DerivedCategory (supportModules Λ S)) (q : ℤ) :
    PreservesColimitsOfShape ℕ
      (DerivedCategory.singleFunctor _ 0 ⋙ (derivedTensor Λ S).obj D ⋙
        DerivedCategory.homologyFunctor _ q ⋙ Mod.forget (condensedRingObj Λ S)) := by
  let C := supportModules Λ S
  have : AB5OfSize.{0, 0} C := AB5OfSize_shrink.{0, 0, u + 1, u + 1} C
  have : AB5OfSize.{0, 0} (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  let T := (derivedTensor Λ S).obj D
  let HD := DerivedCategory.homologyFunctor C q
  let HC := HomologicalComplex.homologyFunctor C (.up ℤ) q
  let B : C ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u + 1} :=
    Mod.forget (condensedRingObj Λ S)
  obtain ⟨P, _, ⟨eP⟩⟩ := tensorKFlatModel D
  let TP := (curriedTensor (CochainComplex C ℤ)).obj P.obj
  have eT : T = rootTensor D := tensorRootEq Λ S D
  let e : DerivedCategory.Q ⋙ T ≅ TP ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q (eqToIso eT) ≪≫ eP
  have : PreservesColimitsOfSize.{u + 1, u + 1} TP := complexTensor_preservesColimits P.obj
  let : PreservesColimitsOfSize.{0, 0} TP :=
    preservesSmallestColimits_of_preservesColimits TP
  let e' : DerivedCategory.singleFunctor C 0 ⋙ T ⋙ HD ⋙ B ≅
      CochainComplex.singleFunctor C 0 ⋙ TP ⋙ HC ⋙ B :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (CochainComplex.singleFunctor C 0) e) (HD ⋙ B) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor C 0 ⋙ TP)
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C q) B)
  have : PreservesColimitsOfShape ℕ (CochainComplex.singleFunctor C 0) :=
    inferInstanceAs (PreservesColimitsOfShape ℕ (HomologicalComplex.single C (.up ℤ) 0))
  have : PreservesColimitsOfShape ℕ TP := by infer_instance
  have : PreservesColimitsOfShape ℕ HC := by dsimp only [HC]; infer_instance
  have : PreservesColimitsOfShape ℕ B := by dsimp only [B]; infer_instance
  have : PreservesColimitsOfShape ℕ
      (CochainComplex.singleFunctor C 0 ⋙ TP ⋙ HC ⋙ B) := by infer_instance
  exact preservesColimitsOfShape_of_natIso e'.symm
end CondensedRing
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
private theorem kernel_annihilated
    {A : Type*} [Category* A] [Abelian A] (l r : ℕ) (F : A) :
    (l ^ r) • 𝟙 (kernel ((l ^ r) • 𝟙 F)) = 0 := by
  apply (cancel_mono (kernel.ι ((l ^ r) • 𝟙 F))).1
  rw [zero_comp]
  calc
    ((l ^ r) • 𝟙 (kernel ((l ^ r) • 𝟙 F))) ≫ kernel.ι ((l ^ r) • 𝟙 F) =
        (l ^ r) • kernel.ι ((l ^ r) • 𝟙 F) := by
      simp only [Preadditive.nsmul_comp, Category.id_comp]
    _ = kernel.ι ((l ^ r) • 𝟙 F) ≫ ((l ^ r) • 𝟙 F) := by
      simp only [Preadditive.comp_nsmul, Category.comp_id]
    _ = 0 := kernel.condition _


private theorem tensor_cohomology_classical_torsion
    (l : ℕ) (hl : l.Prime)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (D : DerivedCategory (supportModules Λ S))
    (hfinite : ∀ (G : supportModules Λ S), IsClassicalAbelian G.X →
      ∀ r : ℕ, 1 ≤ r → (l ^ r) • 𝟙 G.X = 0 → ∀ q : ℤ,
        IsClassicalAbelian
          ((DerivedCategory.homologyFunctor _ q).obj
            (((derivedTensor Λ S).obj D).obj
              ((DerivedCategory.singleFunctor _ 0).obj G))).X)
    (F : supportModules Λ S) (hF : IsClassicalAbelian F.X)
    (htors : IsEllPowerTorsion l hl F.X) (q : ℤ) :
    IsClassicalAbelian
      ((DerivedCategory.homologyFunctor _ q).obj
        (((derivedTensor Λ S).obj D).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
    IsEllPowerTorsion l hl
      ((DerivedCategory.homologyFunctor _ q).obj
        (((derivedTensor Λ S).obj D).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).X := by
  let C := supportModules Λ S
  have : AB5OfSize.{0, 0} C := AB5OfSize_shrink.{0, 0, u + 1, u + 1} C
  have : AB5OfSize.{0, 0} (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) :=
    AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
  let B : C ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u + 1} :=
    Mod.forget (condensedRingObj Λ S)
  let T := (derivedTensor Λ S).obj D
  have : T.Additive := by
    dsimp only [T, derivedTensor]
    infer_instance
  let H : C ⥤ Sheaf (Scheme.ProEt.topology S) Ab.{u + 1} :=
    DerivedCategory.singleFunctor C 0 ⋙ T ⋙ DerivedCategory.homologyFunctor C q ⋙ B
  have : PreservesColimitsOfShape ℕ H :=
    tensor_heart_colimits Λ S D q
  have hMod : IsEllPowerTorsion l hl F :=
    (torsion_transport B l hl F F.X (Iso.refl _)).2 htors
  obtain ⟨hc⟩ := (torsion_iff_colimit l hl F).1 hMod
  refine ⟨?_, additive_preserves_torsion H l hl F hMod⟩
  apply classical_colimit S _ _ (isColimitOfPreserves H hc)
  intro r
  let Fr : C := ellPowerKernel l (F := F) r
  let e : Fr.X ≅ kernel ((l ^ r) • 𝟙 F.X) :=
    PreservesKernel.iso B ((l ^ r) • 𝟙 F) ≪≫
      kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp)
  have hFr : IsClassicalAbelian Fr.X := by
    apply (classical_essImage S _).2
    exact (comparisonUpperStar Ab.{u + 1} S).essImage.prop_of_iso e.symm
      ((classical_essImage S _).1 (classical_kernel S F.X hF _))
  have hk : (l ^ (r + 1)) • 𝟙 Fr = 0 := by
    change (l ^ (r + 1)) • 𝟙 (kernel ((l ^ r) • 𝟙 F)) = 0
    rw [pow_succ, mul_nsmul, kernel_annihilated l r F, nsmul_zero]
  have hk' : (l ^ (r + 1)) • 𝟙 Fr.X = 0 := by
    change (l ^ (r + 1)) • 𝟙 (B.obj Fr) = 0
    simpa using congrArg B.map hk
  change IsClassicalAbelian
    ((DerivedCategory.homologyFunctor C q).obj
      (T.obj ((DerivedCategory.singleFunctor C 0).obj Fr))).X
  exact hfinite Fr hFr (r + 1) (by omega) hk' q
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
private theorem dual_data
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (L : supportModules Λ S)
    (hresolution : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules Λ (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar Λ (U.f a)).obj L)) :
    DerivedCategory.torAmplitudeIn _ 0 1 (stratumModuleDual Λ S L) := by
  classical
  let C := supportModules Λ S
  obtain ⟨U, hU⟩ := hresolution
  have hlocal (a : U.I₀) :
      IsDualizable ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
        ((upperStar Λ (U.f a)).obj L)) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
          ((upperStar Λ (U.f a)).obj L)) := by
    obtain ⟨T, hT, h₁, h₂, ⟨e⟩⟩ := hU a
    have h := shortExact_dualizable_tor_of_iso hT h₁ h₂ e
    exact ⟨dualizableRootTransport Λ (U.X a) _ h.1, h.2⟩
  let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
  let K := (DerivedCategory.singleFunctor C 0).obj L
  have hdglobal : IsDualizable K := by
    apply (condensed_dualizable_iff_proetale_cover R S U K).mpr
    intro a
    let e := ((upperStar Λ (U.f a)).mapDerivedCategorySingleFunctor 0).app L
    have hr := dualizableRootOfSource Λ (U.X a) _ (hlocal a).1
    exact dualizableRootTransport Λ (U.X a) _
      (rootDualizable_of_iso _ _ e.symm hr)
  have hK := (integralHeart_local_duality_descent Λ S L U (-1) 0 hlocal).2
  let D := stratumModuleDual Λ S L
  let H := (derivedHom Λ S).obj (op K)
  have adjH : rootTensor K ⊣ H :=
    (derivedTensorHomAdjunction Λ K).ofNatIsoLeft (eqToIso (tensorRootEq Λ S K))
  have hDdef : D = H.obj (rootUnit (C := C)) :=
    congrArg H.obj (unitRootEq Λ S)
  have hdual := dualizableRootOfSource Λ S K hdglobal
  exact (dualConsequences (C := C) K D H (stratumModuleDualTensor Λ S L)
    (curriedTensor (CochainComplex C ℤ)) (complexTensorRootEq Λ S)
    adjH (tensorRootEq Λ S D) (eqToIso hDdef) hdual hK).1
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale
private noncomputable def evaluation_comparison
    (S : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology S) RingCat.{u + 1})
    [EnoughInjectives (SheafOfModules.{u + 1} R)]
    (M : SheafOfModules.{u + 1} R) (q : ℕ) :
    (((SheafOfModules.toSheaf R ⋙ Sheaf.sectionsFunctorAt
      (Scheme.ProEt.topology S) (Scheme.ProEt.mk (𝟙 S))).rightDerived q).obj M) ≅
      ((Sheaf.sectionsFunctorAt (Scheme.ProEt.topology S)
        (Scheme.ProEt.mk (𝟙 S))).rightDerived q).obj
          ((SheafOfModules.toSheaf R).obj M) := by
  let C := S.ProEt
  let e : C ≌ ULiftHom.{u + 1} C := ULiftHom.equiv
  let J := Scheme.ProEt.topology S
  let J' := e.inverse.inducedTopology J
  let R' := (e.sheafCongr J J' RingCat.{u + 1}).functor.obj R
  let em := SheafOfModules.smallModulesEquivalence e R
  let ea := e.sheafCongr J J' Ab.{u + 1}
  let : EnoughInjectives (SheafOfModules.{u + 1} R') :=
    EnoughInjectives.of_equivalence em.inverse
  let T := Scheme.ProEt.mk (𝟙 S)
  let A : Sheaf J Ab.{u + 1} ⥤ Ab.{u + 1} := Sheaf.sectionsFunctorAt J T
  let A' := Sheaf.sectionsFunctorAt J' (e.functor.obj T)
  let F := SheafOfModules.toSheaf R ⋙ A
  let F' := SheafOfModules.toSheaf R' ⋙ A'
  have : em.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : ea.functor.Additive := Functor.additive_of_preserves_binary_products _
  let ef : em.functor ⋙ F' ≅ F := Iso.refl _
  let eg : ea.functor ⋙ A' ≅ A := Iso.refl _
  let et : ea.functor.obj ((SheafOfModules.toSheaf R).obj M) ≅
      (SheafOfModules.toSheaf R').obj (em.functor.obj M) := Iso.refl _
  let d := Classical.choose
    (module_abelian_evaluation_comparison_general J' R' (e.functor.obj T))
  exact Functor.rightDerivedObjIsoOfIso ef.symm q M ≪≫
    Functor.compRightDerivedObjIso em.functor F'
      (fun I _ ↦ F'.rightAcyclic_of_injective (em.functor.obj I)) q M ≪≫
    (d q).app (em.functor.obj M) ≪≫
    (A'.rightDerived q).mapIso et.symm ≪≫
    (Functor.compRightDerivedObjIso ea.functor A'
      (fun I _ ↦ A'.rightAcyclic_of_injective (ea.functor.obj I)) q _).symm ≪≫
    Functor.rightDerivedObjIsoOfIso eg q _
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
private noncomputable def sections_heart_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (M : supportModules Λ S) (q : ℕ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((stratumModuleDerivedSections Λ S).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((rightDerivedGlobalSections Ab.{u + 1} S).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.X)) := by
  let J := Scheme.ProEt.topology S
  let O : Sheaf J Ab.{u + 1} := condensedRingObj Λ S
  let R : Sheaf J RingCat.{u + 1} :=
    (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J O)
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let : EnoughInjectives (SheafOfModules.{u + 1} R) :=
    EnoughInjectives.of_equivalence e.inverse
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  let T := Scheme.ProEt.mk (𝟙 S)
  let A : Sheaf J Ab.{u + 1} ⥤ Ab.{u + 1} := Sheaf.sectionsFunctorAt J T
  let B : Sheaf J Ab.{u + 1} ⥤ Ab.{u + 1} := Sheaf.Γ J Ab.{u + 1}
  let F : supportModules Λ S ⥤ Ab.{u + 1} :=
    preadditiveCoyoneda.obj (op (Mod.regular O))
  let G : SheafOfModules.{u + 1} R ⥤ Ab.{u + 1} := SheafOfModules.toSheaf R ⋙ A
  let ef : F ≅ e.functor ⋙ G := regularSectionsIso S Λ
  let ea : B ≅ A := Sheaf.ΓNatIsoSheafSections J _ (Scheme.ProEt.isTerminalMkId S)
  exact F.homologyRightDerivedFunctorObjSingleFunctorIso M q ≪≫
    Functor.rightDerivedObjIsoOfIso ef q M ≪≫
    Functor.compRightDerivedObjIso e.functor G
      (fun I _ ↦ G.rightAcyclic_of_injective (e.functor.obj I)) q M ≪≫
    evaluation_comparison S R (e.functor.obj M) q ≪≫
    Functor.rightDerivedObjIsoOfIso ea.symm q M.X ≪≫
    (B.homologyRightDerivedFunctorObjSingleFunctorIso M.X q).symm

private theorem abelian_sections_bound
    (l : ℕ) (hl : l.Prime) (S : Scheme.{u}) [IsNoetherian S]
    (s : ℕ) (hs : (s : WithTop ℕ) = cohomologicalDimension l hl S)
    (M : Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
    (hM : IsClassicalAbelian M) (hT : IsEllPowerTorsion l hl M) :
    ∀ q : ℤ, q < 0 ∨ (s : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((rightDerivedGlobalSections Ab.{u + 1} S).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  intro q hq
  rcases hq with hq | hq
  · let K := (rightDerivedGlobalSections Ab.{u + 1} S).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)
    have : K.IsGE 0 := by
      dsimp only [K, rightDerivedGlobalSections]
      exact Functor.isGE_rightDerivedFunctor_obj_singleFunctor
        (Sheaf.Γ (Scheme.ProEt.topology S) Ab.{u + 1}) M
    exact K.isZero_of_isGE 0 q hq
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    by_contra hn
    have hle : (r : WithTop ℕ) ≤ cohomologicalDimension l hl S :=
      le_sSup ⟨r, rfl, M, hM, hT, hn⟩
    rw [← hs] at hle
    have hrs : r ≤ s := WithTop.coe_le_coe.mp hle
    exact (not_le_of_gt hq) (Int.ofNat_le.mpr hrs)

private theorem module_sections_bound
    (l : ℕ) (hl : l.Prime)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) [IsNoetherian S]
    (s : ℕ) (hs : (s : WithTop ℕ) = cohomologicalDimension l hl S)
    (M : supportModules Λ S)
    (hM : IsClassicalAbelian M.X) (hT : IsEllPowerTorsion l hl M.X) :
    ∀ q : ℤ, q < 0 ∨ (s : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((stratumModuleDerivedSections Λ S).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  intro q hq
  rcases hq with hq | hq
  · let H : supportModules Λ S ⥤ Ab.{u + 1} :=
      preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ S)))
    let K := (stratumModuleDerivedSections Λ S).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)
    have : K.IsGE 0 := by
      dsimp only [K, stratumModuleDerivedSections]
      exact H.isGE_rightDerivedFunctor_obj_singleFunctor M
    exact K.isZero_of_isGE 0 q hq
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    exact (abelian_sections_bound l hl S s hs M.X hM hT r (Or.inr hq)).of_iso
      (sections_heart_iso Λ S M r)
end AlgebraicGeometry.ProEtale.CondensedRing

private theorem amplitude_from_heart_images
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) (K : DerivedCategory A)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor A q).obj K))
    (hheart : ∀ q i : ℤ, i < c ∨ d < i →
      IsZero ((DerivedCategory.homologyFunctor B i).obj
        (T.obj ((DerivedCategory.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A q).obj K))))) :
    ∀ i : ℤ, i < a + c ∨ b + d < i →
      IsZero ((DerivedCategory.homologyFunctor B i).obj (T.obj K)) := by
  let P : A → Prop := fun F ↦ ∀ i : ℤ, i < c ∨ d < i →
    IsZero ((DerivedCategory.homologyFunctor B i).obj
      (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))
  apply DerivedCategory.bounded_heart_amplitude A B T P
    (fun M N e h i hi ↦ (h i hi).of_iso
      ((DerivedCategory.homologyFunctor B i).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e))).symm)
    (fun i _ ↦ (DerivedCategory.homologyFunctor B i).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A))))
    c d hcd (fun _ h ↦ h) a b hab K hK hheart

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Keeping coefficients abstract prevents expansion of the chosen localization structures.
private theorem sections_bound_of_tor_and_classical_cohomology
    (l : ℕ) (hl : l.Prime)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) [IsNoetherian S]
    (s : ℕ) (hs : (s : WithTop ℕ) = cohomologicalDimension l hl S)
    (D : DerivedCategory (supportModules Λ S)) (F : supportModules Λ S)
    (hD : DerivedCategory.torAmplitudeIn _ 0 1 D)
    (hcoh : ∀ r : ℤ,
      IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedTensor Λ S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X ∧
      IsEllPowerTorsion l hl
        ((DerivedCategory.homologyFunctor _ r).obj
          (((derivedTensor Λ S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).X) :
    ∀ q : ℤ, q < 0 ∨ (s : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((stratumModuleDerivedSections Λ S).obj
          (((derivedTensor Λ S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  let A := supportModules Λ S
  let G := stratumModuleDerivedSections Λ S
  let : G.CommShift ℤ := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  let : G.IsTriangulated := by dsimp only [G, stratumModuleDerivedSections]; infer_instance
  let K := ((derivedTensor Λ S).obj D).obj ((DerivedCategory.singleFunctor A 0).obj F)
  have hK : ∀ r : ℤ, r < 0 ∨ 1 < r →
      IsZero ((DerivedCategory.homologyFunctor A r).obj K) := by
    have h := hD F
    change DerivedCategory.homologyConcentratedIn 0 1 K at h
    have : K.IsGE 0 := h.1
    have : K.IsLE 1 := h.2
    intro r hr
    rcases hr with hr | hr
    · exact K.isZero_of_isGE 0 r hr
    · exact K.isZero_of_isLE 1 r hr
  have hbound := amplitude_from_heart_images G 0 1 0 (s : ℤ)
    (by omega) (by omega) K hK (by
      intro r i hi
      exact module_sections_bound l hl Λ S s hs _ (hcoh r).1 (hcoh r).2 i hi)
  intro q hq
  exact hbound q (by rcases hq with hq | hq <;> omega)

/-- On a classical prime-power torsion heart object, tensor by the derived dual of a
finite constant integral local model followed by derived sections has amplitude `[0,s+1]`.
The target sheaf need not be constructible or annihilated by one uniform prime power.

Source: blueprint `sk-lem-int-ext.proof.md`, paragraph (2), second and third bullets;
`lem-sf-integral-stratum-reduction-ext-bound`, steps 4 and 8--9;
Stacks Tags 08JJ, 099Y and 08J5.
(blueprint: lem-route-integral-dual-torsion-heart-sections).

Proof: the local two-term resolution of L makes each local single L dualizable of
Tor amplitude [-1,0]; proetale descent and the exact dual pairing give Tor amplitude
[0,1] for the derived dual, so K = L-dual tensor F[0] has cohomology only in [0,1].
For every r the kernel F_r of l^r on F is classical (classical sheaves are the essential
image of comparison inverse image, closed under kernels) and killed by l^(r+1), so the
finite-level dual-classicality theorem makes every cohomology sheaf of L-dual tensor
F_r[0] classical. Local torsion writes F as the filtered colimit of the F_r; a K-flat
model of the dual and exact filtered colimits show that each fixed-degree cohomology of
L-dual tensor (-)[0] preserves this colimit, so the cohomology sheaves of K are classical
(closure of the essential image under colimits) and l-power torsion (an additive functor
preserving the kernel colimit preserves local torsion). Module sections agree with
abelian proetale sections through the internal/sectionwise module equivalence and the
ringed-site evaluation comparison (transported along ULiftHom); the definition of cd_l
and s = cd_l bound them in [0,s]. Bounded-heart amplitude for the triangulated derived
sections functor gives [0,s+1]. -/
theorem integral_dual_torsion_heart_sections
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hmodel : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L)
    (s : ℕ)
    (hs : (s : WithTop ℕ) = cohomologicalDimension l (Fact.out : l.Prime) S)
    (F : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hF : IsClassicalAbelian F.X)
    (htors : IsEllPowerTorsion l (Fact.out : l.Prime) F.X) :
    ∀ q : ℤ, q < 0 ∨ (s : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((integralStratumDerivedSections l E S).obj
          ((integralStratumDualTensor l E S L).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  exact sections_bound_of_tor_and_classical_cohomology l (Fact.out : l.Prime)
    (integralCoefficientRing l E) S s hs
    (stratumModuleDual (integralCoefficientRing l E) S L) F
    (dual_data (integralCoefficientRing l E) S L
      (integral_constantModel_localResolution l E S L hmodel))
    (tensor_cohomology_classical_torsion l (Fact.out : l.Prime)
      (integralCoefficientRing l E) S (stratumModuleDual (integralCoefficientRing l E) S L)
      (fun M hM n hn hk q ↦
        (integral_finite_level_dual_classical l E S L hmodel M hM n hn hk q).1)
      F hF htors)

end AlgebraicGeometry.ProEtale.CondensedRing
