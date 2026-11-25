/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Inverse-limit acyclicity of levelwise ringed-topos direct images

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E.
(blueprint: lem-weil-ringed-tower-pushforward-limit-acyclic).

The localization argument uses the shared resolving-adjunction API in
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

private theorem towerAcyclic_commRingSheaf
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ O : Sheaf J CommRingCat.{u},
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O = R := by
  let obj (U : Cᵒᵖ) : CommRingCat.{u} :=
    { carrier := R.obj.obj U
      commRing := { (inferInstance : Ring (R.obj.obj U)) with mul_comm := hcomm U } }
  let Oc : Cᵒᵖ ⥤ CommRingCat.{u} :=
    { obj := obj
      map := fun {U V} g ↦
        @CommRingCat.ofHom (obj U) (obj V) (obj U).commRing (obj V).commRing
          (R.obj.map g).hom
      map_id := fun U ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_id U)
      map_comp := fun g h ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_comp g h) }
  have hO : Presheaf.IsSheaf J Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp J Oc (forget₂ CommRingCat RingCat)
    exact R.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

private def towerUntranspose {A : Type*} [Category* A] [HasZeroMorphisms A]
    (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i
  d i j :=
    { app := fun n ↦ (P.obj n).d i j
      naturality := fun n m g ↦ (P.map g).comm i j }
  shape i j h := by ext n; exact (P.obj n).shape i j h
  d_comp_d' i j k _ _ := by ext n; exact (P.obj n).d_comp_d i j k

private def towerUntransposeMap {A : Type*} [Category* A] [HasZeroMorphisms A]
    {P Q : ℕᵒᵖ ⥤ CochainComplex A ℤ} (p : P ⟶ Q) :
    towerUntranspose P ⟶ towerUntranspose Q where
  f i :=
    { app := fun n ↦ (p.app n).f i
      naturality := fun n m g ↦ congrArg (fun z ↦ z.f i) (p.naturality g) }
  comm' i j _ := by ext n; exact (p.app n).comm i j

private structure towerFlatKFlat
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (X : HomotopyCategory
      (ℕᵒᵖ ⥤ ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (ComplexShape.up ℤ)) : Prop where
  kflat (n : ℕᵒᵖ) : CochainComplex.IsAcyclicTensorKFlat (X.as.asFunctor.obj n)
  flat (n : ℕᵒᵖ) (q : ℤ) : SheafOfModules.IsFlat ((X.as.asFunctor.obj n).X q)

private theorem towerFlatKFlat_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    ∀ X, ∃ (P : _) (s : P ⟶ X), towerFlatKFlat J R P ∧
      IsIso (DerivedCategory.Qh.{w}.map s) := by
  intro X
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  let e := ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_diagram_isKFlatResolution J R (e.inverse ⋙ X.asFunctor)
  let P' := e.functor ⋙ P
  let p' : P' ⟶ X.asFunctor := Functor.whiskerLeft e.functor p
  let s : towerUntranspose P' ⟶ X := towerUntransposeMap p'
  have hs : QuasiIso s := by
    apply (HomologicalComplex.quasiIso_iff_evaluation s).mpr
    intro n
    exact hp (e.functor.obj n)
  refine ⟨(HomotopyCategory.quotient _ _).obj (towerUntranspose P'),
    (HomotopyCategory.quotient _ _).map s, ?_, ?_⟩
  · exact ⟨fun n ↦ hP (e.functor.obj n), fun n ↦ hf (e.functor.obj n)⟩
  · apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hs

private theorem towerMapsInverts
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ → Prop)
    (hinv : ∀ (X Y : CochainComplex A ℤ) (s : X ⟶ Y), P X → P Y →
      QuasiIso s → QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    ∀ {X Y : HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)},
      (∀ n : ℕᵒᵖ, P (X.as.asFunctor.obj n)) →
      (∀ n : ℕᵒᵖ, P (Y.as.asFunctor.obj n)) → ∀ s : X ⟶ Y,
      IsIso (DerivedCategory.Qh.{w}.map s) →
      IsIso (DerivedCategory.Qh.{w}.map
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomotopyCategory
          (ComplexShape.up ℤ)).map s)) := by
  intro X Y hX hY s hs
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  have hq : QuasiIso s := by
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using
        (DerivedCategory.isIso_Qh_map_iff _).mp hs
  have hout : QuasiIso
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    exact hinv _ _ ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) (hX n) (hY n) inferInstance
  apply (DerivedCategory.isIso_Qh_map_iff _).mpr
  rw [Functor.mapHomotopyCategory_map]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    ((HomologicalComplex.mem_quasiIso_iff _).mpr hout)

/-- A K-injective resolution of the levelwise direct image of a K-injective tower
remains a quasi-isomorphism after inverse limit. The three localization choices are
the derived categories already used by the comparison theorem.

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0D6E
(blueprint: lem-weil-ringed-tower-pushforward-limit-acyclic).

Proof: Use K-flat resolutions with flat terms in the target module category and in
its strict tower category. The module pullback adjunction applied levelwise inverts
quasi-isomorphisms between these good tower complexes. The exact constant-tower
functor sends a good module complex to a good tower complex. Consequently the two
pullback adjunctions compose on the homotopy localizations. Testing the displayed map
against good module complexes identifies postcomposition with the quasi-isomorphism
between K-injective resolutions, hence with a bijection. Every derived object has a
good representative, so Yoneda shows the inverse-limit map is invertible after
localization, equivalently a quasi-isomorphism. -/
theorem ringedTowerPushforwardLimitAcyclic
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (hcommR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (hcommS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    (f : RingedToposMorphism R S)
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ℤ) (hT : T.IsKInjective)
    (j : ((((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R)
        (ringedSiteModules.{u} S)).obj f.modules).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ⟶ T) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ⥤ _).mapHomologicalComplex
      (ComplexShape.up ℤ)).map j) := by
  obtain ⟨R, rfl⟩ := towerAcyclic_commRingSheaf R hcommR
  obtain ⟨S, rfl⟩ := towerAcyclic_commRingSheaf S hcommS
  let MR := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let MS := ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
  have := hI
  have := hT
  obtain ⟨FL, hFL, af, _, hinvf⟩ := f.exists_kFlatPullback J K R S
  let CT := (Functor.const ℕᵒᵖ : MS ⥤ (ℕᵒᵖ ⥤ MS))
  let LT := (lim : (ℕᵒᵖ ⥤ MS) ⥤ MS)
  have : CT.Additive := { map_add := by intros; rfl }
  have : LT.Additive := Functor.additive_of_preserves_binary_products _
  have ag : CT ⊣ LT := constLimAdj
  have hIs : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ MS) (ComplexShape.up ℤ)).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using (inferInstance : QuasiIso j)
  have hconst : ∀ {X Y}, flatKFlat K S X → flatKFlat K S Y → ∀ s : X ⟶ Y,
      IsIso (DerivedCategory.Qh.map s) →
        IsIso (DerivedCategory.Qh.map
          ((CT.mapHomotopyCategory (ComplexShape.up ℤ)).map s)) := by
    intro X Y _ _ s hs
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have hq : QuasiIso s := by
      simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff] using
          (DerivedCategory.isIso_Qh_map_iff _).mp hs
    have hout : QuasiIso ((CT.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
      apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
      intro n
      exact hq
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    erw [CT.mapHomotopyCategory_map]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      ((HomologicalComplex.mem_quasiIso_iff _).mpr hout)
  have hmap : IsIso (DerivedCategory.Qh.map
      ((LT.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ MS) (ComplexShape.up ℤ)).map j))) :=
    isIso_map_of_adjoints
      ((af.whiskerRight ℕᵒᵖ).mapHomotopyCategory (ComplexShape.up ℤ))
      (ag.mapHomotopyCategory (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (ℕᵒᵖ ⥤ MS) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso MS (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
      (towerFlatKFlat K S) (flatKFlat K S)
      (towerFlatKFlat_resolutions K S) (flatKFlat_resolutions K S)
      (fun {X Y} hX hY s hs ↦ towerMapsInverts FL
        (fun P ↦ CochainComplex.IsAcyclicTensorKFlat P ∧
          ∀ q : ℤ, SheafOfModules.IsFlat (P.X q))
        (fun P Q t hP hQ ht ↦ hinvf P Q t hP.1 hP.2 hQ.1 hQ.2 ht)
        (fun n ↦ ⟨hX.kflat n, hX.flat n⟩) (fun n ↦ ⟨hY.kflat n, hY.flat n⟩) s hs)
      hconst
      (fun X hX ↦ ⟨fun _ ↦ hX.kflat, fun _ ↦ hX.flat⟩)
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ MR) (ComplexShape.up ℤ)).obj I)
      (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X I)
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ MS) (ComplexShape.up ℤ)).obj T)
      (fun X ↦ CochainComplex.IsKInjective.Qh_map_bijective X T)
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ MS) (ComplexShape.up ℤ)).map j)
  rw [LT.mapHomotopyCategory_map] at hmap
  exact (HomologicalComplex.mem_quasiIso_iff _).mp
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
      ((DerivedCategory.isIso_Qh_map_iff _).mp hmap))

end CategoryTheory
