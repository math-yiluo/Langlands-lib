/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.CategoryTheory.Sites.CoinduceZMod
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
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
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCohomologicalDimensionDirectSums

/-! # Derived coproducts with a fixed annihilator

Source: Stacks Project, etale-cohomology.tex, Tag 0F11(1), extended to objects
annihilated by a fixed positive integer over arbitrary constant coefficients;
sites-cohomology.tex, Tag 0D6J(3), comparison after forgetting coefficients.
(blueprint: lem-sf-fixed-exponent-derived-coproducts).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma sigma_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {I : Type*} (K : I → C)
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I D] [HasCoproductsOfShape I E] :
    sigmaComparison (F ⋙ G) K =
      sigmaComparison G (fun i ↦ F.obj (K i)) ≫ G.map (sigmaComparison F K) := by
  exact (sigmaComparison_map_desc G (fun i ↦ F.obj (K i)) _
    (fun i ↦ F.map (Sigma.ι K i))).symm

private lemma sigma_image {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {I : Type*} (K : I → C)
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I D] [HasCoproductsOfShape I E]
    [PreservesColimit (Discrete.functor K) F]
    [PreservesColimit (Discrete.functor K) (F ⋙ G)] :
    IsIso (sigmaComparison G (fun i ↦ F.obj (K i))) := by
  have : IsIso (sigmaComparison G (fun i ↦ F.obj (K i)) ≫
      G.map (sigmaComparison F K)) := by rw [← sigma_comp]; infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map (sigmaComparison F K))

private lemma sigma_natural {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {I : Type*} {K L : I → C} (j : ∀ i, K i ⟶ L i)
    [HasCoproduct K] [HasCoproduct L]
    [HasCoproduct (fun i ↦ F.obj (K i))] [HasCoproduct (fun i ↦ F.obj (L i))] :
    sigmaComparison F K ≫ F.map (Limits.Sigma.map j) =
      Limits.Sigma.map (fun i ↦ F.map (j i)) ≫ sigmaComparison F L := by
  apply Sigma.hom_ext
  intro i
  simp only [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc, ι_comp_sigmaComparison,
    ← F.map_comp, Sigma.ι_map]

private lemma sigma_retract {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {I : Type*} {K L : I → C}
    [HasCoproduct K] [HasCoproduct L]
    [HasCoproduct (fun i ↦ F.obj (K i))] [HasCoproduct (fun i ↦ F.obj (L i))]
    (j : ∀ i, K i ⟶ L i) (r : ∀ i, L i ⟶ K i) (h : ∀ i, j i ≫ r i = 𝟙 _)
    [IsIso (sigmaComparison F L)] : IsIso (sigmaComparison F K) := by
  have hsum : Limits.Sigma.map j ≫ Limits.Sigma.map r = 𝟙 _ := by
    rw [Limits.Sigma.map_comp_map]; simp only [h, Limits.Sigma.map_id]
  have himg : Limits.Sigma.map (fun i ↦ F.map (j i)) ≫
      Limits.Sigma.map (fun i ↦ F.map (r i)) = 𝟙 _ := by
    rw [Limits.Sigma.map_comp_map]; simp only [← F.map_comp, h, F.map_id, Limits.Sigma.map_id]
  refine ⟨F.map (Limits.Sigma.map j) ≫ inv (sigmaComparison F L) ≫
    Limits.Sigma.map (fun i ↦ F.map (r i)), ?_, ?_⟩
  · rw [← Category.assoc, sigma_natural, Category.assoc,
      IsIso.hom_inv_id_assoc, himg]
  · rw [Category.assoc, Category.assoc, ← sigma_natural,
      IsIso.inv_hom_id_assoc, ← F.map_comp, hsum, F.map_id]

private lemma forget_derived_coproducts (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (moduleAbelianForget Λ X).mapDerivedCategory := by
  have := constantModuleSheaves_forget_preservesColimits X Λ
  exact Functor.mapDerivedCategory_preservesCoproducts (moduleAbelianForget Λ X) I

private lemma forget_comparison (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleAbelianForget B Y).mapDerivedCategory.ReflectsIsomorphisms ∧
      IsIso (moduleAbelianUnboundedLowerStarComparison B f) := by
  let sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y) := {
    w := by simp
    isoPullback := (asIso (pullback.fst f (𝟙 Y))).symm
    hom_fst := by simp
    hom_snd := by
      change inv (pullback.fst f (𝟙 Y)) ≫ pullback.snd f (𝟙 Y) = f
      rw [IsIso.inv_comp_eq]
      simpa using (pullback.condition (f := f) (g := 𝟙 Y)).symm }
  have h := unbounded_abelian_exchange_comparison B sq
  exact ⟨(h.1 Y).2.2.2.1, (h.2.1 f).1⟩

private noncomputable local instance coind_rightAdjoint (n : ℕ) :
    (coindZMod.{u + 1} n).IsRightAdjoint :=
  (forget₂CoindZModAdj n).isRightAdjoint

private lemma coind_additive (X : Scheme.{u}) (n : ℕ) :
    (sheafCompose X.smallEtaleTopology (coindZMod.{u + 1} n)).Additive := by
  exact Functor.additive_of_preserves_binary_products _

private lemma coind_shortExact (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective F] :
    ∃ (h : Sheaf.coindCounit X.smallEtaleTopology n F ≫ (n • 𝟙 F) = 0),
      (ShortComplex.mk (Sheaf.coindCounit X.smallEtaleTopology n F) (n • 𝟙 F) h).ShortExact := by
  let G := sheafCompose X.smallEtaleTopology (coindZMod.{u + 1} n)
  let a := Sheaf.coindCounit X.smallEtaleTopology n F
  have hz : a ≫ (n • 𝟙 F) = 0 := by
    ext V x
    change n • (a.hom.app V x) = 0
    rw [← map_nsmul]
    let M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)) := (G.obj F).obj.obj V
    have hx : n • (show M from x) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod n))]
      have hc : (n : ULift.{u + 1} (ZMod n)) = 0 := by
        apply ULift.ext; exact ZMod.natCast_self n
      rw [hc]
      exact zero_smul _ _
    rw [hx, map_zero]
  refine ⟨hz, ?_⟩
  let S := ShortComplex.mk a (n • 𝟙 F) hz
  have hpre : (S.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ (fun V ↦ ?_)
    have he : ((S.map (sheafToPresheaf _ _)).map
        ((CategoryTheory.evaluation _ _).obj V)).Exact := by
      apply (ShortComplex.ab_exact_iff _).2
      intro x hx
      exact (forget₂CoindZModAdj_counit_shortExact n (F.obj.obj V)).2 x
        (by
          change n • x = 0 at hx
          exact_mod_cast hx)
    rw [ShortComplex.exact_iff_isZero_homology] at he
    exact he.of_iso
      ((S.map (sheafToPresheaf _ _)).mapHomologyIso
        ((CategoryTheory.evaluation _ _).obj V)).symm
  have : Mono S.f := by
    have (V : X.Etaleᵒᵖ) : Mono (a.hom.app V) :=
      (AddCommGrpCat.mono_iff_injective _).2
        (forget₂CoindZModAdj_counit_shortExact n (F.obj.obj V)).1
    have : Mono a.hom := NatTrans.mono_of_mono_app _
    exact (sheafToPresheaf _ _).mono_of_mono_map (inferInstance : Mono a.hom)
  have : Epi S.g := Sheaf.epi_nsmul_id_of_injective.{u + 1, u, u + 1} F hn
  refine ⟨?_⟩
  have e : S.map (sheafToPresheaf _ _ ⋙ presheafToSheaf _ _) ≅ S :=
    S.mapNatIso (asIso (sheafificationAdjunction _ _).counit)
  exact (ShortComplex.exact_iff_of_iso e).1 (hpre.map (presheafToSheaf _ _))

private lemma annihilated_retract (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (A : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hA : n • 𝟙 A = 0) :
    ∃ L : DerivedCategoryModule (ULift.{u + 1} (ZMod n)) X,
      Nonempty (Retract A
        ((moduleAbelianForget (ULift.{u + 1} (ZMod n)) X).mapDerivedCategory.obj L)) := by
  classical
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let G := sheafCompose X.smallEtaleTopology (coindZMod.{u + 1} n)
  have : G.Additive := coind_additive X n
  let U := moduleAbelianForget (ULift.{u + 1} (ZMod n)) X
  let P := DerivedCategory.Q.objPreimage A
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj P
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} C).app P) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} C P).2
  let e : A ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso A).symm ≪≫
      asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution C).app P))
  let L := (G.mapHomologicalComplex (.up ℤ)).obj I
  let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶ I := {
    f := fun q ↦ Sheaf.coindCounit X.smallEtaleTopology n (I.X q)
    comm' := fun i j _ ↦ by
      ext V x
      exact ConcreteCategory.congr_hom
        ((forget₂CoindZModAdj n).counit.naturality ((I.d i j).hom.app V)).symm x }
  have hz : a ≫ (n • 𝟙 I) = 0 := by
    ext q : 1
    exact (coind_shortExact X n hn (I.X q)).choose
  let S := ShortComplex.mk a (n • 𝟙 I) hz
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    exact (coind_shortExact X n hn (I.X q)).choose_spec
  let T := DerivedCategory.triangleOfSES hS
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  have hnI : n • 𝟙 (DerivedCategory.Q.obj I) = 0 := by
    apply (cancel_epi e.hom).1
    calc
      e.hom ≫ (n • 𝟙 _) = (n • 𝟙 A) ≫ e.hom := by
        simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
          Category.comp_id, Category.id_comp]
      _ = e.hom ≫ 0 := by rw [hA, zero_comp, comp_zero]
  have hzT : T.mor₂ = 0 := by
    change DerivedCategory.Q.map (n • 𝟙 I) = 0
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, hnI]
  obtain ⟨j, hj⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT
    (𝟙 (DerivedCategory.Q.obj I)) (by rw [hzT, comp_zero])
  let c := U.mapDerivedCategoryFactors.app L
  refine ⟨DerivedCategory.Q.obj L, ⟨{
    i := e.hom ≫ j ≫ c.inv
    r := c.hom ≫ DerivedCategory.Q.map a ≫ e.inv
    retract := ?_ }⟩⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hj' : j ≫ DerivedCategory.Q.map a = 𝟙 _ := hj.symm
  rw [reassoc_of% hj']
  simp

/-- For a qcqs morphism of finite torsion etale cohomological dimension, total
K-injective direct image preserves coproducts of arbitrary unbounded complexes killed
by one fixed positive integer. The coefficient ring is arbitrary. The comparison is
`Limits.sigmaComparison`, whose composite with each coprojection is the image of the
corresponding coprojection (`Limits.ι_comp_sigmaComparison`). Empty families are allowed.

Source: Stacks Project, Tags 0F11(1), 0D6J(3), and the divisibility argument in
Tag 0DD7. The fixed-annihilator extension uses the dual kernel construction below.
(blueprint: lem-sf-fixed-exponent-derived-coproducts).

Proof:
1. Ordinary coefficient forgetting preserves coproducts. Its exact derived functor
therefore preserves them too. The unbounded abelian comparison, applied to the square
with identity vertical maps, identifies forgotten module direct image with abelian
direct image and makes derived forgetting conservative.
2. For an abelian derived object A killed by n, choose a representative I with
injective terms. Apply coinduction Hom(Z/n,-) termwise, obtaining a Z/n complex L.
The counit U(L) -> I identifies its terms with the kernels of n on I. Injective
abelian sheaves are divisible, so 0 -> U(L) -> I --n--> I -> 0 is short exact.
3. In its derived triangle the second map is zero, since QI is isomorphic to A.
Exactness of the representable functor lifts the identity of QI through the first
map. Thus A is a retract of the underlying abelian object of QL. This is the dual
of the split quotient-cone argument and needs no K-flat resolution or coefficient
ring-sheaf equivalence.
4. Apply 0F11(1) to the family QL_i. The natural coefficient comparisons and Step 1
identify its invertible coproduct comparison with the abelian comparison on U QL_i.
5. Naturality of the coproduct comparison in the inclusion and retraction maps makes
its value on A_i a retract of that invertible comparison. The explicit inverse is
Rf_*(sum j_i), followed by the inverse comparison, followed by sum Rf_*(r_i).
The two inverse identities use the two naturality squares and j_i followed by r_i
being the identity.
6. Step 1 for the original coefficient ring reflects this abelian coproduct property
back to the stated module comparison. All coprojections are preserved throughout.
The construction includes empty families and n=1, without any boundedness assumption. -/
theorem isIso_sigmaComparison_rightDerivedLowerStar_of_fixedExponent
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (hf : f.torsionEtaleCohomologicalDimension < ⊤) (n : ℕ) (hn : 1 ≤ n)
    (I : Type (u + 1)) (K : I → DerivedCategoryModule Λ X)
    (hK : ∀ i : I, n • 𝟙 (K i) = 0) :
    IsIso (@sigmaComparison _ _ _ _ _
      (rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f) K
      ((derived_hasCoproducts
        (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) I).has_colimit _)
      ((derived_hasCoproducts
        (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) I).has_colimit _)) := by
  classical
  let MX := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let MY := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let AX := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let AY := Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : HasCoproducts.{u + 1} (DerivedCategory MX) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory MY) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory AX) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory AY) := derived_hasCoproducts
  let U := (moduleAbelianForget Λ X).mapDerivedCategory
  let V := (moduleAbelianForget Λ Y).mapDerivedCategory
  let F := rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  let G := rightDerivedLowerStar AddCommGrpCat.{u + 1} f
  have : V.ReflectsIsomorphisms := (forget_comparison Λ f).1
  have : IsIso (moduleAbelianUnboundedLowerStarComparison Λ f) :=
    (forget_comparison Λ f).2
  have : PreservesColimitsOfShape (Discrete I) U := forget_derived_coproducts Λ X I
  have : PreservesColimitsOfShape (Discrete I) V := forget_derived_coproducts Λ Y I
  let A := fun i ↦ U.obj (K i)
  have hA (i : I) : n • 𝟙 (A i) = 0 := by
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
      congrArg U.map (hK i)
  choose L r using fun i ↦ annihilated_retract X n (by omega) (A i) (hA i)
  let Z := ULift.{u + 1} (ZMod n)
  let UZ := (moduleAbelianForget Z X).mapDerivedCategory
  let VZ := (moduleAbelianForget Z Y).mapDerivedCategory
  let FZ := rightDerivedLowerStar (ModuleCat.{u + 1} Z) f
  have : HasCoproducts.{u + 1} (DerivedCategoryModule Z X) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategoryModule Z Y) := derived_hasCoproducts
  have : PreservesColimitsOfShape (Discrete I) UZ := forget_derived_coproducts Z X I
  have : PreservesColimitsOfShape (Discrete I) VZ := forget_derived_coproducts Z Y I
  have : PreservesColimitsOfShape (Discrete I) FZ :=
    (derivedDirectImage_and_globalSections_preserveCoproducts n hn).1 f hf I
  have : IsIso (moduleAbelianUnboundedLowerStarComparison Z f) :=
    (forget_comparison Z f).2
  have : PreservesColimitsOfShape (Discrete I) (FZ ⋙ VZ) := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (UZ ⋙ G) :=
    preservesColimitsOfShape_of_natIso (F := FZ ⋙ VZ) (G := UZ ⋙ G)
      (asIso (moduleAbelianUnboundedLowerStarComparison Z f))
  have : IsIso (sigmaComparison G (fun i ↦ UZ.obj (L i))) := sigma_image UZ G L
  have : IsIso (sigmaComparison G A) :=
    sigma_retract G (fun i ↦ (r i).some.i) (fun i ↦ (r i).some.r)
      (fun i ↦ (r i).some.retract)
  have : PreservesColimit (Discrete.functor A) G :=
    PreservesCoproduct.of_iso_comparison G A
  have : PreservesColimit (Discrete.functor (fun i ↦ U.obj (K i))) G :=
    inferInstanceAs (PreservesColimit (Discrete.functor A) G)
  have : PreservesColimit (Discrete.functor K ⋙ U) G :=
    preservesColimit_of_iso_diagram
      (K₁ := Discrete.functor (fun i ↦ U.obj (K i))) G
      (Discrete.compNatIsoDiscrete K U).symm
  have : PreservesColimit (Discrete.functor K) (U ⋙ G) := inferInstance
  have : PreservesColimit (Discrete.functor K) (F ⋙ V) :=
    preservesColimit_of_natIso (Discrete.functor K) (F := U ⋙ G) (G := F ⋙ V)
      (asIso (moduleAbelianUnboundedLowerStarComparison Λ f)).symm
  have : ReflectsColimit (Discrete.functor K ⋙ F) V :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have : PreservesColimit (Discrete.functor K) F :=
    preservesColimit_of_reflects_of_preserves F V
  exact inferInstanceAs (IsIso (sigmaComparison F K))

end AlgebraicGeometry.Etale
