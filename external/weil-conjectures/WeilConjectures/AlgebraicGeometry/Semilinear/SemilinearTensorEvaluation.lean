/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent

/-! # Evaluation of the K-flat tensor model

## References

* Zheng Construction 4.1
* Stacks 03EK, 06YS and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r a b
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.CanonicalTensorPullbackProof
namespace WeilConjectures.SemilinearSections

private theorem inverseChain
    {E : Type a} [Category.{b} E] {X₀ X₁ X₂ X₃ X₄ X₅ : E}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄)
    (q : X₄ ⟶ X₅) (w : X₀ ⟶ X₅)
    (h : a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ q = w) :
    d.inv ≫ c.inv ≫ b.inv ≫ a.inv ≫ w = q := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

@[irreducible] private noncomputable def exactTensorTotalIso
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    {B : Type a} [Category.{b} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) :
    ((L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
          (.up ℤ) (.up ℤ) (.up ℤ)) ≅
      Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ L.mapHomologicalComplex (.up ℤ) := by
  have (P Q : CochainComplex A ℤ) : IsIso (tensorPullbackTotal L μ hn P Q) :=
    tensorPullbackTotal_isIso L μ hn V adj P Q
  exact NatIso.ofComponents (fun Z ↦ asIso (tensorPullbackTotal L μ hn Z.1 Z.2)) (by
    intro Z Z' f
    simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
    exact tensorPullbackTotal_naturality L μ hn f.1 f.2)

private theorem exactTensorTotalIso_hom_app
    {A : Type a} [Category.{b} A] [Abelian A] [MonoidalCategory A]
    {B : Type a} [Category.{b} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (μ : ∀ M N : A, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N' : A} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (adj : L ⊣ V) (P Q : CochainComplex A ℤ) :
    (exactTensorTotalIso L μ hn V adj).hom.app (P, Q) = tensorPullbackTotal L μ hn P Q := by
  unfold exactTensorTotalIso
  rfl

section Generic
attribute [local irreducible] SheafOfModules.monoidalCategory
variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R : Sheaf J₀ CommRingCat.{max c v r}) (S : Sheaf J₁ CommRingCat.{max c v r})

private def resolving : ObjectProperty (CochainComplex (Mod J₀ R) ℤ) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R) P ∧
    flatTerms.{c, v, r} J₀ R P

private theorem resolvingHomotopy_resolutions :
    ∀ X : HomotopyCategory (Mod J₀ R) (.up ℤ),
      ∃ (Y : ObjectProperty.FullSubcategory
        (fun X : HomotopyCategory (Mod J₀ R) (.up ℤ) ↦ resolving.{c, v, r} J₀ R X.as))
        (f : Y.obj ⟶ X), HomotopyCategory.quasiIso (Mod J₀ R) (.up ℤ) f := by
  intro X
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
  have hflat : flatTerms.{c, v, r} J₀ R P := by
    intro n
    exact (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)
  refine ⟨⟨(HomotopyCategory.quotient (Mod J₀ R) (.up ℤ)).obj P, hp, hflat⟩,
    (HomotopyCategory.quotient (Mod J₀ R) (.up ℤ)).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq

private noncomputable def resolvingQQ_fullyFaithful
    (E : Type a) [Category.{b} E] :
    (((Functor.whiskeringLeft _ _ E).obj
      (((resolving.{c, v, r} J₀ R).ι ⋙ DerivedCategory.Q).prod
        ((resolving.{c, v, r} J₀ R).ι ⋙ DerivedCategory.Q)))).FullyFaithful := by
  let H : ObjectProperty (HomotopyCategory (Mod J₀ R) (.up ℤ)) :=
    fun X ↦ resolving.{c, v, r} J₀ R X.as
  let ff := Classical.choice (CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    E (HomotopyCategory.quotient (Mod J₀ R) (.up ℤ))
    HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso (Mod J₀ R) (.up ℤ)) DerivedCategory.Qh
    (resolving.{c, v, r} J₀ R) H (fun _ ↦ Iff.rfl) (resolvingHomotopy_resolutions.{c, v, r} J₀ R))
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft (resolving.{c, v, r} J₀ R).ι
      (DerivedCategory.quotientCompQhIso (Mod J₀ R)))
      (Functor.isoWhiskerLeft (resolving.{c, v, r} J₀ R).ι
        (DerivedCategory.quotientCompQhIso (Mod J₀ R)))))

private theorem modelOfOrdinary
    (F : Mod.{c, v, max c v r} J₀ R ⥤
      Mod.{c, v, max c v r} J₁ S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : Mod.{c, v, max c v r} J₁ S ⥤
      Mod.{c, v, max c v r} J₀ R) (adj : F ⊣ G)
    (A : Closed.{c, v, r} J₀ R)
    (B : Closed.{c, v, r} J₁ S)
    (TA : Models.{c, v, r} J₀ R A)
    (TB : Models.{c, v, r} J₁ S B)
    (e : ∀ M N : Mod.{c, v, max c v r} J₀ R,
      F.obj (ordinaryTensor.{c, v, r} J₀ R M N) ≅
        ordinaryTensor.{c, v, r} J₁ S (F.obj M) (F.obj N))
    (he : ∀ {M M' N N' : Mod.{c, v, max c v r} J₀ R} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (ordinaryTensorHom.{c, v, r} J₀ R a b) ≫ (e M' N').hom =
        (e M N).hom ≫ ordinaryTensorHom.{c, v, r} J₁ S (F.map a) (F.map b))
    (hk : ∀ P : CochainComplex (Mod.{c, v, max c v r} J₀ R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R) P →
      flatTerms.{c, v, r} J₀ R P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J₁) (R := S)
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ mu : A.tensor ⋙ F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ B.tensor,
      ∃ model : TensorComparisonModel.{c, v, r} J₀ J₁ R S F A B TA TB mu,
        model.ordinary = e := by
  classical
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let P := resolving.{c, v, r} J₀ R
  let Q : ObjectProperty (CochainComplex (Mod.{c, v, max c v r} J₁ S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
  let i : P.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (CochainComplex.IsKFlatIndependentCoefficients (J := J₀) (R := R)) :=
    ObjectProperty.ιOfLE (fun _ h ↦ h.1)
  let r : (P.ι.prod P.ι) ⋙ totalTensor.{c, v, r} J₀ R ⋙ DerivedCategory.Q ≅
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ A.tensor :=
    Functor.isoWhiskerLeft (i.prod i) TA.comparison
  let H := F.mapHomologicalComplex (.up ℤ)
  have hH : ∀ X, P X → Q (H.obj X) := fun X h ↦ hk X h.1 h.2
  have hn {M M' N N' : Mod.{c, v, max c v r} J₀ R}
      (b : M ⟶ M') (d : N ⟶ N') :
      F.map (b ⊗ₘ d) ≫ (e M' N').hom =
        (e M N).hom ≫ (F.map b ⊗ₘ F.map d) := he b d
  let beta : (H.prod H) ⋙ totalTensor.{c, v, r} J₁ S ≅
      totalTensor.{c, v, r} J₀ R ⋙ H := exactTensorTotalIso F e hn G adj
  obtain ⟨mu, hmu, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q H F.mapDerivedCategory
    (Functor.mapDerivedCategoryFactors F).hom P Q hH
    (resolvingQQ_fullyFaithful.{c, v, r} J₀ R (DerivedCategory (Mod J₁ S)))
    (totalTensor.{c, v, r} J₀ R) (totalTensor.{c, v, r} J₁ S)
    A.tensor B.tensor r TB.comparison beta.symm
    (fun _ _ ↦ by infer_instance) (fun _ _ _ _ ↦ by infer_instance)
  refine ⟨mu, {
    ordinary := e
    chain := fun X Y ↦ beta.hom.app (X, Y)
    summand := ?_
    kflat := hk
    derived := ?_
  }, rfl⟩
  · intro X Y p q k h
    rw [exactTensorTotalIso_hom_app]
    dsimp only [tensorPullbackTotal, tensorPullbackTotalComponent, tensorSummand]
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  · intro X Y hx hy hfx hfy
    have hpx : P X := ⟨hx, hfx⟩
    have hpy : P Y := ⟨hy, hfy⟩
    have hm := hmu X Y hpx hpy
    change F.mapDerivedCategory.map (tensorModelIso.{c, v, r} J₀ R A TA X Y hx hy).hom ≫
        mu.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ≫
        B.tensor.map (Prod.mkHom ((Functor.mapDerivedCategoryFactors F).hom.app X)
          ((Functor.mapDerivedCategoryFactors F).hom.app Y)) =
      (Functor.mapDerivedCategoryFactors F).hom.app ((totalTensor.{c, v, r} J₀ R).obj (X, Y)) ≫
        DerivedCategory.Q.map (beta.inv.app (X, Y)) ≫
        (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
          (hH X hpx) (hH Y hpy)).hom at hm
    have hm' := congrArg (fun f ↦ f ≫
      (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).inv ≫
        DerivedCategory.Q.map (beta.hom.app (X, Y))) hm
    have hi : DerivedCategory.Q.map (beta.inv.app (X, Y)) ≫
        DerivedCategory.Q.map (beta.hom.app (X, Y)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← NatTrans.comp_app, beta.inv_hom_id, NatTrans.id_app]
      exact CategoryTheory.Functor.map_id _ _
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at hm'
    rw [hi] at hm'
    have hm'' := hm'.trans (Category.comp_id _)
    have h := inverseChain
      (F.mapDerivedCategory.mapIso
        (tensorModelIso.{c, v, r} J₀ R A TA X Y hx hy))
      (mu.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y))
      (B.tensor.mapIso (Iso.prod ((Functor.mapDerivedCategoryFactors F).app X)
        ((Functor.mapDerivedCategoryFactors F).app Y)))
      (tensorModelIso.{c, v, r} J₁ S B TB (H.obj X) (H.obj Y)
        (hH X hpx) (hH Y hpy)).symm
      (DerivedCategory.Q.map (beta.hom.app (X, Y)))
      ((Functor.mapDerivedCategoryFactors F).hom.app
        ((totalTensor.{c, v, r} J₀ R).obj (X, Y)))
      (by simpa only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
        Iso.symm_hom] using hm'')
    simpa only [H, Functor.mapIso_inv, Iso.prod_inv, Iso.app_inv, Iso.symm_inv] using h

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_eq_sequence (n : ℕ) :
    evaluation.{c, v, max c v r} J B τ n =
      SheafOfModules.systemSequenceEvaluation (rings J B τ) n := by
  unfold evaluation SheafOfModules.systemSequenceEvaluation
  congr 1
  ext U x
  change ((sheafToPresheaf J RingCat.{max c v r}).map
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm)).app U x = x
  rw [eqToHom_map, eqToHom_app]
  rfl

private theorem evaluation_kflat (n : ℕ)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) P)
    (hf : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J
  let : (SheafOfModules.systemSequenceEvaluation (rings J B τ) n).Additive :=
    SheafOfModules.systemSequenceEvaluationAdditive (rings J B τ) n
  let ec := (NatIso.mapHomologicalComplex
    (eqToIso (evaluation_eq_sequence.{c, v, r} J B τ n)) (.up ℤ)).app P
  exact SheafOfModules.kFlat_iso_independent (B n) ec.symm
    (SheafOfModules.systemSequenceEvaluation_preservesKFlat (rings J B τ) n P hP hf).1

private theorem evaluation_map_section (n : ℕ)
    {M N : Systems.{c, v, max c v r} J B τ} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((evaluation.{c, v, max c v r} J B τ n).map f).val.app U
      (evalSection.{c, v, r} J B τ n M U x) =
      evalSection.{c, v, r} J B τ n N U (f.val.app (op (n, U.unop)) x) := rfl

private theorem evaluation_tensor_natural (n : ℕ)
    {M M' N N' : Systems.{c, v, max c v r} J B τ} (f : M ⟶ M') (g : N ⟶ N') :
    (evaluation.{c, v, max c v r} J B τ n).map
        (ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) f g) ≫
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M' N').hom =
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ordinaryTensorHom.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).map f)
        ((evaluation.{c, v, max c v r} J B τ n).map g) := by
  apply (cancel_epi (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply tensor_hom_ext.{c, v, r} J
  intro U x y
  obtain ⟨x, rfl⟩ := evalSection_surjective.{c, v, r} J B τ n M U x
  obtain ⟨y, rfl⟩ := evalSection_surjective.{c, v, r} J B τ n N U y
  change (ordinaryEvaluationTensor.{c, v, r} J B τ n M' N').hom.val.app U
      (((evaluation.{c, v, max c v r} J B τ n).map
        (ordinaryTensorHom.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ)
          f g)).val.app U
          ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U
            (tensorSection.{c, v, r} J (B n) _ _ U
              (evalSection.{c, v, r} J B τ n M U x)
              (evalSection.{c, v, r} J B τ n N U y)))) = _
  rw [evaluation_inv_pure_cast.{c, v, r} J B τ n M N U x y,
    evaluation_map_section.{c, v, r} J B τ n,
    tensorSection_map.{c, v, r} (coefficientSequenceTopology J),
    evaluation_pure_cast.{c, v, r} J B τ n,
    tensorSection_map.{c, v, r} J,
    evaluation_map_section.{c, v, r} J B τ n,
    evaluation_map_section.{c, v, r} J B τ n]

/-- Evaluation of total tensors, with both representative and section normalization. -/
theorem semilinearTensorEvaluation (n : ℕ)
    (closed : Closed.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    (models : Models.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) closed)
    (level : Closed.{c, v, r} J (B n)) (levelModels : Models.{c, v, r} J (B n) level) :
    ∃ (γ : closed.tensor ⋙ e.{c, v, max c v r} J B τ n ≅
        ((e.{c, v, max c v r} J B τ n).prod
          (e.{c, v, max c v r} J B τ n)) ⋙ level.tensor)
      (model : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J) J
        (systemRing.{c, v, max c v r} J B τ) (B n)
        (evaluation.{c, v, max c v r} J B τ n) closed level models levelModels γ),
      ∀ M N : Systems.{c, v, max c v r} J B τ,
        model.ordinary M N = ordinaryEvaluationTensor.{c, v, r} J B τ n M N := by
  let G := WeilConjectures.SequenceModuleEvaluation.coFor J
    (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
    (evaluation_ring J B τ n)
  let adj : evaluation.{c, v, max c v r} J B τ n ⊣ G :=
    WeilConjectures.SequenceModuleEvaluation.coForAdj J
      (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
      (evaluation_ring J B τ n)
  obtain ⟨γ, model, hm⟩ := modelOfOrdinary.{c, v, r}
    (coefficientSequenceTopology J) J (systemRing J B τ) (B n)
    (evaluation.{c, v, max c v r} J B τ n) G adj closed level models levelModels
    (ordinaryEvaluationTensor.{c, v, r} J B τ n)
    (evaluation_tensor_natural.{c, v, r} J B τ n) (evaluation_kflat.{c, v, r} J B τ n)
  exact ⟨γ, model, fun M N ↦ congrFun (congrFun hm M) N⟩

end WeilConjectures.SemilinearSections
