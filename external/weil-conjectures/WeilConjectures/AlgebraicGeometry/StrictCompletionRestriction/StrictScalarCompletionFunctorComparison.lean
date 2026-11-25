/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import Mathlib.CategoryTheory.Localization.Predicate

/-! # StrictScalarCompletionFunctorComparison -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b c d w z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  [HasDerivedCategory.{w} A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
  [HasDerivedCategory.{z} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (S : Presentation A) (T : Presentation B)
  (hscalar : ∀ M : A, F.map (S.scalar.asHom.app M) = T.scalar.asHom.app (F.obj M))

include hscalar in
omit [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem map_scalar_pow (n : ℕ) (M : A) :
    F.map ((S.scalar ^ n).asHom.app M) = (T.scalar ^ n).asHom.app (F.obj M) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, End.mul_asHom, NatTrans.comp_app, Functor.map_comp, ih, hscalar]

omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasCountableProducts B] [HasDerivedCategory B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem cc_coordinates {P : CochainComplex A ℤ} {Q : CochainComplex B ℤ}
    (φ : P ⟶ P) (ψ : Q ⟶ Q) (e : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ Q)
    (h : (F.mapHomologicalComplex (.up ℤ)).map φ ≫ e.hom = e.hom ≫ ψ) (q : ℤ) :
    (CategoryTheory.cc F φ ψ e h).hom.f q ≫
        (principalConeCoordinates ψ q).hom =
      F.map (principalConeCoordinates φ q).hom ≫ F.biprodComparison (P.X q) (P.X (q + 1)) ≫
        biprod.map (e.hom.f q) (e.hom.f (q + 1)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc,
      ← Functor.map_comp_assoc]
    simpa only [principalConeCoordinates, Iso.trans_hom, Category.assoc,
      biprod.braiding_hom, biprod.lift_fst, CategoryTheory.cofiber_snd] using
      CategoryTheory.cc_snd F φ ψ e h q
  · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc,
      ← Functor.map_comp_assoc]
    simpa only [principalConeCoordinates, Iso.trans_hom, Category.assoc,
      biprod.braiding_hom, biprod.lift_snd, HomologicalComplex.homotopyCofiber.fstX] using
      CategoryTheory.cc_fst F φ ψ e h q

omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasCountableProducts B] [HasDerivedCategory B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem transported_cc_coordinates {P : CochainComplex A ℤ}
    {Q : CochainComplex B ℤ} (φ : P ⟶ P) (ψ : Q ⟶ Q)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj P ≅ Q)
    (h : (F.mapHomologicalComplex (.up ℤ)).map φ ≫ e.hom = e.hom ≫ ψ)
    (U : CochainComplex A ℤ) (V : CochainComplex B ℤ)
    (hU : U = CochainComplex.mappingCone φ) (hV : V = CochainComplex.mappingCone ψ)
    (q : ℤ) :
    (((F.mapHomologicalComplex (.up ℤ)).mapIso (eqToIso hU) ≪≫
      CategoryTheory.cc F φ ψ e h ≪≫ (eqToIso hV).symm).hom.f q) ≫
        (eqToIso (congrArg (fun K ↦ K.X q) hV) ≪≫
          principalConeCoordinates ψ q).hom =
      F.map (eqToIso (congrArg (fun K ↦ K.X q) hU) ≪≫
        principalConeCoordinates φ q).hom ≫ F.biprodComparison (P.X q) (P.X (q + 1)) ≫
          biprod.map (e.hom.f q) (e.hom.f (q + 1)) := by
  subst U
  subst V
  simpa using cc_coordinates F φ ψ e h q

private def coneLevel (M : CochainComplex A ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj ((S.tower.obj M).asFunctor.obj (op n)) ≅
      (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor.obj (op n) :=
  (F.mapHomologicalComplex (.up ℤ)).mapIso (eqToIso (S.cone M n)) ≪≫
    CategoryTheory.cc (P := M) (Q := (F.mapHomologicalComplex (.up ℤ)).obj M) F
      ((NatTrans.mapHomologicalComplex (S.scalar ^ (n + 1)).asHom (.up ℤ)).app M)
      ((NatTrans.mapHomologicalComplex (T.scalar ^ (n + 1)).asHom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj M))
      (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        ext q
        exact map_scalar_pow F S T hscalar (n + 1) (M.X q)) ≪≫
    (eqToIso (T.cone ((F.mapHomologicalComplex (.up ℤ)).obj M) n)).symm

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem coneLevel_coordinates (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ) :
    ((coneLevel F S T hscalar M n).hom.f q) ≫
        (T.coordinates ((F.mapHomologicalComplex (.up ℤ)).obj M) n q).hom =
      F.map (S.coordinates M n q).hom ≫ F.biprodComparison (M.X q) (M.X (q + 1)) := by
  rw [S.coordinates_eq, T.coordinates_eq]
  have hc := transported_cc_coordinates (P := M)
    (Q := (F.mapHomologicalComplex (.up ℤ)).obj M) F
    ((NatTrans.mapHomologicalComplex (S.scalar ^ (n + 1)).asHom (.up ℤ)).app M)
    ((NatTrans.mapHomologicalComplex (T.scalar ^ (n + 1)).asHom (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj M)) (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        ext q
        exact map_scalar_pow F S T hscalar (n + 1) (M.X q))
    _ _ (S.cone M n) (T.cone _ n) q
  have hi : biprod.map (𝟙 (F.obj (M.X q))) (𝟙 (F.obj (M.X (q + 1)))) = 𝟙 _ := by
    apply biprod.hom_ext <;> simp
  have hr : biprod.map ((Iso.refl ((F.mapHomologicalComplex (.up ℤ)).obj M)).hom.f q)
      ((Iso.refl ((F.mapHomologicalComplex (.up ℤ)).obj M)).hom.f (q + 1)) = 𝟙 _ := hi
  have hh := congrArg (fun k ↦ F.map (eqToIso
      (congrArg (fun K ↦ K.X q) (S.cone M n)) ≪≫
      principalConeCoordinates
        ((NatTrans.mapHomologicalComplex (S.scalar ^ (n + 1)).asHom (.up ℤ)).app M) q).hom ≫
        F.biprodComparison (M.X q) (M.X (q + 1)) ≫ k) hr
  have hc := hc.trans (hh.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _)))
  exact hc

omit [HasCountableProducts B] [HasDerivedCategory B] in
private theorem biprodMap_comp {P Q R U V W : B}
    (f : P ⟶ Q) (g : R ⟶ U) (h : Q ⟶ V) (k : U ⟶ W) :
    biprod.map (f ≫ h) (g ≫ k) = biprod.map f g ≫ biprod.map h k := by
  apply biprod.hom_ext <;> simp only [Category.assoc, biprod.map_fst,
    biprod.map_snd, biprod.map_fst_assoc, biprod.map_snd_assoc]

omit [HasCountableProducts A] [HasDerivedCategory A]
  [HasCountableProducts B] [HasDerivedCategory B] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem biprodComparison_map {P Q R U : A} (f : P ⟶ Q) (g : R ⟶ U) :
    F.map (biprod.map f g) ≫ F.biprodComparison Q U =
      F.biprodComparison P R ≫ biprod.map (F.map f) (F.map g) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, Functor.biprodComparison_fst, biprod.map_fst,
      Functor.biprodComparison_fst_assoc, ← Functor.map_comp, biprod.map_fst]
  · simp only [Category.assoc, Functor.biprodComparison_snd, biprod.map_snd,
      Functor.biprodComparison_snd_assoc, ← Functor.map_comp, biprod.map_snd]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem coneLevel_step (M : CochainComplex A ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((S.tower.obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op) ≫
      (coneLevel F S T hscalar M n).hom =
    (coneLevel F S T hscalar M (n + 1)).hom ≫
      (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor.map
        (homOfLE (Nat.le_succ n)).op := by
  ext q
  apply (cancel_mono (T.coordinates _ n q).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc, coneLevel_coordinates]
  erw [← F.map_comp_assoc, S.transition, Functor.map_comp, Category.assoc,
    biprodComparison_map, T.transition]
  dsimp only [Functor.mapHomologicalComplex_obj_X, Functor.id_obj]
  erw [← Category.assoc, ← coneLevel_coordinates F S T hscalar]
  erw [F.map_id, hscalar]
  exact Category.assoc _ _ _

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem coneLevel_naturality {M N : CochainComplex A ℤ} (f : M ⟶ N) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (S.tower.map f)).app
        (op n)) ≫ (coneLevel F S T hscalar N n).hom =
    (coneLevel F S T hscalar M n).hom ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (T.tower.map ((F.mapHomologicalComplex (.up ℤ)).map f))).app (op n) := by
  ext q
  apply (cancel_mono (T.coordinates _ n q).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f, Category.assoc]
  change F.map (((S.tower.map f).f q).app (op n)) ≫
    ((coneLevel F S T hscalar N n).hom.f q ≫ (T.coordinates _ n q).hom) =
    (coneLevel F S T hscalar M n).hom.f q ≫
      (((T.tower.map ((F.mapHomologicalComplex (.up ℤ)).map f)).f q).app (op n) ≫
        (T.coordinates _ n q).hom)
  erw [coneLevel_coordinates, ← F.map_comp_assoc, S.diagonal,
    Functor.map_comp, Category.assoc, biprodComparison_map, T.diagonal]
  simp only [← Category.assoc]
  exact congrArg (fun k ↦ k ≫ biprod.map (F.map (f.f q)) (F.map (f.f (q + 1))))
    (coneLevel_coordinates F S T hscalar M n q).symm

private def towerLevelIso (M : CochainComplex A ℤ) :
    ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj
      (S.tower.obj M)).asFunctor ≅
    (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor := by
  let τ :
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj
        (S.tower.obj M)).asFunctor ⟶
      (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor :=
    NatTrans.ofOpSequence
    (fun n ↦ (coneLevel F S T hscalar M n).hom)
    (by intro n; exact coneLevel_step F S T hscalar M n)
  let : ∀ n, IsIso (τ.app n) := fun n ↦
    (coneLevel F S T hscalar M n.unop).isIso_hom
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

private def towerObjectIso (M : CochainComplex A ℤ) :
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj
      (S.tower.obj M) ≅ T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ NatIso.ofComponents
    (fun n ↦ HomologicalComplex.Hom.isoApp ((towerLevelIso F S T hscalar M).app n) q)
    (by
      intro i j f
      exact congrArg (fun g ↦ g.f q)
        ((towerLevelIso F S T hscalar M).hom.naturality f)))
    (by intro i j hij; ext n; exact ((towerLevelIso F S T hscalar M).hom.app n).comm i j)

private def towerComparison : S.tower ⋙
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.tower :=
  NatIso.ofComponents (towerObjectIso F S T hscalar) (by
    intro M N f
    ext q n
    simpa [towerObjectIso, towerLevelIso, HomologicalComplex.comp_f] using
      congrArg (fun g ↦ g.f q) (coneLevel_naturality F S T hscalar f n.unop))

variable (hproducts : ∀ K : ℕ → CochainComplex A ℤ,
  IsIso (piComparison (F.mapHomologicalComplex (.up ℤ)) K))

private def productComparison (M : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (roosP (S.tower.obj M)) ≅
      roosP (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) := by
  let := hproducts (fun n : ℕ ↦ (S.tower.obj M).asFunctor.obj (op n))
  exact asIso (piComparison (F.mapHomologicalComplex (.up ℤ))
    (fun n : ℕ ↦ (S.tower.obj M).asFunctor.obj (op n))) ≪≫
      Pi.mapIso (fun n : ℕ ↦ coneLevel F S T hscalar M n)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem productComparison_projection (M : CochainComplex A ℤ) (n : ℕ) :
    (productComparison F S T hscalar hproducts M).hom ≫
      Pi.π (fun i : ℕ ↦
        (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor.obj (op i)) n =
    (F.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun i : ℕ ↦ (S.tower.obj M).asFunctor.obj (op i)) n) ≫
      (coneLevel F S T hscalar M n).hom := by
  simp only [productComparison, Iso.trans_hom, asIso_hom,
    Category.assoc, Pi.mapIso_hom_π, piComparison_comp_π_assoc]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem productComparison_roos (M : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosU (S.tower.obj M)) ≫
      (productComparison F S T hscalar hproducts M).hom =
    (productComparison F S T hscalar hproducts M).hom ≫
      roosU (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) := by
  apply Pi.hom_ext
  intro n
  simp only [roosU, towerTransitionEndomorphism, towerProductShift,
    Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.comp_id, Category.assoc, Pi.lift_comp_π,
    productComparison_projection]
  simp only [← Functor.map_comp_assoc, Category.id_comp, Pi.lift_comp_π]
  erw [Functor.map_comp, Category.assoc, coneLevel_step]
  simp only [← Category.assoc]
  erw [productComparison_projection F S T hscalar hproducts M (n + 1)]

private def chainObjectIso (M : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj (S.tower.obj M)) ≅
      roosF.obj (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) :=
  CategoryTheory.cs F _ _ (productComparison F S T hscalar hproducts M)
    (productComparison_roos F S T hscalar hproducts M)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem chainObject_coordinates (M : CochainComplex A ℤ) (p : ℤ) :
    (chainObjectIso F S T hscalar hproducts M).hom.f (p + 1) ≫
      (roosχ (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) p).hom =
    F.map (roosχ (S.tower.obj M) p).hom ≫
      F.biprodComparison ((roosP (S.tower.obj M)).X p)
        ((roosP (S.tower.obj M)).X (p + 1)) ≫
      biprod.map ((productComparison F S T hscalar hproducts M).hom.f p)
        ((productComparison F S T hscalar hproducts M).hom.f (p + 1)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc,
      ← Functor.map_comp_assoc]
    simpa only [chainObjectIso, roosχ, Iso.trans_hom, Category.assoc,
      biprod.braiding_hom, biprod.lift_fst, CategoryTheory.cofiber_snd] using
      CategoryTheory.cs_snd F _ _ (productComparison F S T hscalar hproducts M)
        (productComparison_roos F S T hscalar hproducts M) p
  · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc,
      ← Functor.map_comp_assoc]
    simpa only [chainObjectIso, roosχ, Iso.trans_hom, Category.assoc,
      biprod.braiding_hom, biprod.lift_snd, HomologicalComplex.homotopyCofiber.fstX] using
      CategoryTheory.cs_fst F _ _ (productComparison F S T hscalar hproducts M)
        (productComparison_roos F S T hscalar hproducts M) p

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem productComparison_naturality {M N : CochainComplex A ℤ} (f : M ⟶ N) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosPmap (S.tower.map f)) ≫
      (productComparison F S T hscalar hproducts N).hom =
    (productComparison F S T hscalar hproducts M).hom ≫
      roosPmap (T.tower.map ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productComparison_projection, roosPmap, Pi.map_π]
  erw [← Functor.map_comp_assoc, Pi.map_π, Functor.map_comp, Category.assoc,
    coneLevel_naturality]
  simp only [← Category.assoc]
  erw [productComparison_projection F S T hscalar hproducts M n]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem chainObject_naturality {M N : CochainComplex A ℤ} (f : M ⟶ N) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosF.map (S.tower.map f)) ≫
      (chainObjectIso F S T hscalar hproducts N).hom =
    (chainObjectIso F S T hscalar hproducts M).hom ≫
      roosF.map (T.tower.map ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  ext q
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hp
  subst q
  apply (cancel_mono (roosχ (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj N)) p).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc, chainObject_coordinates, roosF_map_χ]
  erw [← F.map_comp_assoc, roosF_map_χ, Functor.map_comp, Category.assoc,
    reassoc_of% (biprodComparison_map F _ _)]
  erw [reassoc_of% (chainObject_coordinates F S T hscalar hproducts M p)]
  have h := productComparison_naturality F S T hscalar hproducts f
  have hp := congrArg (fun k ↦ k.f p) h
  have hq := congrArg (fun k ↦ k.f (p + 1)) h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp hq
  have hb := congrArg₂ biprod.map hp hq
  simp only [biprodMap_comp] at hb
  exact congrArg (fun k ↦ F.map (roosχ (S.tower.obj M) p).hom ≫
    F.biprodComparison _ _ ≫ k) hb

private def chainComparison : S.tower ⋙ roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.tower ⋙ roosF :=
  NatIso.ofComponents (chainObjectIso F S T hscalar hproducts)
    (fun f ↦ chainObject_naturality F S T hscalar hproducts f)

private theorem augmentation_level_coordinates (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ) :
    ((S.augmentation.app M ≫ roosEval (S.tower.obj M) n).f q) ≫
      (S.coordinates M n q).hom = biprod.inl := by
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hp
  subst q
  simpa only [HomologicalComplex.comp_f, roosEval_f, Category.assoc] using
    S.augmentation_level M n p

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem augmentation_coneLevel (M : CochainComplex A ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map
      (S.augmentation.app M ≫ roosEval (S.tower.obj M) n) ≫
        (coneLevel F S T hscalar M n).hom =
    T.augmentation.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
      roosEval (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) n := by
  ext q
  apply (cancel_mono (T.coordinates _ n q).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
  rw [coneLevel_coordinates]
  erw [← F.map_comp_assoc, augmentation_level_coordinates]
  have ht := augmentation_level_coordinates T ((F.mapHomologicalComplex (.up ℤ)).obj M) n q
  simp only [HomologicalComplex.comp_f, Category.assoc] at ht
  erw [ht]
  apply biprod.hom_ext
  · erw [Category.assoc, Functor.biprodComparison_fst, ← F.map_comp, biprod.inl_fst, F.map_id]
    exact (biprod.inl_fst).symm
  · erw [Category.assoc, Functor.biprodComparison_snd, ← F.map_comp, biprod.inl_snd, F.map_zero]
    exact (biprod.inl_snd).symm

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem chainObject_unit (M : CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (S.augmentation.app M) ≫
      (chainObjectIso F S T hscalar hproducts M).hom =
    T.augmentation.app ((F.mapHomologicalComplex (.up ℤ)).obj M) := by
  ext q
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
  change p + 1 = q at hp
  subst q
  apply (cancel_mono (roosχ (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) p).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
  rw [chainObject_coordinates]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc,
      ← F.map_comp_assoc]
    erw [S.augmentation_zero, F.map_zero, zero_comp,
      T.augmentation_zero]
  · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc]
    apply CategoryTheory.product_component_ext _ (p + 1)
    intro n
    have hp := congrArg (fun k ↦ k.f (p + 1))
      (productComparison_projection F S T hscalar hproducts M n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
    simp only [Category.assoc]
    erw [hp]
    simp only [← F.map_comp_assoc]
    have ha := congrArg (fun k ↦ k.f (p + 1)) (augmentation_coneLevel F S T hscalar M n)
    simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      roosEval_f, Category.assoc, Functor.map_comp] using ha

private theorem descendIso {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (G H : D ⥤ E) (e : L ⋙ G ≅ L ⋙ H) :
    ∃ t : G ≅ H, ∀ X, t.hom.app (L.obj X) = e.hom.app X := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W E
  refine ⟨ff.preimageIso e, ?_⟩
  intro X
  exact congr_app (ff.map_preimage e.hom) X

include hscalar hproducts in
private theorem completionDescent :
    ∃ δ : S.completion ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T.completion,
      ∀ M : CochainComplex A ℤ,
        δ.hom.app (DerivedCategory.Q.obj M) ≫
          T.completion.map (F.mapDerivedCategoryFactors.hom.app M) ≫
          T.descent.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
        F.mapDerivedCategory.map (S.descent.hom.app M) ≫
          F.mapDerivedCategoryFactors.hom.app (roosF.obj (S.tower.obj M)) ≫
          DerivedCategory.Q.map ((chainComparison F S T hscalar hproducts).hom.app M) := by
  let e : DerivedCategory.Q ⋙ (S.completion ⋙ F.mapDerivedCategory) ≅
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ T.completion) :=
    Functor.isoWhiskerRight S.descent F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (S.tower ⋙ roosF) F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (chainComparison F S T hscalar hproducts) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) T.descent.symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm T.completion
  obtain ⟨δ, hδ⟩ := descendIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ e
  refine ⟨δ, ?_⟩
  intro M
  rw [hδ]
  dsimp only [e, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Iso.symm_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [T.completion.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl

private def coneComparison (n : ℕ) :
    S.tower ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
      F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.tower ⋙
      ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun M ↦ coneLevel F S T hscalar M n)
    (fun f ↦ coneLevel_naturality F S T hscalar f n)

include hscalar in
private theorem reductionDescent (n : ℕ) :
    ∃ δ : S.reduction n ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T.reduction n,
      ∀ M : CochainComplex A ℤ,
        δ.hom.app (DerivedCategory.Q.obj M) ≫
          (T.reduction n).map (F.mapDerivedCategoryFactors.hom.app M) ≫
          (T.reduction_descent n).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
        F.mapDerivedCategory.map ((S.reduction_descent n).hom.app M) ≫
          F.mapDerivedCategoryFactors.hom.app ((S.tower.obj M).asFunctor.obj (op n)) ≫
          DerivedCategory.Q.map (coneLevel F S T hscalar M n).hom := by
  let e : DerivedCategory.Q ⋙ (S.reduction n ⋙ F.mapDerivedCategory) ≅
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ T.reduction n) :=
    Functor.isoWhiskerRight (S.reduction_descent n) F.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft
        (S.tower ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ))
        F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (coneComparison F S T hscalar n) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (T.reduction_descent n).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm (T.reduction n)
  obtain ⟨δ, hδ⟩ := descendIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ e
  refine ⟨δ, ?_⟩
  intro M
  rw [hδ]
  dsimp only [e, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Iso.symm_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(T.reduction n).map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem unit_of_representative
    (C : DerivedCategory A ⥤ DerivedCategory A)
    (D : DerivedCategory B ⥤ DerivedCategory B)
    (s : 𝟭 _ ⟶ C) (t : 𝟭 _ ⟶ D)
    (U : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (V : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (sa : ∀ M, M ⟶ U.obj M) (ta : ∀ M, M ⟶ V.obj M)
    (sc : DerivedCategory.Q ⋙ C ≅ U ⋙ DerivedCategory.Q)
    (tc : DerivedCategory.Q ⋙ D ≅ V ⋙ DerivedCategory.Q)
    (su : ∀ M, s.app (DerivedCategory.Q.obj M) ≫ sc.hom.app M =
      DerivedCategory.Q.map (sa M))
    (tu : ∀ M, t.app (DerivedCategory.Q.obj M) ≫ tc.hom.app M =
      DerivedCategory.Q.map (ta M))
    (e : U ⋙ F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙ V)
    (eu : ∀ M, (F.mapHomologicalComplex (.up ℤ)).map (sa M) ≫ e.hom.app M =
      ta ((F.mapHomologicalComplex (.up ℤ)).obj M))
    (δ : C ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ D)
    (hδ : ∀ M, δ.hom.app (DerivedCategory.Q.obj M) ≫
      D.map (F.mapDerivedCategoryFactors.hom.app M) ≫
      tc.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F.mapDerivedCategory.map (sc.hom.app M) ≫
      F.mapDerivedCategoryFactors.hom.app (U.obj M) ≫ DerivedCategory.Q.map (e.hom.app M)) :
    ∀ K, F.mapDerivedCategory.map (s.app K) ≫ δ.hom.app K =
      t.app (F.mapDerivedCategory.obj K) := by
  have he : Functor.whiskerRight s F.mapDerivedCategory ≫ δ.hom =
      Functor.whiskerLeft F.mapDerivedCategory t := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro M
    change F.mapDerivedCategory.map (s.app (DerivedCategory.Q.obj M)) ≫
      δ.hom.app (DerivedCategory.Q.obj M) = t.app _
    apply (cancel_mono (D.map (F.mapDerivedCategoryFactors.hom.app M))).mp
    apply (cancel_mono (tc.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M))).mp
    simp only [Category.assoc, hδ]
    erw [← F.mapDerivedCategory.map_comp_assoc, su]
    have hn := F.mapDerivedCategoryFactors.hom.naturality (sa M)
    dsimp only [Functor.comp_map] at hn
    erw [← Category.assoc, hn, Category.assoc, ← DerivedCategory.Q.map_comp, eu]
    have ht := t.naturality (F.mapDerivedCategoryFactors.hom.app M)
    dsimp only [Functor.id_map, Functor.comp_map] at ht
    erw [← Category.assoc, ← ht, Category.assoc, tu]
  intro K
  exact congr_app he K

private theorem reductionTransition
    (δ : ∀ n, S.reduction n ⋙ F.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ T.reduction n)
    (hδ : ∀ n M, (δ n).hom.app (DerivedCategory.Q.obj M) ≫
      (T.reduction n).map (F.mapDerivedCategoryFactors.hom.app M) ≫
      (T.reduction_descent n).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F.mapDerivedCategory.map ((S.reduction_descent n).hom.app M) ≫
      F.mapDerivedCategoryFactors.hom.app ((S.tower.obj M).asFunctor.obj (op n)) ≫
      DerivedCategory.Q.map (coneLevel F S T hscalar M n).hom) (n : ℕ) :
    ∀ K, F.mapDerivedCategory.map ((S.reduction_step n).app K) ≫ (δ n).hom.app K =
      (δ (n + 1)).hom.app K ≫ (T.reduction_step n).app (F.mapDerivedCategory.obj K) := by
  have he : Functor.whiskerRight (S.reduction_step n) F.mapDerivedCategory ≫ (δ n).hom =
      (δ (n + 1)).hom ≫ Functor.whiskerLeft F.mapDerivedCategory (T.reduction_step n) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro M
    change F.mapDerivedCategory.map ((S.reduction_step n).app (DerivedCategory.Q.obj M)) ≫
      (δ n).hom.app (DerivedCategory.Q.obj M) =
      (δ (n + 1)).hom.app (DerivedCategory.Q.obj M) ≫ (T.reduction_step n).app _
    apply (cancel_mono ((T.reduction n).map (F.mapDerivedCategoryFactors.hom.app M))).mp
    apply (cancel_mono ((T.reduction_descent n).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj M))).mp
    simp only [Category.assoc, hδ]
    erw [← F.mapDerivedCategory.map_comp_assoc, S.reduction_step_descent,
      F.mapDerivedCategory.map_comp, Category.assoc]
    have ht := (T.reduction_step n).naturality (F.mapDerivedCategoryFactors.hom.app M)
    erw [← Category.assoc ((T.reduction_step n).app _) _ _, ← ht, Category.assoc,
      T.reduction_step_descent]
    erw [reassoc_of% (hδ (n + 1) M)]
    have hn := F.mapDerivedCategoryFactors.hom.naturality
      ((S.tower.obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    have hc := congrArg (fun f ↦ DerivedCategory.Q.map f)
      (coneLevel_step F S T hscalar M n)
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at hc
    exact congrArg (fun f ↦ F.mapDerivedCategory.map
      ((S.reduction_descent (n + 1)).hom.app M) ≫
      F.mapDerivedCategoryFactors.hom.app ((S.tower.obj M).asFunctor.obj (op (n + 1))) ≫ f) hc
  intro K
  exact congr_app he K

include hscalar hproducts in
/-- The strict scalar-cone tower, its augmented Roos complex and their derived descents
commute with an exact additive functor preserving countable products and the scalar.

Source: Stacks Tags 014E, 08TC and 015F; blueprint Locality and Cones paragraphs
(blueprint: lem-sfb-strict-scalar-completion-functor-comparison).

Proof: Map the scalar powers and use the canonical mapping-cone comparison.
The two biproduct projections show naturality and compatibility with the successor
transition. Apply the product comparison followed by the product of the cone maps;
its projections identify the Roos endomorphism 1-T. The shifted-cone comparison is
diagonal in these product coordinates. The zero coordinate and every level of the
augmentation agree. Fully faithful precomposition by derived localization descends
the level and Roos isomorphisms. Naturality and the representative equations then
identify all reduction transitions and units, and the completion unit. -/
theorem strictScalarCompletionFunctorComparison : Nonempty (Comparison F S T) := by
  classical
  choose δ hδ using reductionDescent F S T hscalar
  obtain ⟨ε, hε⟩ := completionDescent F S T hscalar hproducts
  refine ⟨{
    homology := F.mapDerivedCategoryHomologyFunctorIso
    homology_eq := fun _ ↦ rfl
    scalar := hscalar
    tower := towerComparison F S T hscalar
    tower_coordinates := ?_
    product := productComparison F S T hscalar hproducts
    product_projection := ?_
    roos_map := productComparison_roos F S T hscalar hproducts
    chain := chainComparison F S T hscalar hproducts
    chain_coordinates := chainObject_coordinates F S T hscalar hproducts
    chain_unit := chainObject_unit F S T hscalar hproducts
    reduction := δ
    reduction_representative := ?_
    reduction_transition := reductionTransition F S T hscalar δ hδ
    reduction_augmentation := ?_
    derived := ε
    representative := hε
    unit := ?_ }⟩
  · intro M n q
    exact coneLevel_coordinates F S T hscalar M n q
  · intro M n q
    exact congrArg (fun k ↦ k.f q)
      (productComparison_projection F S T hscalar hproducts M n)
  · intro n M
    exact hδ n M
  · intro n
    exact unit_of_representative F (S.reduction n) (T.reduction n)
      (S.reduction_unit n) (T.reduction_unit n)
      (S.tower ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ))
      (T.tower ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ))
      (fun M ↦ S.augmentation.app M ≫ roosEval (S.tower.obj M) n)
      (fun M ↦ T.augmentation.app M ≫ roosEval (T.tower.obj M) n)
      (S.reduction_descent n) (T.reduction_descent n)
      (S.reduction_unit_descent n) (T.reduction_unit_descent n)
      (coneComparison F S T hscalar n) (fun M ↦ augmentation_coneLevel F S T hscalar M n)
      (δ n) (hδ n)
  · exact unit_of_representative F S.completion T.completion S.unit T.unit
      (S.tower ⋙ roosF) (T.tower ⋙ roosF) S.augmentation.app T.augmentation.app
      S.descent T.descent S.unit_descent T.unit_descent
      (chainComparison F S T hscalar hproducts)
      (chainObject_unit F S T hscalar hproducts) ε hε

end
end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
