/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.ConstantToContinuousScalarFlat
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolution

/-!
# Two-term resolutions of finite constant scalar models

Source: Bhatt--Scholze, Proposition 6.8.11(3), Lemma 6.8.2(1); Stacks Tags 093J,
093M (blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).

The model functor first forms discrete constant modules, extends scalars by the map
sending a scalar to the constant continuous function, and applies the monoidal inverse
image from the point. Thus it is precisely B_T tensor over the discrete constant A,
not a tensor over the continuous coefficient ring on the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

variable (A : Type u) [CommRing A]

variable [TopologicalSpace A] [IsTopologicalRing A]

attribute [instance] scalarToContinuous_isMonHom

set_option linter.unusedSectionVars false in
attribute [instance] constantScalars_commutative

end AlgebraicGeometry.ProEtale.FiniteConstantModel

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

universe uC vC

/-- A scalar short exact sequence, its specified scalar-extended short exact sequence,
and the augmented complex in degrees minus one and zero. The component equations
fix the differential and augmentation to the images of the original scalar maps.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def HasResolution {A : Type u} [CommRing A] {C : Type uC} [Category.{vC} C] [Abelian C]
    (F : ModuleCat.{u + 1} A ⥤ C) (free : ℕ → C) (P : ModuleCat.{u + 1} A)
    (rational : Bool) : Prop :=
  ∃ (a b : ℕ) (f : freeScalars A a ⟶ freeScalars A b)
      (g : freeScalars A b ⟶ P),
    (rational = true → a = 0) ∧ Function.Injective f.hom ∧
    Function.Exact f.hom g.hom ∧ Function.Surjective g.hom ∧
    Nonempty (F.obj (freeScalars A a) ≅ free a) ∧
    Nonempty (F.obj (freeScalars A b) ≅ free b) ∧
    (rational = true → Nonempty (F.obj P ≅ free b)) ∧
    ∃ h : F.map f ≫ F.map g = 0,
      (ShortComplex.mk (F.map f) (F.map g) h).ShortExact ∧
      ∃ (K : CochainComplex C ℤ)
        (e₁ : K.X (-1) ≅ F.obj (freeScalars A a))
        (e₀ : K.X 0 ≅ F.obj (freeScalars A b))
        (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj (F.obj P)),
        (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) ∧
        K.d (-1) 0 = e₁.hom ≫ F.map f ≫ e₀.inv ∧
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj P)).hom =
          e₀.hom ≫ F.map g ∧ QuasiIso ε

private def freeCoordinates (A : Type u) [CommRing A] (n : ℕ) :
    (Fin n → ULift.{u + 1} A) ≃ₗ[A] (Fin n → A) :=
  LinearEquiv.piCongrRight (fun _ ↦ ULift.moduleEquiv)

private lemma finiteFree_coordinates (A : Type u) [CommRing A]
    (M : Type (u + 1)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M] :
    ∃ n : ℕ, Nonempty ((Fin n → ULift.{u + 1} A) ≃ₗ[A] M) := by
  classical
  let B := Module.Free.chooseBasis A M
  let ι := Module.Free.ChooseBasisIndex A M
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let B' := B.reindex e
  exact ⟨Fintype.card ι, ⟨(freeCoordinates A _).trans B'.equivFun.symm⟩⟩

private lemma scalar_resolution (A : Type u) [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] (P : ModuleCat.{u + 1} A)
    [Module.FinitePresentation A P] :
    ∃ (a b : ℕ) (f : freeScalars A a ⟶ freeScalars A b)
      (g : freeScalars A b ⟶ P),
      Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧
      Function.Surjective g.hom := by
  obtain ⟨b, s, v, w, hv, hw⟩ := Module.FinitePresentation.exists_fin' A P
  let v' : (Fin b → ULift.{u + 1} A) →ₗ[A] P :=
    v.comp (freeCoordinates A b).toLinearMap
  have hv' : Function.Surjective v' := hv.comp (freeCoordinates A b).surjective
  let K := LinearMap.ker v'
  have : Module.Finite A K := inferInstance
  have : Module.Free A K := inferInstance
  obtain ⟨a, ⟨e⟩⟩ := finiteFree_coordinates A K
  let f : freeScalars A a ⟶ freeScalars A b :=
    ModuleCat.ofHom (K.subtype.comp e.toLinearMap)
  let g : freeScalars A b ⟶ P := ModuleCat.ofHom v'
  refine ⟨a, b, f, g, K.injective_subtype.comp e.injective, ?_, hv'⟩
  intro x
  change v' x = 0 ↔ ∃ y, K.subtype (e y) = x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact (e y).property

private lemma field_scalar_sequence (A : Type u) [Field A] (P : ModuleCat.{u + 1} A)
    [Module.FinitePresentation A P] :
    ∃ (b : ℕ) (f : freeScalars A 0 ⟶ freeScalars A b)
      (g : freeScalars A b ≅ P),
      Function.Injective f.hom ∧ Function.Exact f.hom g.hom.hom ∧
      Function.Surjective g.hom.hom := by
  obtain ⟨b, ⟨e⟩⟩ := finiteFree_coordinates A P
  let g : freeScalars A b ≅ P := e.toModuleIso
  refine ⟨b, 0, g, ?_, ?_, e.surjective⟩
  · exact fun x y _ ↦ funext (fun i ↦ Fin.elim0 i)
  · intro x
    change e x = 0 ↔ ∃ y : Fin 0 → ULift.{u + 1} A, (0 : Fin b → ULift.{u + 1} A) = x
    constructor
    · intro hx
      exact ⟨0, (e.injective (hx.trans e.map_zero.symm)).symm⟩
    · rintro ⟨y, rfl⟩
      exact e.map_zero

section FreeModels

variable (A : Type u) [CommRing A]

private lemma scalarModules_additive : (scalarModules A).Additive where
  map_add := by intros; rfl

private def scalarRegularIso :
    (scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A)) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} A)) :=
  Mod.isoMk (Iso.refl _) (by
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    rfl)

private def scalarFiniteFreeIso (n : ℕ) :
    (scalarModules A).obj (freeScalars A n) ≅
      Mod.finiteFree (AddCommGrpCat.of (ULift.{u + 1} A)) n := by
  have : (scalarModules A).Additive := scalarModules_additive A
  exact (scalarModules A).mapIso
      (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of A (ULift.{u + 1} A))).symm ≪≫
    (scalarModules A).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ scalarRegularIso A)

private def mapFiniteFreeIso
    {C D : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
    [Category* D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] (R : C) [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)]
    [PreservesFiniteColimits (tensorLeft (F.obj R))] (n : ℕ) :
    (F.mapMod R).obj (Mod.finiteFree R n) ≅ Mod.finiteFree (F.obj R) n := by
  have : (F.mapMod R).Additive :=
    { map_add := by intros; apply Mod.hom_ext; exact F.map_add }
  exact (F.mapMod R).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦
    Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
      whiskerLeft_id, Category.id_comp]))

private lemma scalarModules_preservesFiniteLimits :
    PreservesFiniteLimits (scalarModules A) := by
  have : PreservesFiniteLimits (scalarModules A ⋙
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    inferInstanceAs (PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A)))

private lemma scalarModules_preservesFiniteColimits :
    PreservesFiniteColimits (scalarModules A) := by
  let V : ModuleCat.{u + 1} A ⥤ Ab.{u + 1} := forget₂ _ _
  have : PreservesColimitsOfSize.{0, 0} V := by
    exact ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, 0, 0} A
  have : PreservesFiniteColimits V := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (scalarModules A ⋙
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    inferInstanceAs (PreservesFiniteColimits V)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A)))

variable [TopologicalSpace A] [IsTopologicalRing A]

private lemma modelFunctor_exact (T : Scheme.{u})
    (hflat : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A))) :
    PreservesFiniteLimits (modelFunctor A T) ∧
      PreservesFiniteColimits (modelFunctor A T) ∧ (modelFunctor A T).Additive := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesFiniteLimits (scalarModules A) := scalarModules_preservesFiniteLimits A
  have : PreservesFiniteColimits (scalarModules A) := scalarModules_preservesFiniteColimits A
  have : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A)) := hflat
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A))) := by
    infer_instance
  have : PreservesFiniteLimits
      ((upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj A)) := by
    infer_instance
  have hlim : PreservesFiniteLimits (modelFunctor A T) := by
    unfold modelFunctor
    infer_instance
  have hcolim : PreservesFiniteColimits (modelFunctor A T) := by
    dsimp [modelFunctor]
    infer_instance
  exact ⟨hlim, hcolim, rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)⟩

private lemma modelFiniteFree (T : Scheme.{u}) (n : ℕ) :
    Nonempty ((modelFunctor A T).obj (freeScalars A n) ≅
      Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) n) := by
  let R := AddCommGrpCat.of (ULift.{u + 1} A)
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let φ := scalarToContinuous A
  let G := (upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj A)
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesBinaryBiproducts (upperStarFromPoint T) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint T).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : G.Additive :=
    { map_add := by intros; apply Mod.hom_ext; exact (upperStarFromPoint T).map_add }
  have : (Mod.extendScalars φ).Additive := inferInstance
  let e := (F.mapMod R).mapIso (scalarFiniteFreeIso A n) ≪≫ mapFiniteFreeIso F R n
  let e' := (Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalars φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular (F.obj R)) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso φ)
  exact ⟨G.mapIso e' ≪≫ mapFiniteFreeIso (upperStarFromPoint T) _ n⟩

end FreeModels

private lemma shortExact_resolution {C : Type uC} [Category.{vC} C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ (K : CochainComplex C ℤ)
      (e₁ : K.X (-1) ≅ S.X₁) (e₀ : K.X 0 ≅ S.X₂)
      (ε : K ⟶ (CochainComplex.singleFunctor C 0).obj S.X₃),
      (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) ∧
      K.d (-1) 0 = e₁.hom ≫ S.f ≫ e₀.inv ∧
      ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).hom =
        e₀.hom ≫ S.g ∧ QuasiIso ε := by
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let K : CochainComplex C ℤ := HomologicalComplex.double S.f hrel
  let e₁ : K.X (-1) ≅ S.X₁ := HomologicalComplex.doubleXIso₀ S.f hrel
  let e₀ : K.X 0 ≅ S.X₂ := HomologicalComplex.doubleXIso₁ S.f hrel (by decide)
  let L := (CochainComplex.singleFunctor C 0).obj S.X₃
  let e : L.X 0 ≅ S.X₃ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃
  let ε : K ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by decide)
    (0 : S.X₁ ⟶ L.X (-1)) (S.g ≫ e.inv)
    (by simp) (by intros; simp [L])
  have hK (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X S.f hrel i h₁ h₀
  have hd : K.d (-1) 0 = e₁.hom ≫ S.f ≫ e₀.inv :=
    HomologicalComplex.double_d S.f hrel (by decide)
  have hε : ε.f 0 = e₀.hom ≫ S.g ≫ e.inv := by
    dsimp [ε]
    simp only [HomologicalComplex.mkHomFromDouble_f₁]
    rfl
  refine ⟨K, e₁, e₀, ε, hK, hd, ?_, ?_⟩
  · rw [hε]
    simp [e]
  · have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₃ i hi
    have hmono : Mono (K.d (-1) 0) := by
      have := hS.mono_f
      rw [hd]
      infer_instance
    have hepi : Epi (ε.f 0) := by
      have := hS.epi_g
      rw [hε]
      infer_instance
    have hw : K.d (-1) 0 ≫ ε.f 0 = 0 := by
      rw [hd, hε]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [S.zero_assoc]
      simp
    let S' := ShortComplex.mk (K.d (-1) 0) (ε.f 0) hw
    let φ : S ⟶ S' :=
      { τ₁ := e₁.inv
        τ₂ := e₀.inv
        τ₃ := e.inv
        comm₁₂ := by dsimp [S']; rw [hd]; simp
        comm₂₃ := by dsimp [S']; rw [hε]; simp }
    have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
    have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
    have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
    have hex : S'.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS.exact
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hK 1 (by decide) (by decide)).eq_of_tgt _ _)
        ((hL (-1) (by decide)).eq_of_src _ _)
        ((hL 1 (by decide)).eq_of_tgt _ _)).2
      exact ⟨hex, hepi⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hi' : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _
          ((hK (-2) (by decide) (by decide)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hK i hi' hi)

private lemma resolution_of_scalar_sequence {A : Type u} [CommRing A]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (F : ModuleCat.{u + 1} A ⥤ C) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (free : ℕ → C) (hfree : ∀ n, Nonempty (F.obj (freeScalars A n) ≅ free n))
    (P : ModuleCat.{u + 1} A) (rational : Bool)
    (a b : ℕ) (f : freeScalars A a ⟶ freeScalars A b)
    (g : freeScalars A b ⟶ P) (ha : rational = true → a = 0)
    (hf : Function.Injective f.hom) (hex : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom)
    (hr : rational = true → Nonempty (F.obj P ≅ free b)) :
    HasResolution F free P rational := by
  have hw : f ≫ g = 0 := by
    ext x
    exact (hex (f.hom x)).2 ⟨x, rfl⟩
  let S := ShortComplex.mk f g hw
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
      mono_f := (ModuleCat.mono_iff_injective f).2 hf
      epi_g := (ModuleCat.epi_iff_surjective g).2 hg }
  have hSF := hS.map_of_exact F
  refine ⟨a, b, f, g, ha, hf, hex, hg, hfree a, hfree b, hr,
    (S.map F).zero, hSF, ?_⟩
  exact shortExact_resolution (S.map F) hSF

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The continuous integral condensed ring with the specified extension absolute value.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(1)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
abbrev integralCoefficients :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)

/-- The continuous rational condensed ring with the specified extension absolute value.
Source: Bhatt--Scholze, Definition 6.8.1
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
abbrev rationalCoefficients :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingObj E

/-- Constant integral scalar modules extended to the actual pulled-back condensed ring.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def integralModel (T : Scheme.{u}) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (integralCoefficients l E) T) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  modelFunctor (Padic.coefficientExtensionIntegers l E) T

/-- Constant rational scalar modules extended to the actual pulled-back condensed ring.
Source: Bhatt--Scholze, Proposition 6.8.11(3), field case
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution). -/
def rationalModel (T : Scheme.{u}) :
    ModuleCat.{u + 1} E ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (rationalCoefficients l E) T) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  modelFunctor E T

/-- Finite constant local models have length-one finite-free resolutions; over E the
negative-degree free term can be zero. No condition is placed on the scheme or on
scalar torsion, and all complexes are ordinary cochain complexes of module sheaves.

Source: Bhatt--Scholze, Proposition 6.8.11(3), with Lemma 6.8.2(1); Stacks 093J, 093M
(blueprint: lem-sfb-finite-constant-model-two-term-free-resolution).

Proof:
1. In the integral case take a finite presentation and its finitely generated kernel.
The kernel is torsion-free as a submodule of a finite free module over the domain O_E.
The DVR theorem lem-weil-l-adic-extension-integers-dvr and
lem-sc-dvr-fg-torsionfree-free make it finite free, giving the scalar short exact sequence.
2. In the field case a finite spanning set contains a basis; take a=0 and let the final
scalar map be that basis isomorphism, including the empty basis for the zero module.
3. By lem-weil-pbc-site-r-module-presheaf-sheafification-exact the constant sheaf
functor preserves this exact sequence, and also identifies finite scalar powers with
finite powers of the constant ring. The scalar map is constant continuous functions.
4. Relative tensor identifies B tensor A^n with B^n: send z tensor (x_i) to (zx_i),
and use (z_i) to sum z_i tensor e_i for its inverse. These maps identify the scalar
extended differentials with the given matrices, including n=0.
5. For integral coefficients, lem-weil-pbc-pid-noetherian-normal makes O_E Noetherian.
The canonical A-algebra comparison lemma-comparison-completed-coefficients--1 identifies
B with the limit of the constant A/(pi^n). Its projections send constant scalars to
their residues, so lem-weil-pbc-completed-constant-sheaf-reduction (Stacks 093M)
preserves the constant short exact sequence under scalar extension. In the field case
the scalar basis isomorphism stays an isomorphism after both functors; no flatness
assertion for the discrete constant E is needed.
6. Form the two-term complex in degrees -1,0 with the specified differential and
augmentation. Exactness gives zero H^-1 and identifies H^0 with the final model by
that augmentation. Other cohomology vanishes, so precisely this augmentation is a
quasi-isomorphism. No completed derived category enters this argument. -/
theorem finite_constant_model_two_term_free_resolution
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (∀ (P : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      [Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) P],
      HasResolution (integralModel l E T)
        (Mod.finiteFree (condensedRingObj (integralCoefficients l E) T)) P false) ∧
    (∀ (P : ModuleCat.{u + 1} E) [Module.FinitePresentation E P],
      HasResolution (rationalModel l E T)
        (Mod.finiteFree (condensedRingObj (rationalCoefficients l E) T)) P true) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.1
  have hexact (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
      [TopologicalSpace A] [IsTopologicalRing A] :
      PreservesFiniteLimits (modelFunctor A T) ∧
        PreservesFiniteColimits (modelFunctor A T) ∧ (modelFunctor A T).Additive := by
    apply modelFunctor_exact A T
    apply constantToContinuous_preservesFiniteLimits A (scalarToContinuous A)
    intro S a
    have h := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
      (Profinite.continuousCoefficientRingObj A)).apply_symm_apply (constantFunctions A)
    exact ConcreteCategory.congr_hom (congr_app h S) a
  constructor
  · intro P hP
    let := hpid
    obtain ⟨hlim, hcolim, hadd⟩ := hexact (Padic.coefficientExtensionIntegers l E)
    let := hlim
    let := hcolim
    let := hadd
    obtain ⟨a, b, f, g, hf, hfg, hg⟩ :=
      scalar_resolution (Padic.coefficientExtensionIntegers l E) P
    exact resolution_of_scalar_sequence
      (modelFunctor (Padic.coefficientExtensionIntegers l E) T) _
      (modelFiniteFree (Padic.coefficientExtensionIntegers l E) T) P false a b f g
      (by simp) hf hfg hg (by simp)
  · intro P hP
    obtain ⟨hlim, hcolim, hadd⟩ := hexact E
    let := hlim
    let := hcolim
    let := hadd
    obtain ⟨b, f, g, hf, hfg, hg⟩ := field_scalar_sequence E P
    exact resolution_of_scalar_sequence (modelFunctor E T) _
      (modelFiniteFree E T) P true 0 b f g.hom (by simp) hf hfg hg
      (fun _ ↦ ⟨((rationalModel l E T).mapIso g).symm ≪≫ (modelFiniteFree E T b).some⟩)

end AlgebraicGeometry.ProEtale.FiniteConstantModel
