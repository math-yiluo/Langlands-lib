/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors
import WeilConjectures.AlgebraicGeometry.CompositeModuleOplaxMate
import WeilConjectures.AlgebraicGeometry.InternalDirectImageLaxRealization
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Ordinary pullback on balanced generators

Source: Stacks Project, Modules on Sites, Tags 03D7, 03EK and 03EL
(auxiliary; not a blueprint node).

The generators below are applications of the existing relative-tensor projections.
In particular, inverse-image sections range over every object of the source site;
they are not restricted to global sections or sections pulled from the target.
The scalar formulas characterize the normalized canonical ringed comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace CategoryTheory.InternalAbelianSheafModule
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
set_option hygiene false in
local notation "E" => sectionModuleFunctor J R
set_option hygiene false in
local notation "IM" => Mod (Sheaf J AddCommGrpCat.{u}) R
set_option hygiene false in
local notation "SM" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf J R))

private theorem sectionIso_injective {M N : SM} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Injective (e.hom.val.app U) := by
  have hi (x : M.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x :=
    congrArg (fun k ↦ (k.val.app U) x) e.hom_inv_id
  intro x y h
  exact (hi x).symm.trans ((congrArg (e.inv.val.app U) h).trans (hi y))

private theorem tensor_smul (M N : IM) (U : Cᵒᵖ)
    (s t : (sectionRingSheaf J R).obj.obj U)
    (m : ((E).obj M).val.obj U) (n : ((E).obj N).val.obj U) :
    comparison_internalTmul J R M N U (s • m) (t • n) =
      @SMul.smul _ _ (ModuleCat.isModule (((E).obj (M ⊗ N)).val.obj U)).toSMul
        (s * t) (comparison_internalTmul J R M N U m n) := by
  let e := comparison_tensorIso J R M N
  apply sectionIso_injective J R e U
  erw [comparison_tensorIso_tmul, map_smul, comparison_tensorIso_tmul]
  unfold comparison_sectionTmul
  simp only [TensorProduct.smul_tmul_smul, map_smul]

section Scalar
variable (A : Sheaf J AddCommGrpCat.{u}) [MonObj A] [IsCommMonObj A]
  (φ : A ⟶ R) [IsMonHom φ]

private def scalarSection (M : Mod (Sheaf J AddCommGrpCat.{u}) A)
    (U : Cᵒᵖ) (s : (sectionRingSheaf J R).obj.obj U) (m : M.X.obj.obj U) :=
  ((Mod.extendπ φ M).hom.app U)
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u}) R M.X).app U
      (s ⊗ₜ[ℤ] m))

private theorem scalarSection_smul (M : Mod (Sheaf J AddCommGrpCat.{u}) A)
    (U : Cᵒᵖ) (s : (sectionRingSheaf J R).obj.obj U) (m : M.X.obj.obj U) :
    scalarSection J R A φ M U s m =
      @SMul.smul _ _ (ModuleCat.isModule
        (((E).obj ((Mod.extendScalars φ).obj M)).val.obj U)).toSMul s
          ((Mod.extendUnitHom φ M).hom.app U m) := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ F R M.X ≫ F.map k)
    (Mod.whiskerLeft_extendUnitHom_smul' φ M)
  simp only [Functor.map_comp] at h
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at h
  exact (congrArg (fun k ↦ (k.app U) (s ⊗ₜ[ℤ] m)) h).symm

private theorem scalarSection_inverse (M N P : Mod (Sheaf J AddCommGrpCat.{u}) A)
    (d : (Mod.extendScalars φ).obj P ⟶
      (Mod.extendScalars φ).obj M ⊗ (Mod.extendScalars φ).obj N)
    (k : (Mod.extendScalars φ).obj M ⊗ (Mod.extendScalars φ).obj N ⟶
      (Mod.extendScalars φ).obj P) (hd : d ≫ k = 𝟙 _)
    (U : Cᵒᵖ) (s t : (sectionRingSheaf J R).obj.obj U)
    (m : M.X.obj.obj U) (n : N.X.obj.obj U) (p : P.X.obj.obj U)
    (h : d.hom.hom.app U ((Mod.extendUnitHom φ P).hom.app U p) =
      comparison_internalTmul J R _ _ U
        ((Mod.extendUnitHom φ M).hom.app U m)
        ((Mod.extendUnitHom φ N).hom.app U n)) :
    k.hom.hom.app U (comparison_internalTmul J R _ _ U
        (scalarSection J R A φ M U s m) (scalarSection J R A φ N U t n)) =
      scalarSection J R A φ P U (s * t) p := by
  have hi : k.hom.hom.app U (comparison_internalTmul J R _ _ U
        ((Mod.extendUnitHom φ M).hom.app U m)
        ((Mod.extendUnitHom φ N).hom.app U n)) =
      (Mod.extendUnitHom φ P).hom.app U p := by
    erw [← h]
    exact congrArg (fun l ↦ (l.hom.hom.app U) ((Mod.extendUnitHom φ P).hom.app U p)) hd
  change (((E).map k).val.app U) _ = _
  erw [scalarSection_smul, scalarSection_smul, tensor_smul, map_smul,
    scalarSection_smul, hi]
  rfl

private theorem scalarSection_unit (P : Mod (Sheaf J AddCommGrpCat.{u}) A)
    (g : (Mod.extendScalars φ).obj P ⟶ 𝟙_ (Mod (Sheaf J AddCommGrpCat.{u}) R))
    (ψ : P.X ⟶ R) (h : Mod.extendUnitHom φ P ≫ g.hom = ψ)
    (U : Cᵒᵖ) (s : (sectionRingSheaf J R).obj.obj U) (p : P.X.obj.obj U) :
    g.hom.hom.app U (scalarSection J R A φ P U s p) =
      s * (@id ((sectionRingSheaf J R).obj.obj U) (ψ.hom.app U p)) := by
  have he : Mod.extendπ φ P ≫ g.hom = R ◁ ψ ≫ MonObj.mul (X := R) := by
    rw [← Mod.whiskerLeft_extendUnitHom_smul' φ P, Category.assoc,
      Mod.act_hom g, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h]
    rfl
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  have he' := congrArg (fun k ↦ Functor.LaxMonoidal.μ F R P.X ≫ F.map k) he
  simp only [Functor.map_comp] at he'
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at he'
  exact congrArg (fun k ↦ (k.app U) (s ⊗ₜ[ℤ] p)) he'

end Scalar
end CategoryTheory.InternalAbelianSheafModule
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual inverse-image module before extension of scalars.
Source: Stacks 03D7 (auxiliary; not a blueprint node). -/
abbrev normalizationInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)

/-- The inverse-image tensor identification applied to a local balanced pure tensor.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
def normalizationInverseImageTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
    (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W) :
    ((normalizationInverseImage Λ f).obj (M ⊗ N)).X.obj.obj W :=
  ((Functor.LaxMonoidal.μ (normalizationInverseImage Λ f) M N).hom.hom.app W)
    (InternalAbelianSheafModule.comparison_internalTmul
      (Scheme.ProEt.topology X) ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y))
      ((normalizationInverseImage Λ f).obj M) ((normalizationInverseImage Λ f).obj N) W m n)

/-- The local scalar-extension generator s tensor m, using the actual coequalizer projection.
Source: Stacks 03D7 and 03EK (auxiliary; not a blueprint node). -/
def normalizationScalarTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W) :
    ((CondensedRing.upperStar Λ f).obj M).X.obj.obj W :=
  ((Mod.extendπ (condensedPullbackHom Λ f) ((normalizationInverseImage Λ f).obj M)).hom.app W)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ((normalizationInverseImage Λ f).obj M).X).app W)
      (s ⊗ₜ[ℤ] m))

/-- The actual composite oplax tensor map: abelian inverse image followed by scalar extension.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
@[reducible] def normalizationInternalTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (CondensedRing.upperStar Λ f).obj (M ⊗ N) ⟶
      (CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N

/-- The inverse of the actual composite oplax tensor map, supplied by its strong structure.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
@[reducible] def normalizationInternalTensorInv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N ⟶
      (CondensedRing.upperStar Λ f).obj (M ⊗ N) :=
  (CondensedRing.monoidal_upperStar Λ f).toLaxMonoidal.μ M N

/-- The actual composite oplax unit, retaining the scalar-extension multiplication map.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
@[reducible] def normalizationInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj (𝟙_ (internalModules Λ Y)) ⟶
      𝟙_ (internalModules Λ X) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η

/-- The specified ringed-section adjunction mate tensor map.
Source: Stacks 03D7 and 03EL (auxiliary; not a blueprint node). -/
@[reducible] def normalizationSectionTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :
    (pullback Λ f).obj (M ⊗ N) ⟶ (pullback Λ f).obj M ⊗ (pullback Λ f).obj N :=
  (pullOplax Λ f).δ M N

/-- The specified ringed-section adjunction mate unit map.
Source: Stacks 03D7 and 03EL (auxiliary; not a blueprint node). -/
@[reducible] def normalizationSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).obj (𝟙_ (modules Λ Y)) ⟶ 𝟙_ (modules Λ X) :=
  (pullOplax Λ f).η

section MateTransport

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
  {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
  {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
  {B' : Type u₄} [Category.{v₄} B'] [MonoidalCategory B']

omit [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory A']
  [MonoidalCategory B'] in
private theorem hom_mate_transport
    (E : A ⥤ A') (F : B ⥤ B') (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (b : L' ⊣ R')
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (hunit : ∀ M, E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      R'.map (γ.hom.app M) = b.unit.app (E.obj M))
    (M : A) (N : B) (h : L.obj M ⟶ N) :
    E.map (a.homEquiv M N h) ≫ β.hom.app N =
      b.homEquiv (E.obj M) (F.obj N) (γ.inv.app M ≫ F.map h) := by
  have hu : E.map (a.unit.app M) ≫ β.hom.app (L.obj M) =
      b.unit.app (E.obj M) ≫ R'.map (γ.inv.app M) := by
    apply (cancel_mono (R'.map (γ.hom.app M))).mp
    rw [Category.assoc, Category.assoc, ← R'.map_comp, γ.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [R'.map_id, Category.comp_id]
    exact hunit M
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [show E.map (R.map h) ≫ β.hom.app N =
    β.hom.app (L.obj M) ≫ R'.map (F.map h) from β.hom.naturality h]
  rw [← Category.assoc, hu, Category.assoc]

private theorem tensor_unit_mate_transport
    (E : A ⥤ A') (F : B ⥤ B') (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (b : L' ⊣ R')
    [R.LaxMonoidal] [R'.LaxMonoidal]
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (e : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N) (e₀ : E.obj (𝟙_ A) ≅ 𝟙_ A')
    (g : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N) (g₀ : F.obj (𝟙_ B) ≅ 𝟙_ B')
    (d : ∀ M N, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N) (d₀ : L.obj (𝟙_ A) ⟶ 𝟙_ B)
    (hn : ∀ {M M' N N'} (s : M ⟶ M') (t : N ⟶ N'),
      E.map (s ⊗ₘ t) ≫ (e M' N').hom =
        (e M N).hom ≫ (E.map s ⊗ₘ E.map t))
    (hunit : ∀ M, E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      R'.map (γ.hom.app M) = b.unit.app (E.obj M))
    (hpair : ∀ M N, (e (R.obj M) (R.obj N)).hom ≫
      (β.hom.app M ⊗ₘ β.hom.app N) ≫ Functor.LaxMonoidal.μ R' (F.obj M) (F.obj N) =
        E.map (Functor.LaxMonoidal.μ R M N) ≫ β.hom.app (M ⊗ N) ≫ R'.map (g M N).hom)
    (heps : E.map (Functor.LaxMonoidal.ε R) ≫ β.hom.app (𝟙_ B) ≫ R'.map g₀.hom =
      e₀.hom ≫ Functor.LaxMonoidal.ε R')
    (hmt : ∀ M N, a.homEquiv _ _ (d M N) =
      (a.unit.app M ⊗ₘ a.unit.app N) ≫ Functor.LaxMonoidal.μ R (L.obj M) (L.obj N))
    (hmu : a.homEquiv _ _ d₀ = Functor.LaxMonoidal.ε R) :
    (∀ M N, F.map (d M N) ≫ (g (L.obj M) (L.obj N)).hom ≫
      (γ.hom.app M ⊗ₘ γ.hom.app N) =
        γ.hom.app (M ⊗ N) ≫ L'.map (e M N).hom ≫
          b.leftAdjointOplaxMonoidal.δ (E.obj M) (E.obj N)) ∧
    (F.map d₀ ≫ g₀.hom = γ.hom.app (𝟙_ A) ≫ L'.map e₀.hom ≫
      b.leftAdjointOplaxMonoidal.η) := by
  have hc := hom_mate_transport E F L R a L' R' b β γ hunit
  constructor
  · intro M N
    apply (cancel_epi (γ.inv.app (M ⊗ N))).mp
    apply (b.homEquiv _ _).injective
    simp only [Iso.inv_hom_id_app_assoc]
    calc
      _ = E.map (a.homEquiv _ _ (d M N)) ≫ β.hom.app (L.obj M ⊗ L.obj N) ≫
          R'.map ((g (L.obj M) (L.obj N)).hom ≫ (γ.hom.app M ⊗ₘ γ.hom.app N)) := by
        rw [reassoc_of% (hc (M ⊗ N) (L.obj M ⊗ L.obj N) (d M N))]
        simpa only [Category.assoc] using b.homEquiv_naturality_right
          (γ.inv.app (M ⊗ N) ≫ F.map (d M N))
          ((g (L.obj M) (L.obj N)).hom ≫ (γ.hom.app M ⊗ₘ γ.hom.app N))
      _ = E.map (a.unit.app M ⊗ₘ a.unit.app N) ≫
          (e (R.obj (L.obj M)) (R.obj (L.obj N))).hom ≫
          (β.hom.app (L.obj M) ⊗ₘ β.hom.app (L.obj N)) ≫
          Functor.LaxMonoidal.μ R' (F.obj (L.obj M)) (F.obj (L.obj N)) ≫
          R'.map (γ.hom.app M ⊗ₘ γ.hom.app N) := by
        rw [hmt, Functor.map_comp, Functor.map_comp]
        simpa only [Category.assoc] using congrArg
          (fun k ↦ E.map (a.unit.app M ⊗ₘ a.unit.app N) ≫ k ≫
            R'.map (γ.hom.app M ⊗ₘ γ.hom.app N)) (hpair (L.obj M) (L.obj N)).symm
      _ = (e M N).hom ≫
          ((E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫ R'.map (γ.hom.app M)) ⊗ₘ
            (E.map (a.unit.app N) ≫ β.hom.app (L.obj N) ≫ R'.map (γ.hom.app N))) ≫
          Functor.LaxMonoidal.μ R' (L'.obj (E.obj M)) (L'.obj (E.obj N)) := by
        rw [reassoc_of% (hn (a.unit.app M) (a.unit.app N))]
        rw [← Functor.LaxMonoidal.μ_natural]
        simp only [tensorHom_comp_tensorHom_assoc]
        rfl
      _ = (e M N).hom ≫ (b.unit.app (E.obj M) ⊗ₘ b.unit.app (E.obj N)) ≫
          Functor.LaxMonoidal.μ R' (L'.obj (E.obj M)) (L'.obj (E.obj N)) := by
        rw [hunit, hunit]
      _ = _ := by
        rw [b.homEquiv_naturality_left]
        simp only [Adjunction.leftAdjointOplaxMonoidal_δ, Functor.comp_obj,
          Equiv.apply_symm_apply]
  · apply (cancel_epi (γ.inv.app (𝟙_ A))).mp
    apply (b.homEquiv _ _).injective
    simp only [Iso.inv_hom_id_app_assoc]
    calc
      _ = E.map (a.homEquiv _ _ d₀) ≫ β.hom.app (𝟙_ B) ≫ R'.map g₀.hom := by
        rw [reassoc_of% (hc (𝟙_ A) (𝟙_ B) d₀)]
        simpa only [Category.assoc] using b.homEquiv_naturality_right
          (γ.inv.app (𝟙_ A) ≫ F.map d₀) g₀.hom
      _ = e₀.hom ≫ Functor.LaxMonoidal.ε R' := by rw [hmu]; exact heps
      _ = _ := by
        rw [b.homEquiv_naturality_left]
        simp only [Adjunction.leftAdjointOplaxMonoidal_η, Equiv.apply_symm_apply]

end MateTransport

-- Use the uniqueness API without expanding the chosen constraints.
attribute [local irreducible] ordinaryTensorComparison ordinaryUnitComparison
attribute [local irreducible] internalPushLax pushLax

private theorem ordinaryTensor_natural (X : Scheme.{u})
    {M M' N N' : internalModules Λ X} (g : M ⟶ M') (h : N ⟶ N') :
    (equivalence Λ X).functor.map (g ⊗ₘ h) ≫ (ordinaryTensorComparison Λ X M' N').hom =
      (ordinaryTensorComparison Λ X M N).hom ≫
        ((equivalence Λ X).functor.map g ⊗ₘ (equivalence Λ X).functor.map h) := by
  obtain ⟨t, t₀, ht, _, hn, _⟩ :=
    (InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)).2
  have he (M N : internalModules Λ X) : t M N = ordinaryTensorComparison Λ X M N :=
    (ordinaryTensorComparison_existsUnique Λ X M N).unique (ht M N)
      (by simpa only [ordinaryTensorComparison] using
        (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec)
  rw [← he M N, ← he M' N']
  exact hn M M' N N' g h

private theorem ordinaryMate_transport {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ M N : internalModules Λ Y,
      (equivalence Λ X).functor.map (normalizationInternalTensor Λ f M N) ≫
          (ordinaryTensorComparison Λ X
            ((CondensedRing.upperStar Λ f).obj M) ((CondensedRing.upperStar Λ f).obj N)).hom ≫
          ((pullComparison Λ f).hom.app M ⊗ₘ (pullComparison Λ f).hom.app N) =
        (pullComparison Λ f).hom.app (M ⊗ N) ≫
          (pullback Λ f).map (ordinaryTensorComparison Λ Y M N).hom ≫
          normalizationSectionTensor Λ f
            ((equivalence Λ Y).functor.obj M) ((equivalence Λ Y).functor.obj N)) ∧
    ((equivalence Λ X).functor.map (normalizationInternalUnit Λ f) ≫
        (ordinaryUnitComparison Λ X).hom =
      (pullComparison Λ f).hom.app (𝟙_ (internalModules Λ Y)) ≫
        (pullback Λ f).map (ordinaryUnitComparison Λ Y).hom ≫
        normalizationSectionUnit Λ f) := by
  have hd := internal_direct_image_lax_realization Λ f
  have hm := composite_module_oplax_mate Λ f
  exact tensor_unit_mate_transport
    (equivalence Λ Y).functor (equivalence Λ X).functor
    (CondensedRing.upperStar Λ f) (CondensedRing.lowerStar Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (pullback Λ f) (pushforward Λ f) (adjunction Λ f)
    (pushComparison Λ f) (pullComparison Λ f)
    (ordinaryTensorComparison Λ Y) (ordinaryUnitComparison Λ Y)
    (ordinaryTensorComparison Λ X) (ordinaryUnitComparison Λ X)
    (normalizationInternalTensor Λ f) (normalizationInternalUnit Λ f)
    (ordinaryTensor_natural Λ Y) hd.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2.1 hm.1 hm.2

attribute [local irreducible] CategoryTheory.Localization.Monoidal.tensorBifunctor
set_option backward.isDefEq.respectTransparency.types false

private theorem forward_insert {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
    (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W) :
    ((normalizationInternalTensor Λ f M N).hom.hom.app W)
        (((Mod.extendUnitHom (condensedPullbackHom Λ f)
          ((normalizationInverseImage Λ f).obj (M ⊗ N))).hom.app W)
          (normalizationInverseImageTensor Λ f M N W m n)) =
      internalPureTensor Λ X _ _ W
        (((Mod.extendUnitHom (condensedPullbackHom Λ f)
          ((normalizationInverseImage Λ f).obj M)).hom.app W) m)
        (((Mod.extendUnitHom (condensedPullbackHom Λ f)
          ((normalizationInverseImage Λ f).obj N)).hom.app W) n) := by
  let A := ProEtale.upperStar Ab.{u + 1} f
  let T := normalizationInverseImage Λ f
  let φ := condensedPullbackHom Λ f
  let E := Mod.extendScalarsIsoComapInv φ
  have hu (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (A.obj (condensedRingObj Λ Y))) :
      (E.inv.app K).hom = Mod.extendUnitHom φ K := by
    apply (cancel_mono (E.hom.app K).hom).mp
    rw [← Mod.comp_hom', E.inv_hom_id_app]
    exact (CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f K).symm
  have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ A M.X N.X ≫ k)
    (upperStar_tensorπ_delta Λ f M N)
  rw [Functor.Monoidal.μ_δ_assoc] at h
  have hT := A.tensorπ_mapModTensorIso_hom_hom M N
  change Mod.tensorObjπ (T.obj M) (T.obj N) ≫
    (Functor.LaxMonoidal.μ T M N).hom = _ at hT
  rw [← reassoc_of% hT] at h
  have hn := tensorπ_natural (E.inv.app (T.obj M)) (E.inv.app (T.obj N))
  change Mod.tensorObjπ ((Mod.comap (asIso φ).inv).obj (T.obj M))
    ((Mod.comap (asIso φ).inv).obj (T.obj N)) ≫ _ = _ at hn
  rw [hn, hu, hu] at h
  let F := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  have h' := congrArg (fun k ↦ Functor.LaxMonoidal.μ F (T.obj M).X (T.obj N).X ≫
    F.map k) h
  simp only [Functor.map_comp] at h'
  rw [← Functor.LaxMonoidal.μ_natural_assoc] at h'
  exact congrArg (fun k ↦ (k.app W) (m ⊗ₜ[ℤ] n)) h'

-- The strong structure is used only through its inverse equations below.
attribute [local irreducible] CondensedRing.monoidal_upperStar

private theorem inverseTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s t : (ring Λ X).obj.obj W)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
    (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W) :
    ((normalizationInternalTensorInv Λ f M N).hom.hom.app W)
        (internalPureTensor Λ X _ _ W
          (normalizationScalarTensor Λ f M W s m)
          (normalizationScalarTensor Λ f N W t n)) =
      normalizationScalarTensor Λ f (M ⊗ N) W (s * t)
        (normalizationInverseImageTensor Λ f M N W m n) := by
  have hd : normalizationInternalTensor Λ f M N ≫
      normalizationInternalTensorInv Λ f M N = 𝟙 _ := by
    let := CondensedRing.monoidal_upperStar Λ f
    exact Functor.Monoidal.δ_μ _ M N
  exact InternalAbelianSheafModule.scalarSection_inverse
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
    ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y))
    (condensedPullbackHom Λ f)
    ((normalizationInverseImage Λ f).obj M) ((normalizationInverseImage Λ f).obj N)
    ((normalizationInverseImage Λ f).obj (M ⊗ N))
    (normalizationInternalTensor Λ f M N) (normalizationInternalTensorInv Λ f M N) hd
    W s t m n (normalizationInverseImageTensor Λ f M N W m n)
    (forward_insert Λ f M N W m n)

private theorem forwardTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
    (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W) :
    ((normalizationInternalTensor Λ f M N).hom.hom.app W)
        (normalizationScalarTensor Λ f (M ⊗ N) W s
          (normalizationInverseImageTensor Λ f M N W m n)) =
      internalPureTensor Λ X _ _ W
        (normalizationScalarTensor Λ f M W s m)
        (normalizationScalarTensor Λ f N W 1 n) := by
  have hd : normalizationInternalTensor Λ f M N ≫
      normalizationInternalTensorInv Λ f M N = 𝟙 _ := by
    let := CondensedRing.monoidal_upperStar Λ f
    exact Functor.Monoidal.δ_μ _ M N
  have hk : normalizationInternalTensorInv Λ f M N ≫
      normalizationInternalTensor Λ f M N = 𝟙 _ := by
    let := CondensedRing.monoidal_upperStar Λ f
    exact Functor.Monoidal.μ_δ _ M N
  have hi (x) : ((normalizationInternalTensor Λ f M N).hom.hom.app W)
      (((normalizationInternalTensorInv Λ f M N).hom.hom.app W) x) = x :=
    congrArg (fun k ↦ (k.hom.hom.app W) x) hk
  have hinj : Function.Injective
      ((normalizationInternalTensorInv Λ f M N).hom.hom.app W) := by
    intro x y h
    exact (hi x).symm.trans ((congrArg
      ((normalizationInternalTensor Λ f M N).hom.hom.app W) h).trans (hi y))
  apply hinj
  have h := congrArg (fun k ↦ (k.hom.hom.app W)
    (normalizationScalarTensor Λ f (M ⊗ N) W s
      (normalizationInverseImageTensor Λ f M N W m n))) hd
  change ((normalizationInternalTensorInv Λ f M N).hom.hom.app W)
    (((normalizationInternalTensor Λ f M N).hom.hom.app W)
      (normalizationScalarTensor Λ f (M ⊗ N) W s
        (normalizationInverseImageTensor Λ f M N W m n))) =
      normalizationScalarTensor Λ f (M ⊗ N) W s
        (normalizationInverseImageTensor Λ f M N W m n) at h
  exact h.trans (by
    simpa only [mul_one] using (inverseTensor_scalar Λ f M N W s 1 m n).symm)

private theorem unit_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
    (r : ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)).obj.obj W) :
    ((normalizationInternalUnit Λ f).hom.hom.app W)
        (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) =
      s * (@id ((ring Λ X).obj.obj W) ((condensedPullbackHom Λ f).hom.app W r)) := by
  have hu := CondensedRing.extendUnitHom_η_upperStar Λ f
  change Mod.extendUnitHom (condensedPullbackHom Λ f)
    ((normalizationInverseImage Λ f).obj (𝟙_ (internalModules Λ Y))) ≫
      (normalizationInternalUnit Λ f).hom = condensedPullbackHom Λ f at hu
  exact InternalAbelianSheafModule.scalarSection_unit
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
    ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y))
    (condensedPullbackHom Λ f)
    ((normalizationInverseImage Λ f).obj (𝟙_ (internalModules Λ Y)))
    (normalizationInternalUnit Λ f) (condensedPullbackHom Λ f) hu W s r

-- Keep the proved generator formulas as the interface during the final assembly.
attribute [local irreducible] normalizationScalarTensor normalizationInverseImageTensor

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
