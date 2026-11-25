/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantModuleScalarCenter
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Sectionwise coordinates for a finite basis of constant coefficient rings

Given a finite basis `b` of `B` over `A`, the sheafified coordinate functionals give, on
every object, `A`-linear coordinates of sections of the constant sheaf `B`; these satisfy
the Kronecker and expansion identities with respect to the sheafified basis vectors.
Source: Stacks 03CY, 03CZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory.ConstantModuleScalar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Sections of a finite sum of morphisms of sheaves of modules. -/
theorem _root_.SheafOfModules.sum_val_app {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{r} R}
    {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (U : Cᵒᵖ) (x : M.val.obj U) :
    (∑ i ∈ s, f i).val.app U x = ∑ i ∈ s, (f i).val.app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

/-- Morphisms out of a sheafification of presheaves of modules are determined by their
values on the sections coming from the presheaf. -/
theorem _root_.PresheafOfModules.sheafification_hom_ext {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R₀ : Cᵒᵖ ⥤ RingCat.{r}} {R : Sheaf J RingCat.{r}}
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
    {P : PresheafOfModules.{r} R₀} {F : SheafOfModules.{r} R}
    (f g : (PresheafOfModules.sheafification α).obj P ⟶ F)
    (h : ∀ (U : Cᵒᵖ) (x : P.obj U), f.val.app U ((toSheafify J P.presheaf).app U x) =
      g.val.app U ((toSheafify J P.presheaf).app U x)) : f = g := by
  apply (PresheafOfModules.sheafificationHomEquiv α).injective
  ext U x
  exact h U x

section RestrictSheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S) (P : PresheafOfModules.{r} S.obj)

/-- The presheaf unit of a sheafification, after restricting scalars. -/
def restrictToSheafify :
    (PresheafOfModules.restrictScalars φ.hom).obj P ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
        ((SheafOfModules.restrictScalars φ).obj
          ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P)).val where
  app U := ModuleCat.ofHom (X := ((PresheafOfModules.restrictScalars φ.hom).obj P).obj U)
    (Y := ((PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
        ((SheafOfModules.restrictScalars φ).obj
          ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P)).val).obj U)
    { toFun := (toSheafify J P.presheaf).app U
      map_add' := _root_.map_add _
      map_smul' := fun r t ↦
        ((PresheafOfModules.toSheafify (𝟙 S.obj) (toSheafify J P.presheaf)).app U).hom.map_smul
          (φ.hom.app U r) t }
  naturality {U V} f := by
    ext t
    exact ConcreteCategory.congr_hom ((toSheafify J P.presheaf).naturality f) t

/-- The comparison between the sheafification of a restriction of scalars and the
restriction of scalars of a sheafification. -/
@[irreducible]
def restrictSheafifyComparison :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars φ.hom).obj P) ⟶
      (SheafOfModules.restrictScalars φ).obj
        ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (restrictToSheafify φ P)

theorem restrictSheafifyComparison_apply (U : Cᵒᵖ) (t : P.obj U) :
    (restrictSheafifyComparison φ P).val.app U
      ((toSheafify J ((PresheafOfModules.restrictScalars φ.hom).obj P).presheaf).app U t) =
        (toSheafify J P.presheaf).app U t := by
  have h := congrArg (fun g ↦ (PresheafOfModules.toPresheaf R.obj).map g)
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
      (P := (PresheafOfModules.restrictScalars φ.hom).obj P)
      (F := (SheafOfModules.restrictScalars φ).obj
          ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P))).apply_symm_apply
      (restrictToSheafify φ P))
  rw [restrictSheafifyComparison]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) t

instance restrictSheafifyComparison_isIso : IsIso (restrictSheafifyComparison φ P) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let Q := ((PresheafOfModules.restrictScalars φ.hom).obj P).presheaf
  have h : toSheafify J Q ≫
      ((SheafOfModules.toSheaf _).map (restrictSheafifyComparison φ P)).hom =
        toSheafify J P.presheaf := by
    ext U t
    exact restrictSheafifyComparison_apply φ P U t
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J Q),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J Q)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J Q ≫ ((SheafOfModules.toSheaf _).map (restrictSheafifyComparison φ P)).hom) ∧ _
  erw [h]
  exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (toSheafify J P.presheaf) x y h⟩,
    ⟨fun x ↦ Presheaf.imageSieve_mem J (toSheafify J P.presheaf) x⟩⟩

/-- Morphisms out of the restriction of scalars of a sheafification are determined by
their values on the sections coming from the presheaf. -/
theorem restrictSheafify_hom_ext {F : SheafOfModules.{r} R}
    (f g : (SheafOfModules.restrictScalars φ).obj
      ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P) ⟶ F)
    (h : ∀ (U : Cᵒᵖ) (t : P.obj U), f.val.app U ((toSheafify J P.presheaf).app U t) =
      g.val.app U ((toSheafify J P.presheaf).app U t)) : f = g := by
  rw [← cancel_epi (restrictSheafifyComparison φ P)]
  apply PresheafOfModules.sheafification_hom_ext
  intro U t
  change f.val.app U ((restrictSheafifyComparison φ P).val.app U _) =
    g.val.app U ((restrictSheafifyComparison φ P).val.app U _)
  rw [restrictSheafifyComparison_apply]
  exact h U t

/-- Lift a morphism of presheaves of modules to the restriction of scalars of the
sheafification. -/
def restrictSheafifyLift {F : SheafOfModules.{r} R}
    (g : (PresheafOfModules.restrictScalars φ.hom).obj P ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj F.val) :
    (SheafOfModules.restrictScalars φ).obj
      ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P) ⟶ F :=
  inv (restrictSheafifyComparison φ P) ≫ (PresheafOfModules.sheafificationHomEquiv _).symm g

theorem restrictSheafifyLift_apply {F : SheafOfModules.{r} R}
    (g : (PresheafOfModules.restrictScalars φ.hom).obj P ⟶
      (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj F.val) (U : Cᵒᵖ) (t : P.obj U) :
    (restrictSheafifyLift φ P g).val.app U ((toSheafify J P.presheaf).app U t) =
      g.app U t := by
  rw [← restrictSheafifyComparison_apply φ P U t]
  have h := congrArg (fun g ↦ (PresheafOfModules.toPresheaf R.obj).map g)
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
      (P := (PresheafOfModules.restrictScalars φ.hom).obj P) (F := F)).apply_symm_apply g)
  change ((restrictSheafifyComparison φ P ≫ restrictSheafifyLift φ P g).val.app U) _ = _
  rw [restrictSheafifyLift, IsIso.hom_inv_id_assoc]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) t

/-- The unit of the sheafification of a presheaf of modules is linear. -/
theorem toSheafify_smul (U : Cᵒᵖ) (s : S.obj.obj U) (t : P.obj U) :
    (toSheafify J P.presheaf).app U (s • t) =
      HSMul.hSMul (α := S.obj.obj U)
        (β := ((PresheafOfModules.sheafification (𝟙 S.obj)).obj P).val.obj U)
        s ((toSheafify J P.presheaf).app U t) :=
  ((PresheafOfModules.toSheafify (𝟙 S.obj) (toSheafify J P.presheaf)).app U).hom.map_smul s t

end RestrictSheafify

section Coordinates

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Sheafification of commutative ring presheaves on an essentially small site is
locally bijective. -/
instance ringLocallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, u, r+1, r, r, r} J

/-- The constant presheaf of modules attached to a module. -/
def constModule (A : CommRingCat.{r}) (M : ModuleCat.{r} A) :
    PresheafOfModules.{r} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj _ := M
  map _ := ModuleCat.ofHom LinearMap.id
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The unit from the constant ring presheaf to the constant ring sheaf. -/
def constRingUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (constantRing J A)).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)

instance constRingUnit_isLocallyInjective (A : CommRingCat.{r}) :
    Presheaf.IsLocallyInjective J (constRingUnit J A) :=
  ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x y h⟩

instance constRingUnit_isLocallySurjective (A : CommRingCat.{r}) :
    Presheaf.IsLocallySurjective J (constRingUnit J A) :=
  ⟨fun x ↦ Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x⟩

variable (A B : CommRingCat.{r}) [Algebra A B]

/-- The constant algebra map between constant ring sheaves. -/
abbrev constAlgebraMap : constantRing J A ⟶ constantRing J B :=
  (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))

/-- The constant sheaf `B`, regarded as a sheaf of modules over the constant sheaf `A`. -/
abbrev basisTarget : modules (constantRing J A) :=
  (restriction (constAlgebraMap J A B)).obj (SheafOfModules.unit _)

/-- The sheafified basis vector attached to a constant section. -/
abbrev constSection (c : B) (U : Cᵒᵖ) : (constantRing J B).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U c

omit [EssentiallySmall.{r} C] [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- The constant algebra map commutes with the sheafification units. -/
theorem constAlgebraMap_constSection (U : Cᵒᵖ) (a : A) :
    (constAlgebraMap J A B).hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) =
      constSection J B (algebraMap A B a) U :=
  (congrArg (fun t ↦ t a) (NatTrans.congr_app
    (toSheafify_naturality J
      ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (algebraMap A B)))) U)).symm

/-- The constant presheaf `B` maps to the constant sheaf `B`. -/
def basisConstToTarget :
    constModule A (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (constRingUnit J A)).obj
        (basisTarget J A B).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (constRingUnit J A)).obj
      (basisTarget J A B).val).obj U)
    { toFun := (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        rw [Algebra.smul_def]
        change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U
          (algebraMap A B a * b) = _
        rw [map_mul]
        congr 1
        exact (constAlgebraMap_constSection J A B U a).symm }
  naturality {U V} f := by
    ext b
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) b

/-- The comparison from the module sheafification of the constant presheaf `B`. -/
@[irreducible]
def basisLift :
    (PresheafOfModules.sheafification (constRingUnit J A)).obj
      (constModule A (ModuleCat.of A B)) ⟶ basisTarget J A B :=
  (PresheafOfModules.sheafificationHomEquiv _).symm (basisConstToTarget J A B)

theorem basisLift_constant (U : Cᵒᵖ) (x : B) :
    (basisLift J A B).val.app U
      ((toSheafify J (constModule (C := C) A (ModuleCat.of A B)).presheaf).app U x) =
        constSection J B x U := by
  have h := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g)
    ((PresheafOfModules.sheafificationHomEquiv (constRingUnit J A)
      (P := constModule (C := C) A (ModuleCat.of A B))
      (F := basisTarget J A B)).apply_symm_apply (basisConstToTarget J A B))
  rw [basisLift]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) x

instance basisLift_isIso : IsIso (basisLift J A B) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := (constModule (C := C) A (ModuleCat.of A B)).presheaf
  have h : toSheafify J P ≫
      ((SheafOfModules.toSheaf _).map (basisLift J A B)).hom =
        (PresheafOfModules.toPresheaf _).map (basisConstToTarget J A B) := by
    let E := PresheafOfModules.sheafificationHomEquiv (constRingUnit J A)
      (P := constModule (C := C) A (ModuleCat.of A B)) (F := basisTarget J A B)
    have hh := E.apply_symm_apply (basisConstToTarget J A B)
    have hh' := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g) hh
    change toSheafify J P ≫ (PresheafOfModules.toPresheaf _).map (basisLift J A B).val = _
    rw [basisLift]
    exact hh'
  rw [← Presheaf.comp_isLocallyInjective_iff J (toSheafify J P),
    ← Presheaf.comp_isLocallySurjective_iff J (toSheafify J P)]
  change Presheaf.IsLocallyInjective J
    (toSheafify J P ≫ ((SheafOfModules.toSheaf _).map (basisLift J A B)).hom) ∧ _
  erw [h]
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x⟩

/-- The constant presheaf map induced by an `A`-linear functional on `B`. -/
def coordConst (q : B →ₗ[A] A) :
    constModule A (ModuleCat.of A B) ⟶
      (PresheafOfModules.restrictScalars (constRingUnit J A)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (constantRing J A))).val where
  app U := ModuleCat.ofHom (Y :=
    ((PresheafOfModules.restrictScalars (constRingUnit J A)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (constantRing J A))).val).obj U)
    { toFun := fun x ↦ (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U (q x)
      map_add' := fun x y ↦ by
        rw [_root_.map_add, _root_.map_add]
      map_smul' := fun a x ↦ by
        rw [_root_.map_smul, smul_eq_mul, map_mul]
        rfl }
  naturality {U V} f := by
    ext x
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).naturality f) (q x)

/-- The sheafified coordinate functional attached to an `A`-linear functional on `B`. -/
def coord (q : B →ₗ[A] A) :
    basisTarget J A B ⟶ SheafOfModules.unit _ :=
  inv (basisLift J A B) ≫ (PresheafOfModules.sheafificationHomEquiv _).symm
    (coordConst J A B q)

theorem coord_constSection (q : B →ₗ[A] A) (U : Cᵒᵖ) (x : B) :
    (coord J A B q).val.app U (constSection J B x U) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U (q x) := by
  rw [← basisLift_constant J A B U x]
  have h := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g)
    ((PresheafOfModules.sheafificationHomEquiv (constRingUnit J A)
      (P := constModule (C := C) A (ModuleCat.of A B))
      (F := SheafOfModules.unit _)).apply_symm_apply (coordConst J A B q))
  change ((basisLift J A B ≫ coord J A B q).val.app U) _ = _
  rw [coord, IsIso.hom_inv_id_assoc]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) x

/-- Multiplication by a constant section, from the constant sheaf `A`. -/
def basisColumn (c : B) : SheafOfModules.unit _ ⟶ basisTarget J A B :=
  (basisTarget J A B).unitHomEquiv.symm
    ⟨fun U ↦ constSection J B c U,
      fun {_ _} f ↦ ConcreteCategory.congr_hom
        ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) c |>.symm⟩

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
theorem basisColumn_apply (c : B) (U : Cᵒᵖ) (x : (constantRing J A).obj.obj U) :
    (basisColumn J A B c).val.app U x =
      (constAlgebraMap J A B).hom.app U x * constSection J B c U := rfl

/-- The coordinates of a basis reconstruct every section of the constant sheaf `B`. -/
theorem coord_expansion {I : Type*} [Fintype I] (b : Module.Basis I A B) :
    ∑ i, coord J A B (b.coord i) ≫ basisColumn J A B (b i) = 𝟙 _ := by
  rw [← cancel_epi (basisLift J A B), Category.comp_id]
  apply PresheafOfModules.sheafification_hom_ext
  intro U x
  change (∑ i, coord J A B (b.coord i) ≫ basisColumn J A B (b i)).val.app U
    ((basisLift J A B).val.app U _) = (basisLift J A B).val.app U _
  rw [basisLift_constant, SheafOfModules.sum_val_app]
  change ∑ i, (basisColumn J A B (b i)).val.app U
    ((coord J A B (b.coord i)).val.app U (constSection J B x U)) = _
  simp only [coord_constSection, basisColumn_apply, constAlgebraMap_constSection,
    constSection]
  conv_rhs => rw [← b.sum_repr x]
  simp [Algebra.smul_def]

/-- The coordinates of a basis vector are Kronecker deltas. -/
theorem coord_basis {I : Type*} [DecidableEq I] (b : Module.Basis I A B) (i j : I)
    (U : Cᵒᵖ) :
    (coord J A B (b.coord i)).val.app U (constSection J B (b j) U) =
      (if j = i then 1 else 0 : (constantRing J A).obj.obj U) := by
  rw [coord_constSection, b.coord_apply, b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

end Coordinates

open scoped ChangeOfRings

section Projections

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (A B : CommRingCat.{r}) [Algebra A B]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
omit [EssentiallySmall.{r} C] in
/-- Restriction on the sectionwise change of rings, on pure tensors. -/
theorem changeOfRingsPresheaf_map_tmul (M : modules (constantRing J A)) {U V : Cᵒᵖ}
    (f : U ⟶ V) (s : (constantRing J B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).map f
        (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m) =
      (constantRing J B).obj.map f s ⊗ₜ[(constantRing J A).obj.obj V,
        ((constAlgebraMap J A B).hom.app V).hom] M.val.map f m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap (constAlgebraMap J A B) M f) s m

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Sectionwise contraction with a coordinate functional: `s ⊗ m ↦ q(s) m`. -/
def coordTensorApp (q : B →ₗ[A] A) (M : modules (constantRing J A)) (U : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (constAlgebraMap J A B)).hom).obj
          (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M)).obj U ⟶
      ((PresheafOfModules.restrictScalars (𝟙 _)).obj M.val).obj U :=
  ModuleCat.ofHom (X := ((PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (constAlgebraMap J A B)).hom).obj
          (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M)).obj U)
    (Y := ((PresheafOfModules.restrictScalars (𝟙 _)).obj M.val).obj U)
    { toFun := fun t ↦ TensorProduct.lift ((LinearMap.lsmul _ (M.val.obj U)).comp
        ((coord J A B q).val.app U).hom) t
      map_add' := _root_.map_add _
      map_smul' := fun r t ↦ by
        induction t using TensorProduct.inductionOn with
        | tmul s m =>
          erw [ModuleCat.ExtendScalars.smul_tmul]
          rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul, LinearMap.comp_apply,
            LinearMap.comp_apply, LinearMap.lsmul_apply, LinearMap.lsmul_apply]
          exact (congrArg (· • m) (((coord J A B q).val.app U).hom.map_smul r s)).trans
            (mul_smul _ _ _)
        | add x y hx hy =>
          rw [smul_add, _root_.map_add, _root_.map_add, hx, hy, smul_add] }

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem coordTensorApp_tmul (q : B →ₗ[A] A) (M : modules (constantRing J A)) (U : Cᵒᵖ)
    (s : (constantRing J B).obj.obj U) (m : M.val.obj U) :
    coordTensorApp J A B q M U
        (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m) =
      (coord J A B q).val.app U s • m := by
  change TensorProduct.lift _ _ = _
  exact TensorProduct.lift.tmul _ _

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Contraction with a coordinate functional, as a morphism of presheaves of modules. -/
def coordTensor (q : B →ₗ[A] A) (M : modules (constantRing J A)) :
    (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map (constAlgebraMap J A B)).hom).obj
          (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M) ⟶
      (PresheafOfModules.restrictScalars (𝟙 _)).obj M.val where
  app U := coordTensorApp J A B q M U
  naturality {U V} f := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul s m =>
      change coordTensorApp J A B q M V
          ((SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).map f
            (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m)) =
        M.val.map f (coordTensorApp J A B q M U
          (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m))
      rw [changeOfRingsPresheaf_map_tmul, coordTensorApp_tmul, coordTensorApp_tmul,
        M.val.map_smul]
      congr 1
      exact PresheafOfModules.naturality_apply (coord J A B q).val f s
    | add x y hx hy =>
      rw [_root_.map_add, _root_.map_add, hx, hy]

/-- The coordinate projection `B ⊗ M → M`, `s ⊗ m ↦ q(s) m`, on the sheafified change of
rings. -/
def proj (q : B →ₗ[A] A) (M : modules (constantRing J A)) :
    (restriction (constAlgebraMap J A B)).obj
      (SheafOfModules.changeOfRings (constAlgebraMap J A B) M) ⟶ M :=
  restrictSheafifyLift _ _ (coordTensor J A B q M)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem proj_apply (q : B →ₗ[A] A) (M : modules (constantRing J A)) (U : Cᵒᵖ)
    (s : (constantRing J B).obj.obj U) (m : M.val.obj U) :
    (proj J A B q M).val.app U ((toSheafify J
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
        (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m)) =
      (coord J A B q).val.app U s • m := by
  exact (restrictSheafifyLift_apply _ _ (coordTensor J A B q M) U _).trans
    (coordTensorApp_tmul J A B q M U s m)

omit [EssentiallySmall.{r} C] in
/-- Under the sheafification unit, `s ⊗ a m = (a s) ⊗ m` for a scalar `a` of the base. -/
theorem toSheafify_tmul_smul (M : modules (constantRing J A)) (U : Cᵒᵖ)
    (s : (constantRing J B).obj.obj U) (a : (constantRing J A).obj.obj U)
    (m : M.val.obj U) :
    (toSheafify J
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
        (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom]
          (a • m)) =
    (toSheafify J
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
        (((constAlgebraMap J A B).hom.app U a * s) ⊗ₜ[(constantRing J A).obj.obj U,
          ((constAlgebraMap J A B).hom.app U).hom] m) := by
  let : Module ((constantRing J A).obj.obj U) ((constantRing J B).obj.obj U) :=
    Module.compHom _ ((constAlgebraMap J A B).hom.app U).hom
  exact congrArg _ (TensorProduct.smul_tmul a s m).symm

omit [EssentiallySmall.{r} C] in
theorem incl_naturality_apply (c : B) (M : modules (constantRing J A)) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : M.val.obj U) :
    (toSheafify J
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app V
        (constSection J B c V ⊗ₜ[(constantRing J A).obj.obj V,
          ((constAlgebraMap J A B).hom.app V).hom] M.val.map f x) =
    (SheafOfModules.changeOfRings (constAlgebraMap J A B) M).val.map f
      ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
          (constSection J B c U ⊗ₜ[(constantRing J A).obj.obj U,
            ((constAlgebraMap J A B).hom.app U).hom] x)) := by
  have h : constSection J B c V = (constantRing J B).obj.map f (constSection J B c U) :=
    (ConcreteCategory.congr_hom ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f) c)
  rw [h, ← changeOfRingsPresheaf_map_tmul]
  exact ConcreteCategory.congr_hom ((toSheafify J
    (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).naturality f) _

/-- The inclusion `M → B ⊗ M`, `m ↦ c ⊗ m`, for a constant section `c`. -/
def incl (c : B) (M : modules (constantRing J A)) :
    M ⟶ (restriction (constAlgebraMap J A B)).obj
      (SheafOfModules.changeOfRings (constAlgebraMap J A B) M) where
  val :=
    { app U := ModuleCat.ofHom (X := M.val.obj U)
        (Y := ((restriction (constAlgebraMap J A B)).obj
          (SheafOfModules.changeOfRings (constAlgebraMap J A B) M)).val.obj U)
        { toFun x := (toSheafify J
            (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
              (constSection J B c U ⊗ₜ[(constantRing J A).obj.obj U,
                ((constAlgebraMap J A B).hom.app U).hom] x)
          map_add' x y := by
            rw [TensorProduct.tmul_add, _root_.map_add]
          map_smul' a x := by
            rw [toSheafify_tmul_smul]
            exact toSheafify_smul
              (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M) U
              ((constAlgebraMap J A B).hom.app U a)
              (constSection J B c U ⊗ₜ[(constantRing J A).obj.obj U,
                ((constAlgebraMap J A B).hom.app U).hom] x) }
      naturality {U V} f := by
        ext x
        exact incl_naturality_apply J A B c M f x }

omit [EssentiallySmall.{r} C] in
theorem incl_apply (c : B) (M : modules (constantRing J A)) (U : Cᵒᵖ) (x : M.val.obj U) :
    (incl J A B c M).val.app U x = (toSheafify J
      (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
        (constSection J B c U ⊗ₜ[(constantRing J A).obj.obj U,
          ((constAlgebraMap J A B).hom.app U).hom] x) := rfl

/-- The coordinates of a basis reconstruct every section, sectionwise. -/
theorem coord_expansion_apply {I : Type*} [Fintype I] (b : Module.Basis I A B) (U : Cᵒᵖ)
    (s : (constantRing J B).obj.obj U) :
    ∑ i, (constAlgebraMap J A B).hom.app U ((coord J A B (b.coord i)).val.app U s) *
      constSection J B (b i) U = s := by
  have h := congrArg (fun g ↦ g.val.app U s) (coord_expansion J A B b)
  rw [SheafOfModules.sum_val_app] at h
  exact h

omit [EssentiallySmall.{r} C] [HasWeakSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
/-- The sheafification of a morphism of presheaves of modules, on presheaf sections. -/
theorem sheafification_map_apply {S : Sheaf J RingCat.{r}} {P Q : PresheafOfModules.{r} S.obj}
    (g : P ⟶ Q) (U : Cᵒᵖ) (t : P.obj U) :
    ((PresheafOfModules.sheafification (𝟙 S.obj)).map g).val.app U
      ((toSheafify J P.presheaf).app U t) = (toSheafify J Q.presheaf).app U (g.app U t) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map g)) U) t).symm

theorem incl_proj_self {I : Type*} (b : Module.Basis I A B) (c : I)
    (M : modules (constantRing J A)) :
    incl J A B (b c) M ≫ proj J A B (b.coord c) M = 𝟙 M := by
  classical
  ext U x
  change (proj J A B (b.coord c) M).val.app U ((incl J A B (b c) M).val.app U x) = x
  rw [incl_apply, proj_apply, coord_basis, ite_eq_left rfl, one_smul]

theorem incl_proj_of_ne {I : Type*} (b : Module.Basis I A B) {c d : I} (h : c ≠ d)
    (M : modules (constantRing J A)) :
    incl J A B (b c) M ≫ proj J A B (b.coord d) M = 0 := by
  classical
  ext U x
  change (proj J A B (b.coord d) M).val.app U ((incl J A B (b c) M).val.app U x) = 0
  rw [incl_apply, proj_apply, coord_basis, ite_eq_right h, zero_smul]

theorem sum_proj_incl {I : Type*} [Fintype I] (b : Module.Basis I A B)
    (M : modules (constantRing J A)) :
    ∑ c, proj J A B (b.coord c) M ≫ incl J A B (b c) M = 𝟙 _ := by
  apply restrictSheafify_hom_ext
  intro U t
  rw [SheafOfModules.sum_val_app]
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    let : Module ((constantRing J A).obj.obj U) ((constantRing J B).obj.obj U) :=
      Module.compHom _ ((constAlgebraMap J A B).hom.app U).hom
    calc ∑ c, (incl J A B (b c) M).val.app U ((proj J A B (b.coord c) M).val.app U
          ((toSheafify J
            (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
              (s ⊗ₜ[(constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m)))
        = ∑ c, (toSheafify J
            (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
              (((constAlgebraMap J A B).hom.app U
                ((coord J A B (b.coord c)).val.app U s) * constSection J B (b c) U) ⊗ₜ[
                  (constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m) := by
          refine Finset.sum_congr rfl (fun c _ ↦ ?_)
          rw [proj_apply, incl_apply]
          exact toSheafify_tmul_smul J A B M U _ _ m
      _ = (toSheafify J
            (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U
              (∑ c, ((constAlgebraMap J A B).hom.app U
                ((coord J A B (b.coord c)).val.app U s) * constSection J B (b c) U) ⊗ₜ[
                  (constantRing J A).obj.obj U, ((constAlgebraMap J A B).hom.app U).hom] m) :=
          (_root_.map_sum _ _ _).symm
      _ = _ := by
          rw [← TensorProduct.sum_tmul, coord_expansion_apply]
          rfl
  | add x y hx hy =>
    simp only [_root_.map_add, Finset.sum_add_distrib, hx, hy]

omit [EssentiallySmall.{r} C] in
theorem changeOfRingsHom_apply {M N : modules (constantRing J A)} (f : M ⟶ N) (U : Cᵒᵖ)
    (t : (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).obj U) :
    (SheafOfModules.changeOfRingsHom (constAlgebraMap J A B) M f).val.app U
      ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U t) =
    (toSheafify J
        (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) N).presheaf).app U
      ((ModuleCat.extendScalars ((constAlgebraMap J A B).hom.app U).hom).map (f.val.app U) t) :=
  sheafification_map_apply J _ U t

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem proj_extendScalars_map (q : B →ₗ[A] A) {M N : modules (constantRing J A)}
    (f : M ⟶ N) (U : Cᵒᵖ)
    (t : (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).obj U) :
    (proj J A B q N).val.app U ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) N).presheaf).app U
      ((ModuleCat.extendScalars ((constAlgebraMap J A B).hom.app U).hom).map (f.val.app U) t)) =
    f.val.app U ((proj J A B q M).val.app U ((toSheafify J
        (SheafOfModules.changeOfRingsPresheaf (constAlgebraMap J A B) M).presheaf).app U t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [proj_apply, proj_apply]
    exact ((f.val.app U).hom.map_smul _ m).symm
  | add x y hx hy =>
    simp only [_root_.map_add, hx, hy]

theorem proj_naturality (q : B →ₗ[A] A) {M N : modules (constantRing J A)} (f : M ⟶ N) :
    (restriction (constAlgebraMap J A B)).map
        (SheafOfModules.changeOfRingsHom (constAlgebraMap J A B) M f) ≫ proj J A B q N =
      proj J A B q M ≫ f := by
  apply restrictSheafify_hom_ext
  intro U t
  exact (congrArg ((proj J A B q N).val.app U) (changeOfRingsHom_apply J A B f U t)).trans
    (proj_extendScalars_map J A B q f U t)

end Projections

end CategoryTheory.ConstantModuleScalar
