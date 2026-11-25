/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.CategoryTheory.SiteConstantModuleHom
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Constant finite free presentations after scalar extension

Source: Stacks Project, Modules on Sites, Tags 03EI, 03DA, 03ER(3), Section 03EK;
blueprint main-20261015, ctf-equals-bc, Local models
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]

/-- The finite categorical power of the regular module, including the empty power.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev power (T : Sheaf J RingCat.{max u v}) (s : ℕ) : SheafOfModules.{max u v} T :=
  ∏ᶜ (fun _ : Fin s ↦ SheafOfModules.unit T)

/-- Evaluate a finite-power projection on sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
abbrev coordinate (T : Sheaf J RingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x : (power J T s).val.obj U) (i : Fin s) : T.obj.obj U :=
  (Pi.π (fun _ : Fin s ↦ SheafOfModules.unit T) i).val.app U x

/-- Evaluate coordinates with the original commutative coefficient carrier.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
abbrev commCoordinate (T : Sheaf J CommRingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T) s).val.obj U)
    (i : Fin s) : T.obj.obj U :=
  coordinate J _ s U x i

variable (B : Sheaf J CommRingCat.{max u v})
  (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

/-- The specified object B tensor P_C, using the recorded scalar-extension construction.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def extension (P : ModuleCat.{max u v} R) :
    SheafOfModules.{max u v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  SheafOfModules.changeOfRingsOfUniverses (C := C) (J := J) σ ((constantModuleHomFunctor J R).obj P)

/-- The specified map id tensor f_C. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
def extensionMap {P Q : ModuleCat.{max u v} R} (f : P ⟶ Q) :
    extension J R B σ P ⟶ extension J R B σ Q :=
  SheafOfModules.changeOfRingsHomOfUniverses (C := C) (J := J) σ
    ((constantModuleHomFunctor J R).obj P)
    ((constantModuleHomFunctor J R).map f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev homCommRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev homRing :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    (homCommRing J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def homRingUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ (homRing J R).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ≫
    (constantModuleHomRingIso J R).hom.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def homUnitLinear (M : ModuleCat.{max u v} R) :
    (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj
        ((constantModuleHomFunctor J R).obj M).val :=
  PresheafOfModules.homMk (constantModuleHomUnit J R M) (fun U r x ↦ by
    have hi := congrArg
      (fun f ↦ f.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r))
      (constantModuleHomRingIso J R).hom_inv_id
    change (constantModuleHomRingIso J R).inv.hom.app U
      ((constantModuleHomRingIso J R).hom.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r at hi
    change (constantModuleHomUnit J R M).app U (r • x) =
      (constantModuleHomRingIso J R).inv.hom.app U
        ((constantModuleHomRingIso J R).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r)) •
        (show ((siteConstantModuleFunctorGeneral J R).obj M).val.obj U from
          (constantModuleHomUnit J R M).app U x)
    rw [hi]
    exact (((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app U).hom.map_smul r x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance unitLinear_surjective (M : ModuleCat.{max u v} R) :
    PresheafOfModules.IsLocallySurjective J (homUnitLinear J R M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance unitLinear_injective (M : ModuleCat.{max u v} R) :
    PresheafOfModules.IsLocallyInjective J (homUnitLinear J R M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private local instance ringUnit_surjective : Presheaf.IsLocallySurjective J (homRingUnit J R) := by
  unfold homRingUnit
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def constantLift (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj N.val) :
    (constantModuleHomFunctor J R).obj M ⟶ N :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (homRingUnit J R) N.isSheaf).symm
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (homUnitLinear J R M) N.isSheaf).symm f)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma constantLift_unit (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (f : (siteConstantModulePresheafGeneral (C := C) R).obj M ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj N.val)
    (U : Cᵒᵖ) (x : M) :
    (constantLift J R M N f).val.app U ((constantModuleHomUnit J R M).app U x) =
      f.app U x := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (homUnitLinear J R M) N.isSheaf).apply_symm_apply f
  exact congrArg (fun t ↦ t.app U x) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma constant_hom_ext (M : ModuleCat.{max u v} R)
    (N : SheafOfModules.{max u v} (homRing J R))
    (a b : (constantModuleHomFunctor J R).obj M ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : M),
      a.val.app U ((constantModuleHomUnit J R M).app U x) =
        b.val.app U ((constantModuleHomUnit J R M).app U x)) : a = b := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext J _ _ N.isSheaf
  ext U x
  exact h U x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def constantOne : ((constantModuleHomFunctor J R).obj (ModuleCat.of R R)).sections :=
  ⟨fun U ↦ (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R),
    fun {_ _} f ↦ (NatTrans.naturality_apply
      (constantModuleHomUnit J R (ModuleCat.of R R)) f (1 : R)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularMap :
    (siteConstantModulePresheafGeneral (C := C) R).obj (ModuleCat.of R R) ⟶
      (PresheafOfModules.restrictScalars (homRingUnit J R)).obj
        (SheafOfModules.unit (homRing J R)).val where
  app U := ModuleCat.ofHom
    (X := ((siteConstantModulePresheafGeneral (C := C) R).obj (ModuleCat.of R R)).obj U)
    (Y := ((PresheafOfModules.restrictScalars (homRingUnit J R)).obj
      (SheafOfModules.unit (homRing J R)).val).obj U)
    { toFun := fun x ↦ (homRingUnit J R).app U x
      map_add' := ((homRingUnit J R).app U).hom.map_add
      map_smul' := fun r x ↦ ((homRingUnit J R).app U).hom.map_mul r x }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact NatTrans.naturality_apply (homRingUnit J R) f x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularHom : (constantModuleHomFunctor J R).obj (ModuleCat.of R R) ⟶
    SheafOfModules.unit (homRing J R) :=
  constantLift J R _ _ (regularMap J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma regularHom_unit (U : Cᵒᵖ) (x : R) :
    (regularHom J R).val.app U
      ((constantModuleHomUnit J R (ModuleCat.of R R)).app U x) =
      (homRingUnit J R).app U x :=
  constantLift_unit J R _ _ (regularMap J R) U x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularInv : SheafOfModules.unit (homRing J R) ⟶
    (constantModuleHomFunctor J R).obj (ModuleCat.of R R) :=
  (SheafOfModules.unitHomEquiv _).symm (constantOne J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma regularInv_apply (U : Cᵒᵖ) (x : (homRing J R).obj.obj U) :
    (regularInv J R).val.app U x =
      x • (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def regularIso : (constantModuleHomFunctor J R).obj (ModuleCat.of R R) ≅
    SheafOfModules.unit (homRing J R) where
  hom := regularHom J R
  inv := regularInv J R
  hom_inv_id := by
    apply constant_hom_ext J R
    intro U x
    change (regularInv J R).val.app U
      ((regularHom J R).val.app U
        ((constantModuleHomUnit J R (ModuleCat.of R R)).app U x)) = _
    rw [regularHom_unit, regularInv_apply]
    change _ = (constantModuleHomUnit J R (ModuleCat.of R R)).app U x
    have h := ((homUnitLinear J R (ModuleCat.of R R)).app U).hom.map_smul x (1 : R)
    change (constantModuleHomUnit J R (ModuleCat.of R R)).app U (x * 1) =
      (homRingUnit J R).app U x •
        (constantModuleHomUnit J R (ModuleCat.of R R)).app U (1 : R) at h
    simpa only [mul_one] using h.symm
  inv_hom_id := by
    apply (SheafOfModules.unitHomEquiv _).injective
    ext U
    change (regularHom J R).val.app U
      ((regularInv J R).val.app U (1 : (homRing J R).obj.obj U)) =
        (1 : (homRing J R).obj.obj U)
    rw [regularInv_apply, one_smul, regularHom_unit, map_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constant_exact :
    exactFunctor _ _ (siteConstantModuleFunctorGeneral J R) := by
  let F := siteConstantModulePresheafGeneral (C := C) R
  let G := PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  have : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ Functor.const Cᵒᵖ)
    infer_instance
  have : PreservesFiniteColimits (F ⋙ G) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ Functor.const Cᵒᵖ)
    infer_instance
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  have : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F G
  exact ⟨comp_preservesFiniteLimits F _, comp_preservesFiniteColimits F _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantHom_limits : PreservesFiniteLimits (constantModuleHomFunctor J R) := by
  let G := SheafOfModules.toSheaf (homRing J R)
  have : PreservesFiniteLimits (constantModuleHomFunctor J R ⋙ G) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ constantSheaf J AddCommGrpCat)
    have : PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{max u v}) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (constantSheaf J AddCommGrpCat.{max u v})
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def alpha (s : ℕ) :
    (constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)) ≅
      power J (homRing J R) s := by
  have := constantHom_limits J R
  exact (constantModuleHomFunctor J R).mapIso
      (ModuleCat.piIsoPi (fun _ : Fin s ↦ ModuleCat.of R R)).symm ≪≫
    PreservesProduct.iso (constantModuleHomFunctor J R) (fun _ : Fin s ↦ ModuleCat.of R R) ≪≫
    Pi.mapIso (fun _ : Fin s ↦ regularIso J R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma alpha_projection (s : ℕ) (i : Fin s) :
    (alpha J R s).hom ≫ Pi.π _ i =
      (constantModuleHomFunctor J R).map
        (ModuleCat.ofHom (LinearMap.proj i : (Fin s → R) →ₗ[R] R)) ≫
          (regularIso J R).hom := by
  simp only [alpha, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    PreservesProduct.iso_hom, Category.assoc, Pi.mapIso_hom_π, piComparison_comp_π_assoc,
    ← Functor.map_comp_assoc, ModuleCat.piIsoPi_inv_kernel_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unit_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((constantModuleHomFunctor J R).map f).val.app U
      ((constantModuleHomUnit J R M).app U x) =
        (constantModuleHomUnit J R N).app U (f x) := by
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) R).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma alpha_unit (s : ℕ) (U : Cᵒᵖ) (x : Fin s → R) (i : Fin s) :
    coordinate J _ s U ((alpha J R s).hom.val.app U
      ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x)) i =
        (homRingUnit J R).app U (x i) := by
  have h := congrArg (fun f ↦ f.val.app U
    ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x))
      (alpha_projection J R s i)
  change coordinate J _ s U ((alpha J R s).hom.val.app U
    ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x)) i = _ at h
  rw [h]
  change (regularHom J R).val.app U
    (((constantModuleHomFunctor J R).map
      (ModuleCat.ofHom (LinearMap.proj i : (Fin s → R) →ₗ[R] R))).val.app U
        ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x)) = _
  rw [unit_naturality, regularHom_unit]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def powerSectionIso (T : Sheaf J RingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ) :
    (power J T s).val.obj U ≅ ModuleCat.of (T.obj.obj U) (Fin s → T.obj.obj U) :=
  PreservesProduct.iso (SheafOfModules.evaluation T U)
      (fun _ : Fin s ↦ SheafOfModules.unit T) ≪≫
    ModuleCat.piIsoPi (fun _ : Fin s ↦ ModuleCat.of (T.obj.obj U) (T.obj.obj U))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma powerSectionIso_apply (T : Sheaf J RingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x : (power J T s).val.obj U) (i : Fin s) :
    (powerSectionIso J T s U).hom x i = coordinate J T s U x i := by
  have h' : (powerSectionIso J T s U).hom ≫ ModuleCat.ofHom
      (LinearMap.proj i : (Fin s → T.obj.obj U) →ₗ[T.obj.obj U] T.obj.obj U) =
        (Pi.π (fun _ : Fin s ↦ SheafOfModules.unit T) i).val.app U := by
    dsimp only [powerSectionIso, Iso.trans_hom]
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      PreservesProduct.iso_hom]
    exact piComparison_comp_π _ _ i
  exact ConcreteCategory.congr_hom h' x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma coordinate_ext (T : Sheaf J RingCat.{max u v}) (s : ℕ) (U : Cᵒᵖ)
    (x y : (power J T s).val.obj U)
    (h : ∀ i, coordinate J T s U x i = coordinate J T s U y i) : x = y := by
  apply (ConcreteCategory.bijective_of_isIso (powerSectionIso J T s U).hom).1
  funext i
  rw [powerSectionIso_apply, powerSectionIso_apply]
  exact h i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def basisSection (s : ℕ) (i : Fin s) :
    ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).sections :=
  ⟨fun U ↦ (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
      (Pi.single i 1),
    fun {_ _} f ↦ (NatTrans.naturality_apply
      (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))) f (Pi.single i 1)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def basisMap (s : ℕ) (i : Fin s) :
    SheafOfModules.unit (homRing J R) ⟶
      (constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)) :=
  (SheafOfModules.unitHomEquiv _).symm (basisSection J R s i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma basisMap_apply (s : ℕ) (i : Fin s) (U : Cᵒᵖ)
    (r : (homRing J R).obj.obj U) :
    (basisMap J R s i).val.app U r =
      r • (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
        (Pi.single i 1) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma sum_eval {T : Sheaf J RingCat.{max u v}}
    {M N : SheafOfModules.{max u v} T} {ι : Type*}
    (t : Finset ι) (f : ι → (M ⟶ N)) (U : Cᵒᵖ) (x : M.val.obj U) :
    (∑ i ∈ t, f i).val.app U x = ∑ i ∈ t, (f i).val.app U x := by
  exact map_sum
    ({ toFun := fun f : M ⟶ N ↦ f.val.app U x
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : (M ⟶ N) →+ N.val.obj U) f t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma basis_decomposition (s : ℕ) (U : Cᵒᵖ)
    (x : ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).val.obj U) :
    x = ∑ i : Fin s, coordinate J _ s U ((alpha J R s).hom.val.app U x) i •
      (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U (Pi.single i 1) := by
  have h : (𝟙 ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)))) =
      ∑ i : Fin s, (alpha J R s).hom ≫ Pi.π _ i ≫ basisMap J R s i := by
    apply constant_hom_ext J R
    intro V y
    change (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app V y = _
    rw [sum_eval]
    change _ = ∑ i : Fin s, (basisMap J R s i).val.app V
      (coordinate J _ s V ((alpha J R s).hom.val.app V
        ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app V y)) i)
    simp only [basisMap_apply, alpha_unit]
    have h := congrArg
      (fun z ↦ (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app V z)
      (pi_eq_sum_univ' y)
    rw [map_sum] at h
    change (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app V y = _
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    exact ((homUnitLinear J R (ModuleCat.of R (Fin s → R))).app V).hom.map_smul
      (y i) (Pi.single i 1)
  have hx := congrArg (fun f ↦ f.val.app U x) h
  rw [sum_eval] at hx
  exact hx

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def scalarPresheafMap
    {M N : SheafOfModules.{max u v} (homRing J R)} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsPresheafOfUniverses (C := C) (J := J) σ M ⟶
      SheafOfModules.changeOfRingsPresheafOfUniverses (C := C) (J := J) σ N where
  app U := show (ModuleCat.extendScalars (σ.hom.app U).hom).obj (M.val.obj U) ⟶
      (ModuleCat.extendScalars (σ.hom.app U).hom).obj (N.val.obj U) from
    (ModuleCat.extendScalars (σ.hom.app U).hom).map (f.val.app U)
  naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses σ M f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def scalarPresheafFunctor :
    SheafOfModules.{max u v} (homRing J R) ⥤
      PresheafOfModules.{max u v} (B.obj ⋙ forget₂ CommRingCat RingCat) where
  obj M := SheafOfModules.changeOfRingsPresheafOfUniverses (C := C) (J := J) σ M
  map f := scalarPresheafMap J R B σ f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (σ.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (σ.hom.app U).hom).map_comp _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def extensionFunctor : ModuleCat.{max u v} R ⥤
    SheafOfModules.{max u v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  constantModuleHomFunctor J R ⋙ scalarPresheafFunctor J R B σ ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev baseRing :=
  (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def scalarToUnit : SheafOfModules.unit (homRing J R) ⟶
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map σ)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) where
  val :=
    { app U := ModuleCat.ofHom
        (X := ModuleCat.of ((homRing J R).obj.obj U) ((homRing J R).obj.obj U))
        (Y := ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map σ)).obj
            (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val.obj U)
        { toFun := fun x ↦ σ.hom.app U x
          map_add' := (σ.hom.app U).hom.map_add
          map_smul' := fun a b ↦ (σ.hom.app U).hom.map_mul a b }
      naturality {U V} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (σ.hom.naturality f) x }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def betaHom (s : ℕ) : extension J R B σ (ModuleCat.of R (Fin s → R)) ⟶
    power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s :=
  Pi.lift (fun i ↦ SheafOfModules.scalarExtensionLift σ _ _
    ((alpha J R s).hom ≫ Pi.π _ i ≫ scalarToUnit J R B σ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma betaHom_tmul (s : ℕ) (U : Cᵒᵖ)
    (x : ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).val.obj U)
    (b : B.obj.obj U) (i : Fin s) :
    coordinate J _ s U ((betaHom J R B σ s).val.app U
      (SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b)) i =
        b * σ.hom.app U (coordinate J _ s U ((alpha J R s).hom.val.app U x) i) := by
  have h := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b))
      (Pi.lift_comp_π (fun i : Fin s ↦ SheafOfModules.scalarExtensionLift σ _ _
        ((alpha J R s).hom ≫ Pi.π _ i ≫ scalarToUnit J R B σ)) i)
  exact h.trans (SheafOfModules.scalarExtensionLift_tmul σ _ _ _ U b x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def extendedBasisSection (s : ℕ) (i : Fin s) :
    (extension J R B σ (ModuleCat.of R (Fin s → R))).sections :=
  ⟨fun U ↦ SheafOfModules.scalarExtensionSection σ _ U 1
      ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U (Pi.single i 1)), by
    intro U V f
    refine (SheafOfModules.scalarExtensionSection_naturality σ _ f 1 _).trans ?_
    have hunit :
        ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).val.map f
          ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
            (Pi.single i 1)) =
          (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app V
            (Pi.single i 1) :=
      (NatTrans.naturality_apply
        (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))) f (Pi.single i 1)).symm
    exact congrArg₂ (fun (b : B.obj.obj V)
      (x : ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).val.obj V) ↦
        SheafOfModules.scalarExtensionSection σ _ V b x)
      (B.obj.map f).hom.map_one hunit⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def betaInv (s : ℕ) :
    power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s ⟶
      extension J R B σ (ModuleCat.of R (Fin s → R)) :=
  ∑ i : Fin s, Pi.π _ i ≫
    (SheafOfModules.unitHomEquiv _).symm (extendedBasisSection J R B σ s i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma betaInv_apply (s : ℕ) (U : Cᵒᵖ)
    (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s).val.obj U) :
    (betaInv J R B σ s).val.app U y = ∑ i : Fin s,
      SheafOfModules.scalarExtensionRingIsoTmul σ _ U
        ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U (Pi.single i 1))
        (coordinate J _ s U y i) := by
  unfold betaInv
  rw [sum_eval]
  apply Finset.sum_congr rfl
  intro i _
  exact (SheafOfModules.scalarExtensionSection_smul σ _ U
    (commCoordinate J B s U y i) 1
    (show ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))).val.obj U from
      (constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
        (Pi.single i 1))).trans (by rw [mul_one]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def beta (s : ℕ) : extension J R B σ (ModuleCat.of R (Fin s → R)) ≅
    power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s where
  hom := betaHom J R B σ s
  inv := betaInv J R B σ s
  hom_inv_id := by
    apply SheafOfModules.scalarExtension_hom_ext σ _
    intro U b x
    change (betaInv J R B σ s).val.app U ((betaHom J R B σ s).val.app U
      (SheafOfModules.scalarExtensionSection σ _ U b x)) =
        SheafOfModules.scalarExtensionSection σ _ U b x
    rw [betaInv_apply]
    simp only [show ∀ U x b, SheafOfModules.scalarExtensionSection σ
      ((constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R))) U b x =
        SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b from fun _ _ _ ↦ rfl,
      betaHom_tmul]
    change (∑ i : Fin s, SheafOfModules.scalarExtensionRingIsoTmul σ _ U
      ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U (Pi.single i 1))
      (b * σ.hom.app U (coordinate J _ s U ((alpha J R s).hom.val.app U x) i))) = _
    conv_rhs => rw [basis_decomposition J R s U x]
    dsimp only [SheafOfModules.scalarExtensionRingIsoTmul]
    rw [TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (SheafOfModules.scalarExtensionSection_base_smul σ _ U b _ _).symm
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext y
    apply coordinate_ext J _ s U
    intro i
    change coordinate J _ s U ((betaHom J R B σ s).val.app U
      ((betaInv J R B σ s).val.app U y)) i = coordinate J _ s U y i
    rw [betaInv_apply, map_sum]
    unfold coordinate
    rw [map_sum]
    simp only [betaHom_tmul, alpha_unit]
    simp [Pi.single_apply, homRingUnit]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def matrixMap (m n : ℕ)
    (A : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R)) :
    power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m ⟶
      power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) n :=
  (beta J R B σ m).inv ≫ extensionMap J R B σ A ≫ (beta J R B σ n).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma matrixMap_commutes (m n : ℕ)
    (A : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R)) :
    extensionMap J R B σ A ≫ (beta J R B σ n).hom =
      (beta J R B σ m).hom ≫ matrixMap J R B σ m n A := by
  simp [matrixMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma extensionMap_tmul {P Q : ModuleCat.{max u v} R} (f : P ⟶ Q)
    (U : Cᵒᵖ) (x : ((constantModuleHomFunctor J R).obj P).val.obj U) (b : B.obj.obj U) :
    (extensionMap J R B σ f).val.app U
      (SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b) =
        SheafOfModules.scalarExtensionRingIsoTmul σ _ U
          (((constantModuleHomFunctor J R).map f).val.app U x) b :=
  SheafOfModules.scalarExtension_map_tmul σ _ U b x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma matrixMap_apply (m n : ℕ)
    (A : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R))
    (U : Cᵒᵖ)
    (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m).val.obj U)
    (i : Fin n) :
    coordinate J _ n U ((matrixMap J R B σ m n A).val.app U y) i = ∑ j : Fin m,
      σ.hom.app U ((homRingUnit J R).app U (A (Pi.single j 1) i)) *
        commCoordinate J _ m U y j := by
  change coordinate J _ n U ((betaHom J R B σ n).val.app U
    ((extensionMap J R B σ A).val.app U ((betaInv J R B σ m).val.app U y))) i = _
  rw [betaInv_apply, map_sum, map_sum]
  unfold coordinate
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change coordinate J _ n U ((betaHom J R B σ n).val.app U
    ((extensionMap J R B σ A).val.app U
      (SheafOfModules.scalarExtensionRingIsoTmul σ _ U
        ((constantModuleHomUnit J R (ModuleCat.of R (Fin m → R))).app U
          (Pi.single j 1)) (coordinate J _ m U y j)))) i = _
  rw [extensionMap_tmul, unit_naturality, betaHom_tmul, alpha_unit, mul_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev restrictedB : SheafOfModules.{max u v} (homRing J R) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map σ)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

open scoped ChangeOfRings in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private def rawFlatIso : scalarPresheafFunctor J R B σ ⋙
      PresheafOfModules.toPresheaf (B.obj ⋙ forget₂ CommRingCat RingCat) ≅
    SheafOfModules.forget (homRing J R) ⋙
      SheafOfModules.siteTensorRight (R := (baseRing J R).obj) (restrictedB J R B σ).val ⋙
        PresheafOfModules.toPresheaf (homRing J R).obj :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun U ↦ (TensorProduct.comm ((baseRing J R).obj.obj U)
      ((restrictedB J R B σ).val.obj U) (M.val.obj U)).toAddEquiv.toAddCommGrpIso)
    (by
      intro U V f
      ext z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul b x =>
        change (TensorProduct.comm ((baseRing J R).obj.obj V)
            ((restrictedB J R B σ).val.obj V) (M.val.obj V))
            (SheafOfModules.changeOfRingsMapOfUniverses σ M f
              (b ⊗ₜ[((baseRing J R).obj.obj U), (σ.hom.app U).hom] x)) =
          M.val.restrictₛₗ f x ⊗ₜ[(baseRing J R).obj.obj V]
            ((restrictedB J R B σ).val.restrictₛₗ f b)
        exact congrArg (fun z ↦
          (TensorProduct.comm ((baseRing J R).obj.obj V)
            ((restrictedB J R B σ).val.obj V) (M.val.obj V)) z)
          (SheafOfModules.changeOfRingsMap_tmulOfUniverses (C := C) (J := J)
            σ M f (show B.obj.obj U from b) x)))
    (by
      intro M N f
      ext U z
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul b x => rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_exact
    (hflat : SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := baseRing J R)
      (restrictedB J R B σ)) :
    exactFunctor _ _ (scalarPresheafFunctor J R B σ ⋙ PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)) := by
  let F := scalarPresheafFunctor J R B σ ⋙ PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)
  let G := SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
  have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight (C := C) (J := J)
      (A := baseRing J R) (restrictedB J R B σ)) :=
    hflat.1
  have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight (C := C) (J := J)
      (A := baseRing J R) (restrictedB J R B σ)) :=
    hflat.2
  let e : F ⋙ G ≅ SheafOfModules.siteSheafTensorRight (C := C) (J := J)
      (A := baseRing J R) (restrictedB J R B σ) ⋙
      SheafOfModules.toSheaf (homRing J R) := by
    let A := presheafToSheaf J AddCommGrpCat.{max u v}
    refine NatIso.ofComponents (fun M ↦ A.mapIso ((rawFlatIso J R B σ).app M)) ?_
    intro M N f
    have h := congrArg A.map ((rawFlatIso J R B σ).hom.naturality f)
    rw [A.map_comp, A.map_comp] at h
    exact h
  have : PreservesFiniteLimits
      (SheafOfModules.siteSheafTensorRight (C := C) (J := J)
        (A := baseRing J R) (restrictedB J R B σ) ⋙
          SheafOfModules.toSheaf (homRing J R)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (SheafOfModules.siteSheafTensorRight (C := C) (J := J)
        (A := baseRing J R) (restrictedB J R B σ) ⋙
          SheafOfModules.toSheaf (homRing J R)) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (F ⋙ G) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (F ⋙ G) := preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F G,
    preservesFiniteColimits_of_reflects_of_preserves F G⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extension_exact
    (hflat : SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := baseRing J R)
      (restrictedB J R B σ)) :
    exactFunctor _ _ (extensionFunctor J R B σ) := by
  let H := constantModuleHomFunctor J R
  let G := SheafOfModules.toSheaf (homRing J R)
  have : PreservesFiniteColimits (H ⋙ G) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ constantSheaf J AddCommGrpCat)
    have : PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{max u v}) :=
      comp_preservesFiniteColimits _ _
    exact comp_preservesFiniteColimits
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (constantSheaf J AddCommGrpCat.{max u v})
  have : PreservesFiniteColimits H := preservesFiniteColimits_of_reflects_of_preserves H G
  have : PreservesFiniteLimits H := constantHom_limits J R
  have : PreservesFiniteLimits (scalarPresheafFunctor J R B σ ⋙
      PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)) :=
    (scalar_exact J R B σ hflat).1
  have : PreservesFiniteColimits (scalarPresheafFunctor J R B σ ⋙
      PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)) :=
    (scalar_exact J R B σ hflat).2
  exact ⟨comp_preservesFiniteLimits H _, comp_preservesFiniteColimits H _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- All finite-power coordinate identifications, the same-matrix equation, and the
specified short exact presentation and isomorphism after scalar extension.
Source: Stacks 03EI, 03DA, 03ER(3), 03EK; blueprint Local models
(auxiliary; not a blueprint node).

Proof: (1) Exact module sequences are exact constant presheaf sequences sectionwise;
exact module sheafification (lem-weil-pbc-site-r-module-presheaf-sheafification-exact)
gives exactness of the recorded constant functor, with the extended scalar actions.
(2) Sheafify coordinate projections; finite-limit preservation gives alpha, including
the empty product. Constant basis vectors go to coordinate basis sections.
(3) On section tensors define beta by b tensor x -> (b sigma(x_i))_i and its inverse
by (b_i) -> sum_i b_i tensor e_i. Balancing and basis expansion show the two composites
are identities. Restrictions commute with both formulas, and the finite power is a
sheaf, so module sheafification gives the asserted isomorphisms.
(4) Apply these formulas to A(e_j); its ith coordinate is a_ij. Thus conjugation gives
exactly the matrix with entries sigma(a_ij). This also proves naturality on finite free
modules. Empty sums handle either rank zero.
(5) Flatness (def-pc-flat-sheaf-modules) makes tensor exact. The tensor symmetry
identifies its order with this scalar extension. Exactness is detected on underlying
abelian sheaves, since kernels are sectionwise and cokernels sheafified sectionwise.
Apply lem-sp-exact-functor-preserves-homology and conjugate by beta: the arrows are
precisely A_B and beta_n.inv followed by E(v).
(6) A specified inverse to v remains inverse after constant sheafification and tensor;
compose with beta.inv. No flatness is used in this last step, including rank zero. -/
theorem constantFiniteFreePresentationExtension :
    exactFunctor _ _ (siteConstantModuleFunctorGeneral J R) ∧
    ∃ α : ∀ s : ℕ, (constantModuleHomFunctor J R).obj (ModuleCat.of R (Fin s → R)) ≅
        power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj (CommRingCat.of R))) s,
    ∃ β : ∀ s : ℕ, extension J R B σ (ModuleCat.of R (Fin s → R)) ≅
        power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s,
      (∀ (s : ℕ) (U : Cᵒᵖ) (x : Fin s → R) (i : Fin s),
        commCoordinate J _ s U ((α s).hom.val.app U
          ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U x)) i =
        (constantModuleHomRingIso J R).hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U (x i))) ∧
      (∀ (s : ℕ) (U : Cᵒᵖ)
        (x : ((constantModuleHomFunctor J R).obj
          (ModuleCat.of R (Fin s → R))).val.obj U) (b : B.obj.obj U) (i : Fin s),
        commCoordinate J _ s U ((β s).hom.val.app U
          (SheafOfModules.scalarExtensionRingIsoTmul σ _ U x b)) i =
        b * σ.hom.app U (commCoordinate J _ s U ((α s).hom.val.app U x) i)) ∧
      (∀ (s : ℕ) (U : Cᵒᵖ)
        (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) s).val.obj U),
        (β s).inv.val.app U y = ∑ i : Fin s,
          SheafOfModules.scalarExtensionRingIsoTmul σ _ U
            ((constantModuleHomUnit J R (ModuleCat.of R (Fin s → R))).app U
              (Pi.single i 1)) (commCoordinate J _ s U y i)) ∧
      (∀ (m n : ℕ) (A : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R)),
        ∃ A_B : power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m ⟶
            power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) n,
          extensionMap J R B σ A ≫ (β n).hom = (β m).hom ≫ A_B ∧
          (∀ (U : Cᵒᵖ)
            (y : (power J ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) m).val.obj U)
            (i : Fin n),
            commCoordinate J _ n U (A_B.val.app U y) i = ∑ j : Fin m,
              σ.hom.app U ((constantModuleHomRingIso J R).hom.hom.app U
                ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U
                  (A (Pi.single j 1) i))) * commCoordinate J _ m U y j) ∧
          (SheafOfModules.IsFlatOnSite (C := C) (J := J)
            (R := (constantSheaf J CommRingCat).obj (CommRingCat.of R))
            ((SheafOfModules.restrictScalars
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map σ)).obj
                (SheafOfModules.unit ((sheafCompose J
                  (forget₂ CommRingCat RingCat)).obj B))) →
            ∀ (P : ModuleCat.{max u v} R) (q : ModuleCat.of R (Fin n → R) ⟶ P),
              Function.Injective A → Function.Exact A q → Function.Surjective q →
              ∃ h : A_B ≫ ((β n).inv ≫ extensionMap J R B σ q) = 0,
                (ShortComplex.mk A_B ((β n).inv ≫ extensionMap J R B σ q) h).ShortExact)) ∧
      (∀ (r : ℕ) (P : ModuleCat.{max u v} R)
        (q : ModuleCat.of R (Fin r → R) ≅ P),
        IsIso ((β r).inv ≫ extensionMap J R B σ q.hom)) := by
  refine ⟨constant_exact J R, alpha J R, beta J R B σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact alpha_unit J R
  · exact betaHom_tmul J R B σ
  · exact betaInv_apply J R B σ
  · intro m n A
    refine ⟨matrixMap J R B σ m n A, matrixMap_commutes J R B σ m n A,
      matrixMap_apply J R B σ m n A, ?_⟩
    intro hflat P q hA hq hsurj
    let F := extensionFunctor J R B σ
    have hF := extension_exact J R B σ hflat
    have : PreservesFiniteLimits F := hF.1
    have : PreservesFiniteColimits F := hF.2
    have : F.PreservesZeroMorphisms := by infer_instance
    have hzero : A ≫ q = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact hq.apply_apply_eq_zero x
    let S := ShortComplex.mk A q hzero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hq hA hsurj
    have hmap := hS.map_of_exact F
    have hz : matrixMap J R B σ m n A ≫
        ((beta J R B σ n).inv ≫ extensionMap J R B σ q) = 0 := by
      change ((beta J R B σ m).inv ≫ F.map A ≫ (beta J R B σ n).hom) ≫
        ((beta J R B σ n).inv ≫ F.map q) = 0
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hzero, F.map_zero, comp_zero]
    refine ⟨hz, ?_⟩
    let T := ShortComplex.mk (matrixMap J R B σ m n A)
      ((beta J R B σ n).inv ≫ extensionMap J R B σ q) hz
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := S.map F) (S₂ := T) (beta J R B σ m) (beta J R B σ n) (Iso.refl _)
        (matrixMap_commutes J R B σ m n A).symm (by
          change (beta J R B σ n).hom ≫ (beta J R B σ n).inv ≫
            extensionMap J R B σ q = extensionMap J R B σ q
          exact (beta J R B σ n).hom_inv_id_assoc _)) hmap
  · intro r P q
    change IsIso ((beta J R B σ r).inv ≫ (extensionFunctor J R B σ).map q.hom)
    infer_instance

end CategoryTheory.ConstantFiniteFreePresentationExtension
