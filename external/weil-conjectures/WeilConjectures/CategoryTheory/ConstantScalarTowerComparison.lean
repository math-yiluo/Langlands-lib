/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Algebra.Homology.Scalar.ScalarDualEvaluationDescent
import all WeilConjectures.Algebra.Homology.Scalar.ScalarDualEvaluationDescent
import all WeilConjectures.CategoryTheory.SiteConstantModuleHom
import all WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement

/-! # Generic scalar comparison used in the rational stratum proof

This is the existing private generic scalar-comparison argument extracted from
RationalStratumFiniteFreeModel to keep compilation below the per-file limit.
Source: Stacks, Tags 03EK and 0GMW; Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-constant-scalar-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- This extracted implementation deliberately adds no public API.
set_option linter.privateModule false
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale.RationalStratum

section
namespace GenericScalar
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J RingCat.{u + 1}]
  [HasWeakSheafify J CommRingCat.{u + 1}]
  {R T : Type (u + 1)} [CommRing R] [CommRing T]
  {B : Sheaf J CommRingCat.{u + 1}} {f : R →+* T}
  {σ : (constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of R) ⟶ B}
  {τ : (constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of T) ⟶ B}
private abbrev directModel (N : ModuleCat.{u + 1} R) :=
  scalarConstantRealization.{u + 1, u} J R B σ N
private abbrev rationalModel (V : ModuleCat.{u + 1} T) :=
  scalarConstantRealization.{u + 1, u} J T B τ V
private abbrev vectorSpace (N : ModuleCat.{u + 1} R) :=
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).obj N
private abbrev vectorUnit (N : ModuleCat.{u + 1} R) (x : N) : vectorSpace (f := f) N :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1} f x
private def Compatible : Prop := ∀ (U : Cᵒᵖ) (r : R),
  ((scalarRingUnit.{u + 1, u} J R B σ).app U).hom r =
    ((scalarRingUnit.{u + 1, u} J T B τ).app U).hom (f r)
private theorem constantScalar_smul (Q : Type (u + 1)) [CommRing Q]
    (σ : (constantSheaf J CommRingCat.{u + 1}).obj
      (CommRingCat.of Q) ⟶ B)
    (N : ModuleCat.{u + 1} Q) (U : Cᵒᵖ) (r : Q) (a : N) :
    scalarConstantGenerator J Q (B) σ N U
      1 (r • a) =
    (scalarRingUnit.{u + 1, u} J Q (B) σ).app U r •
      scalarConstantGenerator J Q (B) σ N U
        1 a := by
  have h := (CategoryTheory.homUnitLinear J Q N).app U |>.hom.map_smul r a
  change (constantModuleHomUnit J Q N).app U (r • a) =
    (CategoryTheory.homRingUnit J Q).app U r • (constantModuleHomUnit J Q N).app U a at h
  change scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ _ U 1 _ = _
  let M := (constantModuleHomFunctor J Q).obj N
  let t := (CategoryTheory.homRingUnit J Q).app U r
  calc
    _ = scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ M U 1
        (t • (constantModuleHomUnit J Q N).app U a) :=
      congrArg (scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ M U 1) h
    _ = scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ M U (1 * σ.hom.app U t)
        ((constantModuleHomUnit J Q N).app U a) :=
      scalarExtensionSection_base_smul.{u + 1, u, u + 1, u + 1} σ M U 1 t _
    _ = σ.hom.app U t • scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ M U 1
        ((constantModuleHomUnit J Q N).app U a) := by
      simpa only [one_mul, mul_one] using
        (scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1} σ M U
          (σ.hom.app U t) 1 ((constantModuleHomUnit J Q N).app U a)).symm
    _ = _ := by rfl

private abbrev directGenerator (N : ModuleCat.{u + 1} R) (U : Cᵒᵖ)
    (a : (B).obj.obj U) (x : N) :=
  scalarConstantGenerator J R (B)
    (σ) N U a x

private abbrev rationalGenerator (V : ModuleCat.{u + 1} T) (U : Cᵒᵖ)
    (a : (B).obj.obj U) (x : V) :=
  scalarConstantGenerator J T (B)
    (τ) V U a x

private def scalarForwardRaw
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    (siteConstantModulePresheafGeneral (C := C) R).obj N ⟶
      (PresheafOfModules.restrictScalars
        (scalarRingUnit.{u + 1, u} J R (B)
          (σ))).obj
        (rationalModel (τ := τ) (vectorSpace (f := f) N)).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars
      (scalarRingUnit.{u + 1, u} J R (B)
        (σ))).obj
          (rationalModel (τ := τ) (vectorSpace (f := f) N)).val).obj U)
    { toFun := fun x ↦ rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1
        (vectorUnit (f := f) N x)
      map_add' := by
        intro x y
        have hv := (ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1}
          (f)).hom.map_add x y
        change rationalGenerator (J := J) (τ := τ) _ U 1 (vectorUnit (f := f) N (x + y)) = _
        change vectorUnit (f := f) N (x + y) =
          vectorUnit (f := f) N x + vectorUnit (f := f) N y at hv
        change scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ U 1 _ = _
        erw [hv]
        erw [((constantModuleHomUnit J T
          (vectorSpace (f := f) N)).app U).hom.map_add]
        exact scalarExtensionSection_add.{u + 1, u, u + 1, u + 1} _ _ _ _ _ _
      map_smul' := by
        intro r x
        have hv := (ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1}
          (f)).hom.map_smul r x
        change vectorUnit (f := f) N (r • x) = f r • vectorUnit (f := f) N x at hv
        change rationalGenerator (J := J) (τ := τ) _ U 1 (vectorUnit (f := f) N (r • x)) = _
        rw [hv]
        exact (constantScalar_smul (J := J) (B := B) T (τ) _ U
          (f r) _).trans (by rw [← hcompat U r]; rfl) }
  naturality {U V} k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change rationalGenerator (J := J) (τ := τ) _ V 1 (vectorUnit (f := f) N x) =
      (rationalModel (τ := τ) (vectorSpace (f := f) N)).val.map k
        (rationalGenerator (J := J) (τ := τ) _ U 1 (vectorUnit (f := f) N x))
    change scalarExtensionSection.{u + 1, u, u + 1, u + 1} (τ) _ V 1 _ =
      (rationalModel (τ := τ) (vectorSpace (f := f) N)).val.map k
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} (τ) _ U 1 _)
    erw [scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}, map_one]
    congr 1
    exact NatTrans.naturality_apply (constantModuleHomUnit J T
      (vectorSpace (f := f) N)) k (vectorUnit (f := f) N x)

private def scalarForward
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    directModel (σ := σ) N ⟶ rationalModel (τ := τ) (vectorSpace (f := f) N) :=
  scalarLift J R (B)
    (σ) N _
    (scalarForwardRaw (J := J) (f := f) (σ := σ) (τ := τ) hcompat N)

private theorem scalarForward_generator
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) (a : (B).obj.obj U) (x : N) :
    (scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
        (directGenerator (J := J) (σ := σ) N U a x) =
      rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U a
        (vectorUnit (f := f) N x) := by
  unfold scalarForward
  erw [scalarLift_generator]
  dsimp only [scalarForwardRaw, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  change a • scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      (τ) _ U 1 _ =
    scalarExtensionSection.{u + 1, u, u + 1, u + 1} (τ) _ U a _
  simpa only [mul_one] using
    (scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1} (τ)
      ((constantModuleHomFunctor J T).obj (vectorSpace (f := f) N))
      U a 1 ((constantModuleHomUnit J T
        (vectorSpace (f := f) N)).app U (vectorUnit (f := f) N x)))

private abbrev backwardSection (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) : ModuleCat.{u + 1} T :=
  ((PresheafOfModules.restrictScalars
    (scalarRingUnit.{u + 1, u} J T (B)
      (τ))).obj (directModel (σ := σ) N).val).obj U

private def backwardUnit
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) : N ⟶ (ModuleCat.restrictScalars (f)).obj
      (backwardSection (J := J) (σ := σ) (τ := τ) N U) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (f)).obj (backwardSection (J := J) (σ := σ) (τ := τ) N U))
    { toFun := fun x ↦ directGenerator (J := J) (σ := σ) N U 1 x
      map_add' := by
        intro x y
        change scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ U 1 _ = _
        erw [((constantModuleHomUnit J R N).app U).hom.map_add]
        exact scalarExtensionSection_add.{u + 1, u, u + 1, u + 1} _ _ _ _ _ _
      map_smul' := by
        intro r x
        exact (constantScalar_smul (J := J) (B := B) R
          (σ) N U r x).trans
          (by rw [hcompat U r]; rfl) }

private def backwardLinear
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) : vectorSpace (f := f) N ⟶ backwardSection (J := J) (σ := σ) (τ := τ) N U :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (f) (backwardUnit (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U)

private theorem backwardLinear_unit
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) (x : N) :
    backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U (vectorUnit (f := f) N x) =
      directGenerator (J := J) (σ := σ) N U 1 x := by
  have h := congrArg (fun f ↦ f x)
    ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (f)).apply_symm_apply (backwardUnit (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U))
  change backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U (vectorUnit (f := f) N x) =
    backwardUnit (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U x at h
  exact h

private def scalarBackwardRaw
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    (siteConstantModulePresheafGeneral (C := C) T).obj (vectorSpace (f := f) N) ⟶
      (PresheafOfModules.restrictScalars
        (scalarRingUnit.{u + 1, u} J T (B)
          (τ))).obj (directModel (σ := σ) N).val where
  app U := backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U
  naturality {U V} k := by
    apply (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (f)).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N V
      (vectorUnit (f := f) N x) =
      (directModel (σ := σ) N).val.map k
        (backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U (vectorUnit (f := f) N x))
    rw [backwardLinear_unit, backwardLinear_unit]
    change scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ V 1 _ =
      (directModel (σ := σ) N).val.map k
        (scalarExtensionSection.{u + 1, u, u + 1, u + 1} _ _ U 1 _)
    erw [scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}, map_one]
    congr 1
    exact NatTrans.naturality_apply (constantModuleHomUnit J R N) k x

private def scalarBackward
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    rationalModel (τ := τ) (vectorSpace (f := f) N) ⟶ directModel (σ := σ) N :=
  scalarLift J T (B)
    (τ) (vectorSpace (f := f) N) _ (scalarBackwardRaw (J := J) (f := f) (σ := σ) (τ := τ) hcompat N)

private theorem scalarBackward_generator
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) (a : (B).obj.obj U) (x : N) :
    (scalarBackward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
        (rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U a
        (vectorUnit (f := f) N x)) =
      directGenerator (J := J) (σ := σ) N U a x := by
  unfold scalarBackward
  erw [scalarLift_generator]
  change a • (show (directModel (σ := σ) N).val.obj U from
    backwardLinear (J := J) (f := f) (σ := σ) (τ := τ) hcompat N U (vectorUnit (f := f) N x)) = _
  rw [backwardLinear_unit]
  change a • scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      (σ) _ U 1 _ =
    scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      (σ) _ U a _
  simpa only [mul_one] using
    (scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
      (σ)
      ((constantModuleHomFunctor J R).obj N)
      U a 1 ((constantModuleHomUnit J R N).app U x))

private theorem generator_add (Q : Type (u + 1)) [CommRing Q]
    (σ : (constantSheaf J CommRingCat.{u + 1}).obj
      (CommRingCat.of Q) ⟶ B)
    (N : ModuleCat.{u + 1} Q) (U : Cᵒᵖ)
    (a : (B).obj.obj U) (x y : N) :
    scalarConstantGenerator J Q (B) σ N U
        a (x + y) =
      scalarConstantGenerator J Q (B) σ N U
        a x +
      scalarConstantGenerator J Q (B) σ N U
        a y := by
  change scalarExtensionSection.{u + 1, u, u + 1, u + 1} σ _ U a _ = _
  erw [((constantModuleHomUnit J Q N).app U).hom.map_add]
  exact scalarExtensionSection_add.{u + 1, u, u + 1, u + 1} σ _ U a _ _

private def rationalUnitLinear (N : ModuleCat.{u + 1} R)
    (U : Cᵒᵖ) : vectorSpace (f := f) N ⟶
      ((PresheafOfModules.restrictScalars
        (scalarRingUnit.{u + 1, u} J T (B)
          (τ))).obj (rationalModel (τ := τ) (vectorSpace (f := f) N)).val).obj
          U :=
  ModuleCat.ofHom (X := vectorSpace (f := f) N)
    (Y := ((PresheafOfModules.restrictScalars
      (scalarRingUnit.{u + 1, u} J T (B)
        (τ))).obj (rationalModel (τ := τ) (vectorSpace (f := f) N)).val).obj U)
    { toFun := fun z ↦ rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 z
      map_add' := generator_add (J := J) (B := B) T (τ) (vectorSpace (f := f) N) U 1
      map_smul' := by
        intro k z
        change rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 (k • z) =
          (scalarRingUnit.{u + 1, u} J T (B)
            (τ)).app U k • rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 z
        exact constantScalar_smul (J := J) (B := B) T (τ) (vectorSpace (f := f) N) U k z }

attribute [local irreducible] scalarForwardRaw backwardUnit backwardLinear scalarBackwardRaw
  scalarForward scalarBackward

private def scalarModelIso
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    directModel (σ := σ) N ≅ rationalModel (τ := τ) (vectorSpace (f := f) N) where
  hom := scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N
  inv := scalarBackward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N
  hom_inv_id := by
    apply scalarHom_ext.{u + 1, u} J R (B)
      (σ) N
    intro U a x
    change (scalarBackward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
      ((scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
        (directGenerator (J := J) (σ := σ) N U a x)) = _
    rw [scalarForward_generator, scalarBackward_generator]
    rfl
  inv_hom_id := by
    apply scalarHom_ext.{u + 1, u} J T (B)
      (τ) (vectorSpace (f := f) N)
    intro U a z
    let g := scalarBackward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N ≫
      scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N
    let RK := PresheafOfModules.restrictScalars
      (scalarRingUnit.{u + 1, u} J T (B)
        (τ))
    have hf : rationalUnitLinear (J := J) (f := f) (τ := τ) N U ≫ (RK.map g.val).app U =
        rationalUnitLinear (J := J) (f := f) (τ := τ) N U := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
        ((scalarBackward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).val.app U
          (rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1
            (vectorUnit (f := f) N x))) =
        rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 (vectorUnit (f := f) N x)
      rw [scalarBackward_generator, scalarForward_generator]
    have h (z : vectorSpace (f := f) N) :
        g.val.app U (rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 z) =
          rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 z :=
      ConcreteCategory.congr_hom hf z
    change g.val.app U (rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U a z) =
      rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U a z
    have hs := scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
      (τ)
      ((constantModuleHomFunctor J T).obj (vectorSpace (f := f) N))
      U a 1 ((constantModuleHomUnit J T
        (vectorSpace (f := f) N)).app U z)
    change a • rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U 1 z =
      rationalGenerator (J := J) (τ := τ) (vectorSpace (f := f) N) U (a * 1) z at hs
    rw [mul_one] at hs
    rw [← hs, map_smul, h]

private theorem scalarModelIso_hom
    (hcompat : Compatible (J := J) (R := R) (T := T) (B := B)
      (f := f) (σ := σ) (τ := τ)) (N : ModuleCat.{u + 1} R) :
    (scalarModelIso (J := J) (f := f) (σ := σ) (τ := τ) hcompat N).hom =
      scalarForward (J := J) (f := f) (σ := σ) (τ := τ) hcompat N := rfl

private theorem scalarModelIso_natural
    (hcompat : Compatible (J := J) (f := f) (σ := σ) (τ := τ))
    {N N' : ModuleCat.{u + 1} R} (g : N ⟶ N') :
    scalarConstantRealizationMap J R B σ g ≫ (scalarModelIso hcompat N').hom =
      (scalarModelIso hcompat N).hom ≫
        scalarConstantRealizationMap J T B τ ((ModuleCat.extendScalars f).map g) := by
  rw [scalarModelIso_hom, scalarModelIso_hom]
  apply scalarHom_ext J R B σ N
  intro U a x
  change (scalarForward hcompat N').val.app U
      ((scalarConstantRealizationMap J R B σ g).val.app U
        (directGenerator (σ := σ) N U a x)) =
    (scalarConstantRealizationMap J T B τ ((ModuleCat.extendScalars f).map g)).val.app U
      ((scalarForward hcompat N).val.app U (directGenerator (σ := σ) N U a x))
  rw [scalarMap_generator, scalarForward_generator, scalarForward_generator,
    scalarMap_generator]
  rfl

/-- Constant scalar realization commutes with an ordinary scalar tower, naturally
and with its prescribed constant generators. Source: Stacks, Tags 03EK and 0GMW;
Bhatt--Scholze, Proposition 6.8.14(2).
(blueprint: lem-per-constant-scalar-tower-comparison).

Proof: Send each generator a tensor x to a tensor (1 tensor x). In the reverse
direction, the ordinary extension/restriction adjunction extends x mapped to
1 tensor x to a linear map on each section. Compatibility of the two scalar units
makes these maps balanced. The adjunction and constant-module universal property
prove naturality and both inverse identities on generators. The same generator
calculation proves naturality in the original module. No finite presentation or
flatness hypothesis is needed. -/
private theorem scalarModel_spec
    (hcompat : Compatible (J := J) (f := f) (σ := σ) (τ := τ)) :
    ∃ e : ∀ N : ModuleCat.{u + 1} R,
        directModel (σ := σ) N ≅ rationalModel (τ := τ) (vectorSpace (f := f) N),
      (∀ (N : ModuleCat.{u + 1} R) (U : Cᵒᵖ) (a : B.obj.obj U) (x : N),
        (e N).hom.val.app U (directGenerator (σ := σ) N U a x) =
          rationalGenerator (τ := τ) (vectorSpace (f := f) N) U a (vectorUnit N x)) ∧
      (∀ {N N' : ModuleCat.{u + 1} R} (g : N ⟶ N'),
        scalarConstantRealizationMap J R B σ g ≫ (e N').hom =
          (e N).hom ≫ scalarConstantRealizationMap J T B τ
            ((ModuleCat.extendScalars f).map g)) := by
  refine ⟨scalarModelIso hcompat, ?_, ?_⟩
  · intro N U a x
    rw [scalarModelIso_hom]
    exact scalarForward_generator hcompat N U a x
  · intro N N' g
    exact scalarModelIso_natural hcompat g

attribute [local irreducible] scalarModelIso


end GenericScalar
end

end AlgebraicGeometry.ProEtale.RationalStratum
