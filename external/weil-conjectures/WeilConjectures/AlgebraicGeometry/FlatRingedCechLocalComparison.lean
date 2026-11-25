/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.RingedScalarExtensionComplexAdjunction
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import all WeilConjectures.AlgebraicGeometry.FlatLocalizationKoszulCohomologyComparison
import WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
import WeilConjectures.AlgebraicGeometry.RingedIdealQuotientComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso

/-! # Flat scalar comparison on a generating slice

Source: Stacks Project, Algebraization, Tags 099H and 099I.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace CategoryTheory

attribute [local irreducible] SheafOfModules.RingedTensor.tensorAdjunction
  SheafOfModules.RingedTensor.tensorFunctor Adjunction.mapHomologicalComplex

private noncomputable def rawScalarIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) :
    let P := (SheafOfModules.RingedTensor.restriction φ).obj
      (SheafOfModules.unit (siteModuleRings B))
    (M.val ⊗ P.val).presheaf ≅
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M).presheaf := by
  refine NatIso.ofComponents (fun X ↦
    (TensorProduct.comm (R.obj.obj X) (M.val.obj X)
      (((SheafOfModules.RingedTensor.restriction φ).obj
        (SheafOfModules.unit (siteModuleRings B))).val.obj X)).toAddEquiv.toAddCommGrpIso) ?_
  intro X Y g
  apply AddCommGrpCat.hom_ext
  ext z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul m b =>
    let : Module (R.obj.obj Y)
        ((ModuleCat.restrictScalars
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map g).hom).obj
            (M.val.obj Y)) :=
      inferInstanceAs (Module (R.obj.obj Y) (M.val.obj Y))
    change B.obj.map g b ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom] M.val.map g m =
      SheafOfModules.changeOfRingsMap φ M g
        (b ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m)
    exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ M g) b m).symm

private noncomputable def underlyingScalarIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) :
    letI := SheafOfModules.monoidalCategory R
    let P := (SheafOfModules.RingedTensor.restriction φ).obj
      (SheafOfModules.unit (siteModuleRings B))
    (SheafOfModules.toSheaf (siteModuleRings R)).obj (M ⊗ P) ≅
      (SheafOfModules.toSheaf (siteModuleRings B)).obj
        ((SheafOfModules.RingedTensor.tensorFunctor φ).obj M) := by
  let := SheafOfModules.monoidalCategory R
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  unfold SheafOfModules.RingedTensor.tensorFunctor
  exact (SheafOfModules.toSheaf (siteModuleRings R)).mapIso
      (SheafOfModules.tensorObjIsoSheafification M P) ≪≫
    (presheafToSheaf J AddCommGrpCat).mapIso (rawScalarIso φ M)

attribute [local semireducible] SheafOfModules.RingedTensor.tensorFunctor

private theorem underlyingScalarIso_pure
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) (X : Cᵒᵖ)
    (m : M.val.obj X) (b : B.obj.obj X) :
    let P := (SheafOfModules.RingedTensor.restriction φ).obj
      (SheafOfModules.unit (siteModuleRings B))
    (underlyingScalarIso φ M).hom.hom.app X
        (SheafOfModules.RingedTensor.pure R M P X m b) =
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (siteModuleRings B).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app X
            (b ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) := by
  let := SheafOfModules.monoidalCategory R
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  let S := presheafToSheaf J AddCommGrpCat.{u}
  let η := (sheafificationAdjunction J AddCommGrpCat.{u}).unit
  have hc := congrArg (fun a ↦ (V.map a).hom.app X
      (((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (siteModuleRings R).obj)).unit.app (M.val ⊗ P.val)).app X
          (m ⊗ₜ[R.obj.obj X] b)))
    (SheafOfModules.tensorObjIsoSheafification M P).inv_hom_id
  have hn := η.naturality (rawScalarIso φ M).hom
  have hn' := congrArg (fun a ↦ a.app X (m ⊗ₜ[R.obj.obj X] b)) hn
  dsimp only [underlyingScalarIso, Iso.trans_hom, Functor.mapIso_hom,
    SheafOfModules.RingedTensor.pure, id]
  change (S.map (rawScalarIso φ M).hom).hom.app X
    ((V.map (SheafOfModules.tensorObjIsoSheafification M P).hom).hom.app X
      ((V.map (SheafOfModules.tensorObjIsoSheafification M P).inv).hom.app X _)) = _
  simp only [Functor.map_comp, Functor.map_id] at hc
  change (V.map (SheafOfModules.tensorObjIsoSheafification M P).hom).hom.app X
      ((V.map (SheafOfModules.tensorObjIsoSheafification M P).inv).hom.app X _) = _ at hc
  rw [hc]
  exact hn'.symm

private theorem scalarExtension_unit_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) (X : Cᵒᵖ) (m : M.val.obj X) :
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M).val.app X m =
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (siteModuleRings B).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app X
            ((1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) := by
  rw [← Adjunction.homEquiv_id]
  unfold SheafOfModules.RingedTensor.tensorAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem rightUnitor_pureMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (siteModuleRings R)) :
    letI := SheafOfModules.monoidalCategory R
    SheafOfModules.RingedTensor.pureMap R M (SheafOfModules.unit (siteModuleRings R)) ≫
      (ρ_ M).hom.val = (ρ_ M.val).hom := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)
  rw [← SheafOfModules.LocalizationCech.tensor_rightUnitor_hom R M]
  dsimp only [SheafOfModules.RingedTensor.pureMap, SheafOfModules.comp_val]
  rw [Category.assoc, ← Category.assoc
    (SheafOfModules.tensorObjIsoSheafification M _).inv.val]
  have he := congrArg SheafOfModules.Hom.val
    (SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit (siteModuleRings R))).inv_hom_id
  change (SheafOfModules.tensorObjIsoSheafification M _).inv.val ≫
    (SheafOfModules.tensorObjIsoSheafification M _).hom.val = 𝟙 _ at he
  rw [he, Category.id_comp]
  have hn := adj.unit.naturality (ρ_ M.val).hom
  change (ρ_ M.val).hom ≫ adj.unit.app M.val =
    adj.unit.app _ ≫ ((PresheafOfModules.sheafification (𝟙 (siteModuleRings R).obj)).map
      (ρ_ M.val).hom).val at hn
  erw [← Category.assoc, ← hn, Category.assoc]
  have ht := adj.right_triangle_components M
  change adj.unit.app M.val ≫ (adj.counit.app M).val = 𝟙 _ at ht
  rw [ht]
  exact Category.comp_id _

private theorem rightUnitor_pure
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (siteModuleRings R)) (X : Cᵒᵖ)
    (m : M.val.obj X) (a : R.obj.obj X) :
    letI := SheafOfModules.monoidalCategory R
    (ρ_ M).hom.val.app X (SheafOfModules.RingedTensor.pure R M
      (SheafOfModules.unit (siteModuleRings R)) X m a) = a • m := by
  exact congrArg (fun t ↦ t.app X (m ⊗ₜ[R.obj.obj X] a)) (rightUnitor_pureMap R M)

private theorem underlying_pure_hom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M N : SheafOfModules.{u} (siteModuleRings R))
    (H : Sheaf J AddCommGrpCat.{u}) :
    letI := SheafOfModules.monoidalCategory R
    ∀ {a b : (SheafOfModules.toSheaf (siteModuleRings R)).obj (M ⊗ N) ⟶ H},
    (∀ X m n, a.hom.app X (SheafOfModules.RingedTensor.pure R M N X m n) =
      b.hom.app X (SheafOfModules.RingedTensor.pure R M N X m n)) → a = b := by
  let := SheafOfModules.monoidalCategory R
  intro a b h
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  apply (cancel_epi (V.map (SheafOfModules.tensorObjIsoSheafification M N).inv)).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul m n => exact h X m n

private theorem underlyingScalarIso_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) :
    letI := SheafOfModules.monoidalCategory R
    let u := SheafOfModules.LocalizationCech.unitMap φ
    let V := SheafOfModules.toSheaf (siteModuleRings R)
    V.map ((ρ_ M).inv ≫ M ◁ u) ≫ (underlyingScalarIso φ M).hom =
      V.map ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M) := by
  let := SheafOfModules.monoidalCategory R
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  let u := SheafOfModules.LocalizationCech.unitMap φ
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  apply (cancel_epi (V.map (ρ_ M).hom)).mp
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← V.map_comp, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  apply underlying_pure_hom_ext R M (SheafOfModules.unit (siteModuleRings R))
  intro X m a
  change R.obj.obj X at a
  let : Module (R.obj.obj X) (B.obj.obj X) :=
    Module.compHom (B.obj.obj X) (φ.hom.app X).hom
  change (underlyingScalarIso φ M).hom.hom.app X
      ((M ◁ u).val.app X (SheafOfModules.RingedTensor.pure R M _ X m a)) = _
  have hp := SheafOfModules.RingedTensor.pure_map R (𝟙 M) u X m a
  simp only [tensorHom_def, id_whiskerRight, Category.id_comp] at hp
  change (M ◁ u).val.app X (SheafOfModules.RingedTensor.pure R M _ X m a) =
    SheafOfModules.RingedTensor.pure R M P X m (u.val.app X a) at hp
  rw [hp]
  change (underlyingScalarIso φ M).hom.hom.app X
      (SheafOfModules.RingedTensor.pure R M P X m (u.val.app X a)) =
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M).val.app X
      ((ρ_ M).hom.val.app X (SheafOfModules.RingedTensor.pure R M _ X m a))
  rw [underlyingScalarIso_pure]
  erw [rightUnitor_pure R M X m (show R.obj.obj X from a)]
  rw [scalarExtension_unit_apply]
  congr 1
  have hu := (SheafOfModules.LocalizationCech.unitMap_existsUnique φ).choose_spec.1 X a
  change u.val.app X a = φ.hom.app X a at hu
  rw [hu]
  change (φ.hom.app X a) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m =
    (1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] (a • m)
  rw [TensorProduct.tmul_smul]
  change (φ.hom.app X a) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m =
    (φ.hom.app X a * 1) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m
  rw [mul_one]

private theorem scalar_unit_isIso_iff_tensor_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : SheafOfModules.{u} (siteModuleRings R)) :
    letI := SheafOfModules.monoidalCategory R
    IsIso ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M) ↔
      IsIso ((ρ_ M).inv ≫ M ◁ SheafOfModules.LocalizationCech.unitMap φ) := by
  let := SheafOfModules.monoidalCategory R
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  have he := underlyingScalarIso_unit φ M
  constructor
  · intro h
    have : IsIso (V.map ((ρ_ M).inv ≫
        M ◁ SheafOfModules.LocalizationCech.unitMap φ) ≫
          (underlyingScalarIso φ M).hom) := by rw [he]; infer_instance
    have : IsIso (V.map ((ρ_ M).inv ≫
        M ◁ SheafOfModules.LocalizationCech.unitMap φ)) :=
      IsIso.of_isIso_comp_right _ (underlyingScalarIso φ M).hom
    exact isIso_of_reflects_iso _ V
  · intro h
    have : IsIso (V.map ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M)) := by
      rw [← he]
      infer_instance
    exact isIso_of_reflects_iso _ V

private noncomputable def rawOverScalarIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (U : C) (M : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.slicePresheafRestriction (J := J.over U) (Over.forget U)
      (siteModuleRings B)).obj (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M) ≅
    SheafOfModules.changeOfRingsPresheaf.{u, u, u}
      ((J.overPullback CommRingCat U).map φ) (M.over U) := by
  refine PresheafOfModules.isoMk (fun X ↦ Iso.refl _) ?_
  intro X Y g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul b m =>
    change SheafOfModules.changeOfRingsMap φ M ((Over.forget U).op.map g)
        (b ⊗ₜ[R.obj.obj ((Over.forget U).op.obj X),
          (φ.hom.app ((Over.forget U).op.obj X)).hom] m) =
      SheafOfModules.changeOfRingsMap ((J.overPullback CommRingCat U).map φ) (M.over U) g
        (b ⊗ₜ[(R.over U).obj.obj X,
          (((J.overPullback CommRingCat U).map φ).hom.app X).hom] m)
    exact ((SheafOfModules.exists_changeOfRingsMap φ M
      ((Over.forget U).op.map g)).choose_spec b m).trans
        ((SheafOfModules.exists_changeOfRingsMap
          ((J.overPullback CommRingCat U).map φ) (M.over U) g).choose_spec b m).symm

private noncomputable def scalarOverIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (U : C) (M : SheafOfModules.{u} (siteModuleRings R)) :
    ((SheafOfModules.RingedTensor.tensorFunctor φ).obj M).over U ≅
      (SheafOfModules.RingedTensor.tensorFunctor
        ((J.overPullback CommRingCat U).map φ)).obj (M.over U) :=
  (SheafOfModules.sliceSheafificationIso (J := J.over U)
      (Over.forget U) (siteModuleRings B)).app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M) ≪≫
    (PresheafOfModules.sheafification (𝟙 (siteModuleRings (B.over U)).obj)).mapIso
      (rawOverScalarIso φ U M)

private theorem scalarOverIso_inv_unitRaw
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (U : C) (M : SheafOfModules.{u} (siteModuleRings R)) :
    let φU := (J.overPullback CommRingCat U).map φ
    let P := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M
    let PU := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φU (M.over U)
    let a := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings B).obj)
    let b := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings (B.over U)).obj)
    b.unit.app PU ≫ (scalarOverIso φ U M).inv.val =
      (rawOverScalarIso φ U M).inv ≫
        (SheafOfModules.slicePresheafRestriction (J := J.over U)
          (Over.forget U) (siteModuleRings B)).map (a.unit.app P) := by
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M
  let S := PresheafOfModules.sheafification (𝟙 (siteModuleRings (B.over U)).obj)
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings B).obj)
  let b := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings (B.over U)).obj)
  let V := SheafOfModules.slicePresheafRestriction (J := J.over U)
    (Over.forget U) (siteModuleRings B)
  let c := (SheafOfModules.sliceSheafificationComparison (J := J.over U)
    (Over.forget U) (siteModuleRings B)).app P
  have hc := (b.homEquiv (V.obj P)
      (((PresheafOfModules.sheafification (𝟙 (siteModuleRings B).obj)).obj P).over U)
    ).apply_symm_apply (V.map (a.unit.app P))
  rw [Adjunction.homEquiv_unit] at hc
  change b.unit.app (V.obj P) ≫ c.val = V.map (a.unit.app P) at hc
  have hn := b.unit.naturality (rawOverScalarIso φ U M).inv
  change (rawOverScalarIso φ U M).inv ≫ b.unit.app (V.obj P) =
    b.unit.app _ ≫ (S.map (rawOverScalarIso φ U M).inv).val at hn
  change b.unit.app _ ≫
    ((S.map (rawOverScalarIso φ U M).inv).val ≫ c.val) = _
  rw [← Category.assoc, ← hn, Category.assoc, hc]

private theorem scalarOverIso_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (U : C) (M : SheafOfModules.{u} (siteModuleRings R)) :
    let φU := (J.overPullback CommRingCat U).map φ
    (SheafOfModules.RingedTensor.tensorAdjunction φU).unit.app (M.over U) ≫
        (SheafOfModules.RingedTensor.restriction φU).map (scalarOverIso φ U M).inv =
      ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M).over U := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (scalarOverIso φ U M).inv.val.app X
      (((SheafOfModules.RingedTensor.tensorAdjunction
        ((J.overPullback CommRingCat U).map φ)).unit.app (M.over U)).val.app X m) =
    ((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app M).val.app
      ((Over.forget U).op.obj X) m
  rw [scalarExtension_unit_apply, scalarExtension_unit_apply]
  exact congrArg (fun a ↦ a.app X
    ((1 : (B.over U).obj.obj X) ⊗ₜ[(R.over U).obj.obj X,
      (((J.overPullback CommRingCat U).map φ).hom.app X).hom] m))
    (scalarOverIso_inv_unitRaw φ U M)

attribute [local irreducible] SheafOfModules.RingedTensor.tensorFunctor
  rawOverScalarIso scalarOverIso

private theorem underlyingScalarIso_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    {M N : SheafOfModules.{u} (siteModuleRings R)} (a : M ⟶ N) :
    letI := SheafOfModules.monoidalCategory R
    let P := (SheafOfModules.RingedTensor.restriction φ).obj
      (SheafOfModules.unit (siteModuleRings B))
    (SheafOfModules.toSheaf (siteModuleRings R)).map (a ▷ P) ≫
        (underlyingScalarIso φ N).hom =
      (underlyingScalarIso φ M).hom ≫
        (SheafOfModules.toSheaf (siteModuleRings B)).map
          ((SheafOfModules.RingedTensor.tensorFunctor φ).map a) := by
  let := SheafOfModules.monoidalCategory R
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  let V := SheafOfModules.toSheaf (siteModuleRings R)
  let S := presheafToSheaf J AddCommGrpCat.{u}
  have h := congrArg V.map
    (SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom a P)
  simp only [Functor.map_comp] at h
  unfold SheafOfModules.RingedTensor.tensorFunctor
  dsimp only [underlyingScalarIso, id, Iso.trans_hom, Functor.mapIso_hom]
  change V.map (a ▷ P) ≫
    (V.map (SheafOfModules.tensorObjIsoSheafification N P).hom ≫
      S.map (rawScalarIso φ N).hom) = _
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  apply (cancel_epi (V.map (SheafOfModules.tensorObjIsoSheafification M P).hom)).mpr
  change S.map ((PresheafOfModules.toPresheaf _).map (a.val ▷ P.val)) ≫
      S.map (rawScalarIso φ N).hom =
    S.map (rawScalarIso φ M).hom ≫
      S.map ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.RingedTensor.tensorPresheafFunctor φ).map a))
  rw [← S.map_comp, ← S.map_comp]
  apply congrArg S.map
  ext X z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul m b =>
    change B.obj.obj X at b
    change b ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] a.val.app X m =
      (ModuleCat.extendScalars (φ.hom.app X).hom).map (a.val.app X)
        (b ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m)
    exact (ModuleCat.ExtendScalars.map_tmul _ _ _ _).symm

private noncomputable def underlyingScalarNatIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    let P := (SheafOfModules.RingedTensor.restriction φ).obj
      (SheafOfModules.unit (siteModuleRings B))
    tensorRight P ⋙ SheafOfModules.toSheaf (siteModuleRings R) ≅
      SheafOfModules.RingedTensor.tensorFunctor φ ⋙
        SheafOfModules.toSheaf (siteModuleRings B) := by
  let := SheafOfModules.monoidalCategory R
  exact NatIso.ofComponents (underlyingScalarIso φ)
    (fun a ↦ underlyingScalarIso_naturality φ a)

private theorem scalarExtension_preservesFiniteLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.RingedTensor.restriction φ).obj
        (SheafOfModules.unit (siteModuleRings B)))) :
    PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) := by
  let := SheafOfModules.monoidalCategory R
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (tensorRight P) := hflat.1
  have : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ ⋙
      SheafOfModules.toSheaf (siteModuleRings B)) :=
    preservesFiniteLimits_of_natIso (underlyingScalarNatIso φ)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (siteModuleRings B))

private instance scalarExtension_preservesFiniteColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ) := by
  have := (SheafOfModules.RingedTensor.tensorAdjunction φ).leftAdjoint_preservesColimits
  infer_instance

private instance scalarRestriction_preservesFiniteLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  have : PreservesLimitsOfSize.{0, 0} (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

private instance scalarRestriction_preservesFiniteColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) :=
    SheafOfModules.LocalizationCech.restriction_colimits φ
  exact PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

private theorem isIso_app_of_iso
    {D E : Type*} [Category D] [Category E] {F G : D ⥤ E}
    (η : F ⟶ G) {X Y : D} (e : X ≅ Y) [IsIso (η.app X)] :
    IsIso (η.app Y) := by
  have hn := η.naturality e.hom
  have : IsIso (F.map e.hom ≫ η.app Y) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom) _

private theorem natTrans_quasiIso_iff_homology
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (F G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) (K : CochainComplex D ℤ) :
    QuasiIso ((η.mapHomologicalComplex (.up ℤ)).app K) ↔
      ∀ q, IsIso (η.app (K.homology q)) := by
  rw [quasiIso_iff]
  apply forall_congr'
  intro q
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  let m := ShortComplex.homologyMap ((K.sc q).mapNatTrans η)
  have he := NatTrans.app_homology η (K.sc q)
  constructor
  · intro h
    have : IsIso m := h
    change IsIso (η.app (K.sc q).homology)
    rw [he]
    infer_instance
  · intro h
    have : IsIso (((K.sc q).mapHomologyIso F).inv ≫ m ≫
        ((K.sc q).mapHomologyIso G).hom) := by
      rw [← he]
      exact h
    have : IsIso (m ≫ ((K.sc q).mapHomologyIso G).hom) :=
      IsIso.of_isIso_comp_left ((K.sc q).mapHomologyIso F).inv _
    exact IsIso.of_isIso_comp_right m ((K.sc q).mapHomologyIso G).hom

private theorem natTrans_quasiIso_of_derived_iso
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    [HasDerivedCategory.{w} D]
    (F G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) {K L : CochainComplex D ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L)
    (h : QuasiIso ((η.mapHomologicalComplex (.up ℤ)).app K)) :
    QuasiIso ((η.mapHomologicalComplex (.up ℤ)).app L) := by
  apply (natTrans_quasiIso_iff_homology F G η L).mpr
  intro q
  have := (natTrans_quasiIso_iff_homology F G η K).mp h q
  let hq : K.homology q ≅ L.homology q :=
    ((DerivedCategory.homologyFunctorFactors D q).app K).symm ≪≫
      (DerivedCategory.homologyFunctor D q).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors D q).app L
  exact isIso_app_of_iso η hq

private theorem scalar_unit_quasiIso_of_tensor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.RingedTensor.restriction φ).obj
        (SheafOfModules.unit (siteModuleRings B))))
    (K : ringedSiteComplex R)
    (h : letI := SheafOfModules.monoidalCategory R
      QuasiIso ((((rightUnitorNatIso (SheafOfModules.{u} (siteModuleRings R))).inv ≫
        (tensoringRight _).map (SheafOfModules.LocalizationCech.unitMap φ)).mapHomologicalComplex
          (.up ℤ)).app K)) :
    QuasiIso ((((SheafOfModules.RingedTensor.tensorAdjunction φ).unit).mapHomologicalComplex
      (.up ℤ)).app K) := by
  let := SheafOfModules.monoidalCategory R
  let A := SheafOfModules.{u} (siteModuleRings R)
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (tensorRight P) := hflat.1
  have : PreservesFiniteColimits (tensorRight P) := hflat.2
  have := scalarExtension_preservesFiniteLimits φ hflat
  apply (natTrans_quasiIso_iff_homology (𝟭 A)
    (SheafOfModules.RingedTensor.tensorFunctor φ ⋙ SheafOfModules.RingedTensor.restriction φ)
    (SheafOfModules.RingedTensor.tensorAdjunction φ).unit K).mpr
  intro q
  apply (scalar_unit_isIso_iff_tensor_unit φ (K.homology q)).mpr
  exact (natTrans_quasiIso_iff_homology (𝟭 A) (tensorRight P)
    ((rightUnitorNatIso A).inv ≫
      (tensoringRight A).map (SheafOfModules.LocalizationCech.unitMap φ)) K).mp h q

private theorem generating_row_cokernel_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R) (U : C) (r : ℕ)
    (f : Fin r → R.obj.obj (Opposite.op U))
    (hf : IsRingedIdealGeneratingList R I.module I.inclusion U r f) :
    Nonempty (cokernel (SheafOfModules.LocalizationCech.idealRow (R.over U) r
      (fun i ↦ ⟨(ringedSliceSection R U (f i)).val,
        (ringedSliceSection R U (f i)).property⟩)) ≅ (cokernel I.inclusion).over U) := by
  classical
  obtain ⟨σ, e, he⟩ := hf
  let A := (siteModuleRings R).over U
  let p : (∐ fun _ : Fin r ↦ SheafOfModules.unit A) ⟶ I.module.over U :=
    Sigma.desc (fun i ↦ (I.module.over U).unitHomEquiv.symm (σ.s (e.symm i)))
  have hp : p = (Sigma.reindex e.symm
      (fun _ : σ.I ↦ SheafOfModules.unit A)).hom ≫ σ.π := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ← Category.assoc]
    have h := SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply σ.π (e.symm i)
    have hi := Sigma.ι_reindex_hom e.symm (fun _ : σ.I ↦ SheafOfModules.unit A) i
    calc
      _ = Sigma.ι (fun _ : σ.I ↦ SheafOfModules.unit A) (e.symm i) ≫ σ.π := by
        simpa only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply,
          SheafOfModules.ιFree] using h
      _ = _ := congrArg (fun a ↦ a ≫ σ.π) hi.symm
  have : Epi p := by rw [hp]; infer_instance
  have hrow : p ≫ I.inclusion.over U =
      SheafOfModules.LocalizationCech.idealRow (R.over U) r
        (fun i ↦ ⟨(ringedSliceSection R U (f i)).val,
          (ringedSliceSection R U (f i)).property⟩) := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc, SheafOfModules.unitHomEquiv_symm_comp]
    erw [SheafOfModules.LocalizationCech.idealRow, Sigma.ι_comp_desc]
    change (SheafOfModules.unit A).unitHomEquiv.symm
      (SheafOfModules.sectionsMap (I.inclusion.over U) (σ.s (e.symm i))) =
      (SheafOfModules.unit A).unitHomEquiv.symm
        ⟨(ringedSliceSection R U (f i)).val, (ringedSliceSection R U (f i)).property⟩
    apply congrArg (SheafOfModules.unit A).unitHomEquiv.symm
    apply Subtype.ext
    funext X
    let s := SheafOfModules.sectionsMap (I.inclusion.over U) (σ.s (e.symm i))
    have hn := s.property (Over.homMk X.unop.hom : X.unop ⟶ Over.mk (𝟙 U)).op
    have ht : s.val (Opposite.op (Over.mk (𝟙 U))) = f i := by
      simpa only [Equiv.apply_symm_apply] using he (e.symm i)
    change R.obj.map X.unop.hom.op
      (s.val (Opposite.op (Over.mk (𝟙 U)))) = s.val X at hn
    change s.val X = R.obj.map X.unop.hom.op (f i)
    rw [← hn, ht]
  let a := I.inclusion.over U
  exact ⟨cokernelIsoOfEq hrow.symm ≪≫ cokernelEpiComp p a ≪≫ (PreservesCokernel.iso
    (SheafOfModules.overFunctor (siteModuleRings R) U) I.inclusion).symm⟩

private theorem tensor_unit_cech_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (P : SheafOfModules.{u} (siteModuleRings R))
    (u : SheafOfModules.unit (siteModuleRings R) ⟶ P) (hflat : SheafOfModules.IsFlat P)
    (hQ : letI := SheafOfModules.monoidalCategory R
      IsIso (((rightUnitorNatIso (SheafOfModules.{u} (siteModuleRings R))).inv ≫
        (tensoringRight _).map u).app
          (cokernel (SheafOfModules.LocalizationCech.idealRow R r
            (fun i ↦ ⟨(b i).val, (b i).property⟩))))) :
    letI := SheafOfModules.monoidalCategory R
    QuasiIso ((((rightUnitorNatIso (SheafOfModules.{u} (siteModuleRings R))).inv ≫
      (tensoringRight _).map u).mapHomologicalComplex (.up ℤ)).app
        (ringedExtendedCech R r b).1) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  let := (SheafOfModules.tensorClosed R).2.1.some
  let A := SheafOfModules.{u} (siteModuleRings R)
  let F := tensorRight P
  let η : 𝟭 A ⟶ F := (rightUnitorNatIso A).inv ≫ (tensoringRight A).map u
  have : PreservesFiniteLimits F := hflat.1
  have : PreservesFiniteColimits F := hflat.2
  have : PreservesColimitsOfSize.{0, 0} F :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight P)
  let D := ringedKoszulDiagram R r b
  let T := F.mapHomologicalComplex (.up ℤ)
  let θ := η.mapHomologicalComplex (.up ℤ)
  have hstage : ∀ n, QuasiIso (θ.app (D.obj n)) := by
    intro n
    apply (natTrans_quasiIso_iff_homology (𝟭 A) F η (D.obj n)).mpr
    intro q
    let s := fun i : Fin r ↦ SheafOfModules.LocalizationCech.sectionScalar R
      ⟨(b i).val, (b i).property⟩
    apply SheafOfModules.LocalizationCech.exact_natTrans_nilpotent F η s
      (fun M hM ↦ SheafOfModules.LocalizationCech.tensor_unit_on_killed u
        (fun i ↦ SheafOfModules.LocalizationCech.scalar R ⟨(b i).val, (b i).property⟩)
        hQ M (fun i ↦
          (SheafOfModules.LocalizationCech.sectionScalar_central R
            ⟨(b i).val, (b i).property⟩ M).trans (hM i)))
      (r * (n + 1) + 1) ((D.obj n).homology q)
    exact SheafOfModules.LocalizationCech.sectionScalar_word_zero R r
      (fun i ↦ ⟨(b i).val, (b i).property⟩) _ _
        (ordered_koszul_ideal_power_annihilates_homology R r b n q)
  have : AB5OfSize.{0, 0} (Sheaf J AddCommGrpCat.{u}) :=
    AB5OfSize_shrink.{0, 0, u, u} _
  have : HasExactColimitsOfShape ℕ A :=
    HasExactColimitsOfShape.domain_of_functor ℕ (SheafOfModules.toSheaf (siteModuleRings R))
  have hcolim : QuasiIso (θ.app (colimit D)) := by
    apply MorphismProperty.colimitsOfShape_le (W := HomologicalComplex.quasiIso A (.up ℤ))
      (J := ℕ) _
    exact MorphismProperty.colimitsOfShape.mk' (W := HomologicalComplex.quasiIso A (.up ℤ))
      _ _ _ _ (colimit.isColimit D) (isColimitOfPreserves T (colimit.isColimit D))
      (CategoryTheory.Functor.whiskerLeft D θ) hstage (θ.app (colimit D))
      (fun n ↦ θ.naturality (colimit.ι D n))
  obtain ⟨α, _⟩ := exists_ringed_cech_koszul_colimit_iso R r b
  apply (natTrans_quasiIso_iff_homology (𝟭 A) F η (ringedExtendedCech R r b).1).mpr
  intro q
  have : IsIso (η.app ((colimit D).homology q)) :=
    (natTrans_quasiIso_iff_homology (𝟭 A) F η (colimit D)).mp hcolim q
  exact isIso_app_of_iso η (X := (colimit D).homology q)
    ((HomologicalComplex.homologyFunctor A (.up ℤ) q).mapIso α)

/-- The scalar-extension unit is a quasi-isomorphism after restriction to a slice
where the source is identified with the extended Čech complex for a generating list.
Source: Stacks Project, Algebraization, Tags 099H and 099I.
(auxiliary; not a blueprint node).

Proof: scalar extension is tensor with the restricted target ring after forgetting scalars.
Flatness makes this functor exact. Restriction to a slice commutes with sheafification and
with this tensor, including its unit. The given derived isomorphism therefore identifies
the restricted unit with the tensor unit on the extended Čech complex. The generators
present the ideal sheaf as the image of their finite free row. The quotient hypothesis
identifies its cokernel with the corresponding cokernel over the target ring. For a finite
Koszul stage, multiplication by each generator to the stage exponent is null-homotopic,
using the degree-one-to-degree-zero contraction on its factor. Thus an ideal power kills
its homology. Flat tensor and induction on that power make the tensor unit invertible on
homology. Sequential filtered colimits are exact and preserve those units. The Koszul
colimit is the extended Čech complex, so its tensor unit is a quasi-isomorphism. Transport
along the given derived isomorphism proves the assertion, including the empty list case.
-/
theorem flat_ringedCech_local_unit_quasiIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ) (U : C) (r : ℕ)
    (f : Fin r → R.obj.obj (Opposite.op U))
    (hf : IsRingedIdealGeneratingList R I.module I.inclusion U r f)
    (K : ringedSiteComplex R)
    (e : DerivedCategory.Q.obj
        (ringedExtendedCech (R.over U) r (fun i ↦ ringedSliceSection R U (f i))).1 ≅
      (ringedDerivedRestriction R U).obj (DerivedCategory.Q.obj K)) :
    QuasiIso (((SheafOfModules.overFunctor.{u} (siteModuleRings R) U).mapHomologicalComplex
      (.up ℤ)).map ((ringedScalarExtensionComplexAdjunction φ).unit.app K)) := by
  let : HasDerivedCategory.{w}
      (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U))))
  let V := SheafOfModules.overFunctor (siteModuleRings R) U
  let φU := (J.overPullback CommRingCat U).map φ
  let P := (SheafOfModules.RingedTensor.restriction φ).obj
    (SheafOfModules.unit (siteModuleRings B))
  let PU := (SheafOfModules.RingedTensor.restriction φU).obj
    (SheafOfModules.unit (siteModuleRings (B.over U)))
  let η := (SheafOfModules.RingedTensor.tensorAdjunction φ).unit
  let ηU := (SheafOfModules.RingedTensor.tensorAdjunction φU).unit
  have hflatU : SheafOfModules.IsFlat PU := SheafOfModules.isFlat_over P U hflat
  have := scalarExtension_preservesFiniteLimits φ hflat
  have := scalarExtension_preservesFiniteLimits φU hflatU
  have hQglobal : IsIso (η.app (cokernel I.inclusion)) :=
    RingedSiteIdeal.scalarExtension_unit_cokernel_isIso I φ hquot
  have hQover : IsIso (ηU.app ((cokernel I.inclusion).over U)) := by
    have : IsIso (ηU.app ((cokernel I.inclusion).over U) ≫
        (SheafOfModules.RingedTensor.restriction φU).map
          (scalarOverIso φ U (cokernel I.inclusion)).inv) := by
      rw [scalarOverIso_unit]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((SheafOfModules.RingedTensor.restriction φU).map
        (scalarOverIso φ U (cokernel I.inclusion)).inv)
  obtain ⟨eQ⟩ := generating_row_cokernel_iso R I U r f hf
  have hQrow := isIso_app_of_iso ηU eQ.symm
  let KU := (V.mapHomologicalComplex (.up ℤ)).obj K
  let L := (ringedExtendedCech (R.over U) r (fun i ↦ ringedSliceSection R U (f i))).1
  have hL : QuasiIso ((ηU.mapHomologicalComplex (.up ℤ)).app L) := by
    apply scalar_unit_quasiIso_of_tensor φU hflatU L
    apply tensor_unit_cech_quasiIso (R.over U) r
      (fun i ↦ ringedSliceSection R U (f i)) PU
      (SheafOfModules.LocalizationCech.unitMap φU) hflatU
    exact (scalar_unit_isIso_iff_tensor_unit φU _).mp hQrow
  let e' : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj KU :=
    e ≪≫ V.mapDerivedCategoryFactors.app K
  have hKU : QuasiIso ((ηU.mapHomologicalComplex (.up ℤ)).app KU) :=
    natTrans_quasiIso_of_derived_iso (𝟭 (SheafOfModules.{u}
      (siteModuleRings (R.over U))))
      (SheafOfModules.RingedTensor.tensorFunctor φU ⋙
        SheafOfModules.RingedTensor.restriction φU) ηU e' hL
  have he : (ringedScalarExtensionComplexAdjunction φ).unit.app K =
      ((η.mapHomologicalComplex (.up ℤ)).app K) := by
    unfold ringedScalarExtensionComplexAdjunction Adjunction.mapHomologicalComplex
    rfl
  rw [he]
  change QuasiIso (((CategoryTheory.Functor.whiskerRight η V).mapHomologicalComplex
    (.up ℤ)).app K)
  apply (natTrans_quasiIso_iff_homology V
    ((SheafOfModules.RingedTensor.tensorFunctor φ ⋙
      SheafOfModules.RingedTensor.restriction φ) ⋙ V)
    (CategoryTheory.Functor.whiskerRight η V) K).mpr
  intro q
  have : IsIso (ηU.app (((K.sc q).map V).homology)) :=
    (natTrans_quasiIso_iff_homology (𝟭 (SheafOfModules.{u}
      (siteModuleRings (R.over U))))
      (SheafOfModules.RingedTensor.tensorFunctor φU ⋙
        SheafOfModules.RingedTensor.restriction φU) ηU KU).mp hKU q
  have : IsIso (ηU.app (V.obj (K.homology q))) :=
    isIso_app_of_iso ηU ((K.sc q).mapHomologyIso V)
  change IsIso (((SheafOfModules.RingedTensor.tensorAdjunction φ).unit.app
    (K.homology q)).over U)
  rw [← scalarOverIso_unit φ U (K.homology q)]
  infer_instance

end CategoryTheory
