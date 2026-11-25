/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

/-! # Tensor comparison for finite intrinsic coefficients

Source: Stacks Project, Tags 00YV, 03EK and 0GMW.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace FiniteCoefficientTotalComparison

/-- The ordinary tensor-comparison type, shared before any site specialization.
Source: Stacks 03EK and 0GMW
(blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
def Ordinary {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D) : Type _ :=
  tensor C ⋙ G ≅ G.prod G ⋙ tensor D

end FiniteCoefficientTotalComparison

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]

private def scalarSheafify :=
  PresheafOfModules.sheafification.{u + 1} (finiteCoefficientIntrinsicScalarMap X A)

omit [Finite A] in
private theorem scalarSheafify_isIso
    {M N : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A)}
    (f : M ⟶ N) (hf : (Scheme.ProEt.topology X).W f) :
    IsIso ((scalarSheafify X A).map
      ((finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).map f)) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  change IsIso ((presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
    (Functor.whiskerRight f
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})))
  rw [← GrothendieckTopology.W_iff]
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hf ⊢
  have := hf.1
  have := hf.2
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology X) f x⟩

omit [Finite A] in
private theorem tensorUnitMap_isIso
    (M N : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso ((scalarSheafify X A).map
      ((finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).map
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N))) := by
  apply scalarSheafify_isIso
  rw [GrothendieckTopology.W_iff]
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  have h := adj.map_μ_comp_counit_app_tensor M N
  have : IsIso ((presheafToSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).map
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N) ≫
          adj.counit.app (M ⊗ N)) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (M ⊗ N))

/-- The intrinsic module tensor structure, with site and coefficient universes fixed.
Source: Stacks 03EK (blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
@[instance_reducible]
def finiteCoefficientIntrinsicMonoidal : MonoidalCategory
    (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing X A)

attribute [local instance] finiteCoefficientIntrinsicMonoidal

private instance presheafMonoidal : MonoidalCategory (PresheafOfModules.{u + 1}
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))) :=
  PresheafOfModules.monoidalCategory
    (R := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))

private def encodeTensor
    (M N : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj M ⊗
      (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj N ≅
    (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj (M ⊗ N) := by
  refine PresheafOfModules.isoMk (fun U ↦ Iso.refl _) ?_
  intro U V f
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

private def scalarTensorIso :=
  (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    (R := Scheme.proEtaleConstantRing X A) (finiteCoefficientIntrinsicScalarMap X A)).choose

private def encodeTensorNatIso :
    (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).prod
        (finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)) ⋙ tensor _ ≅
      tensor (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
        finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A) := by
  refine NatIso.ofComponents (fun M ↦ encodeTensor X A M.1 M.2) ?_
  intro M N f
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

private def sheafTensorMap :
    (sheafToPresheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).prod
        (sheafToPresheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⋙ tensor _ ⟶
      tensor (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⋙
          sheafToPresheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) where
  app M := Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M.1 M.2
  naturality {M N} f := by
    exact Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) f.1 f.2

private def intrinsicTensorNatIso :
    (finiteCoefficientIntrinsicRealization X A).prod
        (finiteCoefficientIntrinsicRealization X A) ⋙ tensor _ ≅
      tensor (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⋙
          finiteCoefficientIntrinsicRealization X A := by
  let i := sheafToPresheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let P := finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let S := scalarSheafify X A
  let c := Functor.whiskerRight (sheafTensorMap X A) (P ⋙ S)
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact tensorUnitMap_isIso X A M.1 M.2
  exact Functor.isoWhiskerLeft ((i ⋙ P).prod (i ⋙ P)) (scalarTensorIso X A) ≪≫
    Functor.isoWhiskerLeft (i.prod i)
      (Functor.isoWhiskerRight (encodeTensorNatIso X A) S) ≪≫ asIso c

private def intrinsicTensorIso
    (M N : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    (finiteCoefficientIntrinsicRealization X A).obj (M ⊗ N) ≅
      (finiteCoefficientIntrinsicRealization X A).obj M ⊗
        (finiteCoefficientIntrinsicRealization X A).obj N :=
  ((intrinsicTensorNatIso X A).app (M, N)).symm

private def intrinsicSection
    (M : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (U : X.ProEtᵒᵖ) (x : M.obj.obj U) :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientIntrinsicScalarMap X A)).unit.app
      ((finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj M.obj)).app U) x

private def intrinsicPure
    (M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.proEtaleConstantRing X A)).obj)).unit.app
            (M.val ⊗ N.val)).app U (x ⊗ₜ y))

omit [Finite A] in
private theorem intrinsicTensorIso_pure
    (M N : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.ProEtᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U) :
    (intrinsicTensorIso X A M N).hom.val.app U
      (intrinsicSection X A (M ⊗ N) U
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N).app U (x ⊗ₜ y))) =
      intrinsicPure X A ((finiteCoefficientIntrinsicRealization X A).obj M)
        ((finiteCoefficientIntrinsicRealization X A).obj N) U
          (intrinsicSection X A M U x) (intrinsicSection X A N U y) := by
  let P := finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let α := finiteCoefficientIntrinsicScalarMap X A
  let e := scalarTensorIso X A
  have he := (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    (R := Scheme.proEtaleConstantRing X A) α).choose_spec
      (P.obj M.obj) (P.obj N.obj) U x y
  change (e.inv.app (P.obj M.obj, P.obj N.obj)).val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app
      (P.obj M.obj ⊗ P.obj N.obj)).app U (x ⊗ₜ y)) = _ at he
  change _ = intrinsicPure X A ((finiteCoefficientIntrinsicRealization X A).obj M)
    ((finiteCoefficientIntrinsicRealization X A).obj N) U
      (intrinsicSection X A M U x) (intrinsicSection X A N U y) at he
  rw [← he]
  let μ := Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N
  have hn := (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.naturality
    ((encodeTensor X A M.obj N.obj).hom ≫ P.map μ)
  have hn' := congrArg (fun z ↦ z.app U (x ⊗ₜ y)) hn
  change intrinsicSection X A (M ⊗ N) U (μ.app U (x ⊗ₜ y)) =
    ((scalarSheafify X A).map ((encodeTensor X A M.obj N.obj).hom ≫ P.map μ)).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app
        (P.obj M.obj ⊗ P.obj N.obj)).app U (x ⊗ₜ y)) at hn'
  rw [hn']
  have hid : (scalarSheafify X A).map
      ((encodeTensor X A M.obj N.obj).hom ≫ P.map μ) ≫
        (intrinsicTensorIso X A M N).hom = e.inv.app (P.obj M.obj, P.obj N.obj) := by
    apply (cancel_mono (intrinsicTensorIso X A M N).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [intrinsicTensorIso, intrinsicTensorNatIso, Iso.symm_inv, Iso.app_hom,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatIso.ofComponents_hom_app, asIso_hom]
    change _ = e.inv.app (P.obj M.obj, P.obj N.obj) ≫
      (e.hom.app (P.obj M.obj, P.obj N.obj) ≫
        (scalarSheafify X A).map (encodeTensor X A M.obj N.obj).hom) ≫
          (scalarSheafify X A).map (P.map μ)
    rw [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  exact congrArg (fun z ↦ z.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.app
      (P.obj M.obj ⊗ P.obj N.obj)).app U (x ⊗ₜ y))) hid

omit [Finite A] in
private theorem comparisonTensor_pure
    (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)) :
    (Functor.OplaxMonoidal.δ
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X) M N).hom.app
        (op (X.toProEt.obj U))
      ((((comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit.app
        (M ⊗ N)).hom.app (op U))
          ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N).app (op U) (x ⊗ₜ y))) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj M)
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj N)).app
          (op (X.toProEt.obj U))
            ((((comparisonAdjunction (ModuleCat.{u + 1}
              (ULift.{u + 1, u} A)) X).unit.app M).hom.app (op U) x) ⊗ₜ
             (((comparisonAdjunction (ModuleCat.{u + 1}
              (ULift.{u + 1, u} A)) X).unit.app N).hom.app (op U) y)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let adj := comparisonAdjunction B X
  let i := sheafToPresheaf X.smallEtaleTopology B
  have h := congrArg i.map (adj.unit_app_tensor_comp_map_δ M N)
  have h' := congrArg (fun z ↦ Functor.LaxMonoidal.μ i M N ≫ z) h
  simp only [Functor.map_comp] at h'
  rw [← Functor.LaxMonoidal.μ_natural_assoc] at h'
  have h'' := congrArg (fun z ↦ z.app (op U) (x ⊗ₜ y)) h'
  have ht := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    X.toProEt B X.smallEtaleTopology (Scheme.ProEt.topology X)
      (comparisonUpperStar B X |>.obj M) (comparisonUpperStar B X |>.obj N) (op U)
  change _ = _ at h''
  change _ = _ at ht
  have ht' := congrArg (fun z ↦ z
    (((i.map (adj.unit.app M)).app (op U)) x ⊗ₜ
      ((i.map (adj.unit.app N)).app (op U)) y)) ht
  change _ = _ at ht'
  have hh := h''.trans ht'
  dsimp only [i, adj] at hh
  exact hh

private def comparisonTensorNatIso :
    tensor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⋙
        finiteCoefficientIntrinsicComparison X A ≅
      (finiteCoefficientIntrinsicComparison X A).prod
        (finiteCoefficientIntrinsicComparison X A) ⋙ tensor _ :=
  Functor.isoWhiskerRight (Functor.Monoidal.μNatIso
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X)).symm
      (finiteCoefficientIntrinsicRealization X A) ≪≫
    Functor.isoWhiskerLeft
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).prod
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X))
          (intrinsicTensorNatIso X A).symm

/-- Section map through the comparison and module-sheafification units.
Source: Stacks 00YV (blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
def finiteCoefficientComparisonSection
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    ((finiteCoefficientIntrinsicComparison X A).obj M).val.obj (op (X.toProEt.obj U)) :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj M).obj)).app
          (op (X.toProEt.obj U)))
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit.app M).hom.app
      (op U) x)

omit [Finite A] in
private theorem comparisonTensorNatIso_pure
    (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)) :
    ((comparisonTensorNatIso X A).app (M, N)).hom.val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U
        ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N).app (op U) (x ⊗ₜ y))) =
      intrinsicPure X A ((finiteCoefficientIntrinsicComparison X A).obj M)
        ((finiteCoefficientIntrinsicComparison X A).obj N) (op (X.toProEt.obj U))
          (finiteCoefficientComparisonSection X A M U x)
          (finiteCoefficientComparisonSection X A N U y) := by
  let V := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let α := finiteCoefficientIntrinsicScalarMap X A
  let P := finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let δ := Functor.OplaxMonoidal.δ V M N
  let u := (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit
  let μ := Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N
  have hn := (PresheafOfModules.sheafificationAdjunction.{u + 1} α).unit.naturality
    (P.map δ.hom)
  have hn' := congrArg (fun z ↦ z.app (op (X.toProEt.obj U))
    ((u.app (M ⊗ N)).hom.app (op U) (μ.app (op U) (x ⊗ₜ y)))) hn
  change intrinsicSection X A (V.obj M ⊗ V.obj N) (op (X.toProEt.obj U))
      (δ.hom.app (op (X.toProEt.obj U))
        ((u.app (M ⊗ N)).hom.app (op U) (μ.app (op U) (x ⊗ₜ y)))) =
    ((finiteCoefficientIntrinsicRealization X A).map δ).val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U (μ.app (op U) (x ⊗ₜ y))) at hn'
  change (intrinsicTensorIso X A (V.obj M) (V.obj N)).hom.val.app
    (op (X.toProEt.obj U))
    (((finiteCoefficientIntrinsicRealization X A).map δ).val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U (μ.app (op U) (x ⊗ₜ y)))) = _
  rw [← hn']
  rw [comparisonTensor_pure X A M N U x y]
  exact intrinsicTensorIso_pure X A (V.obj M) (V.obj N) (op (X.toProEt.obj U))
    ((u.app M).hom.app (op U) x) ((u.app N).hom.app (op U) y)

/-- Intrinsic pure tensor formed after module sheafification.
Source: Stacks 03EK (blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
def finiteCoefficientIntrinsicPure :
    letI := finiteCoefficientIntrinsicMonoidal X A
    ∀ (M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
      (U : X.ProEtᵒᵖ), M.val.obj U → N.val.obj U → (M ⊗ N).val.obj U :=
  letI := finiteCoefficientIntrinsicMonoidal X A
  fun M N U x y ↦
    (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (Scheme.proEtaleConstantRing X A)).obj)).unit.app
              (M.val ⊗ N.val)).app U (x ⊗ₜ y))

/-- Etale sheaf pure tensor of two sections.
Source: Stacks 03EK (blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
def finiteCoefficientEtalePure
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)) :
    (M ⊗ N).obj.obj (op U) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) M N).app (op U) (x ⊗ₜ y)

/-- The ordinary comparison is normalized on etale pure sections through both units.
Source: Stacks 00YV and 03EK (blueprint: lem-sf-finite-intrinsic-tensor-generators). -/
def FiniteCoefficientTensorNormalization :
    letI := finiteCoefficientIntrinsicMonoidal X A
    FiniteCoefficientTotalComparison.Ordinary
      (finiteCoefficientIntrinsicComparison X A) → Prop :=
  letI := finiteCoefficientIntrinsicMonoidal X A
  fun e ↦ ∀ (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) (U : X.Etale)
      (x : M.obj.obj (op U)) (y : N.obj.obj (op U)),
    (e.app (M, N)).hom.val.app (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A (M ⊗ N) U
        (finiteCoefficientEtalePure X A M N U x y)) =
    finiteCoefficientIntrinsicPure X A
      ((finiteCoefficientIntrinsicComparison X A).obj M)
      ((finiteCoefficientIntrinsicComparison X A).obj N) (op (X.toProEt.obj U))
      (finiteCoefficientComparisonSection X A M U x)
      (finiteCoefficientComparisonSection X A N U y)

omit [Finite A] in
/-- The ordinary comparison preserves tensors, with its value on every etale pure tensor.
Source: Stacks Project, Tags 00YV, 03EK and 0GMW.
(blueprint: lem-sf-finite-intrinsic-tensor-generators).
Proof: the strong monoidal etale-to-pro-etale inverse image gives the first
comparison. Encode fixed-ring presheaves as module presheaves and use the tensor
comparison for module sheafification along the locally bijective constant-ring
unit. The lax tensor map of sheaf inclusion becomes invertible after this
sheafification. Compose these isomorphisms. Naturality of both adjunction units
and their tensor identities give the displayed formula. -/
theorem finiteCoefficientIntrinsicTensor_generators :
    letI := finiteCoefficientIntrinsicMonoidal X A
    ∃ e, FiniteCoefficientTensorNormalization X A e := by
  exact ⟨comparisonTensorNatIso X A, comparisonTensorNatIso_pure X A⟩

end AlgebraicGeometry.ProEtale
