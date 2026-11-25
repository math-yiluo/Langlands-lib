/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Prod
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor with scalar restriction on a ringed site

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md, Step 2;
Stacks Project, Tags 03EK, 06YS, 06YU, 06YY
(blueprint: lem-trf-site-derived-tensor-restriction).

The comparison on one K-flat factor is normalized by the recorded two-factor descent
comparison. The representative formula uses this comparison, the change-of-rings counit,
and the exact restriction factorization. A single family `e` occurs in both the naturality
and representative clauses. Local pure tensors specify both directions of the chain map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

universe u v r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}










/-- Termwise restriction, exactly the recorded scalar restriction functor.
Source: Stacks, Tag 03DA (blueprint: lem-trf-site-derived-tensor-restriction). -/
abbrev siteTensorRestriction (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Local section of change of rings, through its actual module-sheafification unit.
The conventional order in `changeOfRings` is `s ⊗ x`, representing `x ⊗ s` in the paper.
Source: Stacks, Tag 03EK (blueprint: lem-trf-site-derived-tensor-restriction). -/
def siteExtensionTmul (φ : R ⟶ S) (M : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (E₀ : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
          (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) : (E₀.obj M).val.obj U :=
  (eqToHom (hobj M).symm).val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

set_option hygiene false in
local notation "𝓜" A:arg => ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)

set_option backward.isDefEq.respectTransparency true

section TensorProof

set_option backward.isDefEq.respectTransparency false in
private abbrev siteSectionModule (A : Sheaf J CommRingCat.{r}) (M : 𝓜 A) (V : Cᵒᵖ) :
    Module (A.obj.obj V) (M.val.obj V) :=
  ModuleCat.isModule (M.val.obj V)

attribute [local instance] siteSectionModule

private theorem tensorSheafificationNaturality
    (A : Sheaf J CommRingCat.{r})
    {M M' N N' : 𝓜 A} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory A
    tensorHom f g ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)).map (tensorHom f.val g.val) := by
  exact SheafOfModules.changeOfRingsTensorIso_naturality_independentCoefficients A f g

private def tensorSwap (A : Sheaf J CommRingCat.{r}) (M N : 𝓜 A) :
    (SheafOfModules.monoidalCategory A).tensorObj M N ≅
      (SheafOfModules.monoidalCategory A).tensorObj N M :=
  SheafOfModules.tensorObjIsoSheafification M N ≪≫
    (PresheafOfModules.sheafification (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)).mapIso (β_ M.val N.val) ≪≫
    (SheafOfModules.tensorObjIsoSheafification N M).symm

private theorem tensorSwap_tmul (M N : 𝓜 R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorSwap R M N).hom.val.app U (siteMonoidalTmul M N U x y) =
      siteMonoidalTmul N M U y x := by
  let O := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let e' := SheafOfModules.tensorObjIsoSheafification N M
  let t := (adj.unit.app (tensorObj M.val N.val)).app U (x ⊗ₜ[R.obj.obj U] y)
  have hi : e.hom.val.app U (e.inv.val.app U t) = t :=
    congrArg (fun f ↦ f.val.app U t) e.inv_hom_id
  have hn := congrArg (fun f ↦ (f.app U) (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality (β_ M.val N.val).hom)
  change (adj.unit.app (tensorObj N.val M.val)).app U (y ⊗ₜ[R.obj.obj U] x) =
    (a.map (β_ M.val N.val).hom).val.app U t at hn
  change e'.inv.val.app U
    ((a.map (β_ M.val N.val).hom).val.app U (e.hom.val.app U (e.inv.val.app U t))) = _
  rw [hi, ← hn]
  rfl

private theorem tensorSwap_inv_tmul (M N : 𝓜 R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorSwap R M N).inv.val.app U (siteMonoidalTmul N M U y x) =
      siteMonoidalTmul M N U x y := by
  rw [← tensorSwap_tmul M N U x y]
  exact congrArg (fun f ↦ f.val.app U (siteMonoidalTmul M N U x y))
    (tensorSwap R M N).hom_inv_id

private theorem tensorSwap_naturality
    (A : Sheaf J CommRingCat.{r}) {M M' N N' : 𝓜 A} (f : M ⟶ M') (g : N ⟶ N') :
    (SheafOfModules.monoidalCategory A).tensorHom f g ≫ (tensorSwap A M' N').hom =
      (tensorSwap A M N).hom ≫ (SheafOfModules.monoidalCategory A).tensorHom g f := by
  let := SheafOfModules.monoidalCategory A
  let a := PresheafOfModules.sheafification (𝟙 ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  apply (cancel_mono (SheafOfModules.tensorObjIsoSheafification N' M').hom).mp
  simp only [tensorSwap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (tensorSheafificationNaturality A f g),
    tensorSheafificationNaturality A g f]
  simp only [Iso.inv_hom_id_assoc]
  rw [← a.map_comp, ← a.map_comp]
  congr 2
  exact BraidedCategory.braiding_naturality f.val g.val

private theorem tensorMap_tmul {M M' N N' : 𝓜 R} (f : M ⟶ M') (g : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorHom f g).val.app U
      (siteMonoidalTmul M N U x y) =
    siteMonoidalTmul M' N' U (f.val.app U x) (g.val.app U y) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let e' := SheafOfModules.tensorObjIsoSheafification M' N'
  let t := (adj.unit.app (tensorObj M.val N.val)).app U (x ⊗ₜ[R.obj.obj U] y)
  have h := tensorSheafificationNaturality R f g
  have h' : e.inv ≫ (SheafOfModules.monoidalCategory R).tensorHom f g =
      (PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val) ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hn := congrArg (fun k ↦ (k.app U) (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality (tensorHom f.val g.val))
  change (adj.unit.app (tensorObj M'.val N'.val)).app U
      ((f.val.app U x) ⊗ₜ[R.obj.obj U] (g.val.app U y)) =
    ((PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val)).val.app U t at hn
  change ((e.inv ≫ (SheafOfModules.monoidalCategory R).tensorHom f g).val.app U) t = _
  rw [h']
  change e'.inv.val.app U
    (((PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val)).val.app U t) = _
  rw [← hn]
  rfl

-- The two coefficient actions require explicit tensor comparison equations.
private theorem ordinaryTensorCancellation (φ : R ⟶ S)
    (E₀ : 𝓜 R ⥤ 𝓜 S)
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M M' : 𝓜 R} (f : M ⟶ M'),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj M').symm) :
    ∃ e : ∀ (M : 𝓜 R) (N : 𝓜 S),
      (SheafOfModules.monoidalCategory R).tensorObj M ((siteTensorRestriction φ).obj N) ≅
      (siteTensorRestriction φ).obj ((SheafOfModules.monoidalCategory S).tensorObj (E₀.obj M) N),
      (∀ {M M' : 𝓜 R} {N N' : 𝓜 S} (f : M ⟶ M') (g : N ⟶ N'),
        (SheafOfModules.monoidalCategory R).tensorHom f ((siteTensorRestriction φ).map g) ≫
          (e M' N').hom = (e M N).hom ≫ (siteTensorRestriction φ).map
            ((SheafOfModules.monoidalCategory S).tensorHom (E₀.map f) g)) ∧
      (∀ (M : 𝓜 R) (N : 𝓜 S) (U : Cᵒᵖ) (x : M.val.obj U)
        (s : S.obj.obj U) (n : N.val.obj U),
        (e M N).inv.val.app U
          (siteMonoidalTmul (E₀.obj M) N U (siteExtensionTmul φ M E₀ hobj U x s) n) =
        siteMonoidalTmul M ((siteTensorRestriction φ).obj N) U x (s • n)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  obtain ⟨k, hk, hksec⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation_sections φ
  let k' (N : 𝓜 S) (M : 𝓜 R) :
      U.obj (tensorObj N (E₀.obj M)) ≅ tensorObj (U.obj N) M :=
    U.mapIso (((curriedTensor _).obj N).mapIso (eqToIso (hobj M))) ≪≫ k N M
  have hknat {N N' : 𝓜 S} {M M' : 𝓜 R} (g : N ⟶ N') (f : M ⟶ M') :
      U.map (tensorHom g (E₀.map f)) ≫ (k' N' M').hom =
        (k' N M).hom ≫ tensorHom (U.map g) f := by
    have hs : tensorHom g (E₀.map f) ≫ (N' ◁ eqToHom (hobj M')) =
        (N ◁ eqToHom (hobj M)) ≫ tensorHom g (SheafOfModules.changeOfRingsHom φ M f) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, hmap, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom g (E₀.map f)) ≫ U.map (N' ◁ eqToHom (hobj M')) ≫
        (k N' M').hom = U.map (N ◁ eqToHom (hobj M)) ≫ (k N M).hom ≫ tensorHom (U.map g) f
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, hk g f]
  have hkinv {N N' : 𝓜 S} {M M' : 𝓜 R} (g : N ⟶ N') (f : M ⟶ M') :
      tensorHom (U.map g) f ≫ (k' N' M').inv =
        (k' N M).inv ≫ U.map (tensorHom g (E₀.map f)) := by
    apply (cancel_epi (k' N M).hom).mp
    rw [← Category.assoc, ← hknat g f]
    simp
  let e (M : 𝓜 R) (N : 𝓜 S) := tensorSwap R M (U.obj N) ≪≫
    (k' N M).symm ≪≫ U.mapIso (tensorSwap S N (E₀.obj M))
  refine ⟨e, ?_, ?_⟩
  · intro M M' N N' f g
    change tensorHom f (U.map g) ≫ (tensorSwap R M' (U.obj N')).hom ≫
        (k' N' M').inv ≫ U.map (tensorSwap S N' (E₀.obj M')).hom =
      (tensorSwap R M (U.obj N)).hom ≫ (k' N M).inv ≫
        U.map (tensorSwap S N (E₀.obj M)).hom ≫ U.map (tensorHom (E₀.map f) g)
    rw [reassoc_of% (tensorSwap_naturality R f (U.map g)), reassoc_of% (hkinv g f)]
    rw [← U.map_comp, ← U.map_comp, tensorSwap_naturality S g (E₀.map f)]
  · intro M N V x s n
    have ht : (eqToHom (hobj M)).val.app V (siteExtensionTmul φ M E₀ hobj V x s) =
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf φ M)).app V)
            (s ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] x) := by
      unfold siteExtensionTmul
      change (((eqToHom (hobj M).symm ≫ eqToHom (hobj M)).val.app V) _) = _
      rw [eqToHom_trans, eqToHom_refl]
      rfl
    change (tensorSwap R M (U.obj N)).inv.val.app V
      ((k N M).hom.val.app V
        ((N ◁ eqToHom (hobj M)).val.app V
          ((tensorSwap S N (E₀.obj M)).inv.val.app V
            (siteMonoidalTmul (E₀.obj M) N V (siteExtensionTmul φ M E₀ hobj V x s) n)))) = _
    rw [tensorSwap_inv_tmul, ← id_tensorHom, tensorMap_tmul, ht]
    change (tensorSwap R M (U.obj N)).inv.val.app V
      ((k N M).hom.val.app V
        (siteMonoidalTmul N (SheafOfModules.changeOfRings φ M) V n _)) = _
    rw [show (k N M).hom.val.app V
        (siteMonoidalTmul N (SheafOfModules.changeOfRings φ M) V n _) =
        siteMonoidalTmul (U.obj N) M V (s • n) x from hksec N M V n s x]
    exact tensorSwap_inv_tmul M (U.obj N) V x (s • n)

private theorem tensorComparison_naturality
    {B : Type*} [Category* B]
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (TR : D₁ × D₁ ⥤ D₁) (TS : D₂ × D₂ ⥤ D₂)
    (E : D₁ ⥤ D₂) (U : D₂ ⥤ D₁) (Z : B ⥤ D₂)
    (ei : ((𝟭 D₁).prod (Z ⋙ U)) ⋙ TR ≅ (E.prod Z) ⋙ TS ⋙ U) :
    (∀ (H H' : D₁) (N : B) (f : H ⟶ H'),
      ((Functor.curry.obj TR).map f).app (U.obj (Z.obj N)) ≫
        (ei.app (H', N)).hom =
      (ei.app (H, N)).hom ≫ U.map
        (((Functor.curry.obj TS).map (E.map f)).app (Z.obj N))) ∧
    (∀ (H : D₁) (N N' : B) (f : N ⟶ N'),
      ((Functor.curry.obj TR).obj H).map (U.map (Z.map f)) ≫
        (ei.app (H, N')).hom =
      (ei.app (H, N)).hom ≫ U.map
        (((Functor.curry.obj TS).obj (E.obj H)).map (Z.map f))) := by
  constructor
  · intro H H' N f
    simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.map_id,
      Iso.app_hom, Functor.curry_obj_obj_obj, Functor.curry_obj_map_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
      using ei.hom.naturality (Prod.mkHom f (𝟙 N))
  · intro H N N' f
    simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.map_id,
      Iso.app_hom, Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
      using ei.hom.naturality (Prod.mkHom (𝟙 H) f)

private theorem descendTensorComparison
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : A ⥤ B) (ff : ((Functor.whiskeringLeft A B D).obj q).FullyFaithful)
    (F G : B ⥤ D) (c : q ⋙ F ≅ q ⋙ G) :
    ∃ e : F ≅ G, ∀ X, e.hom.app (q.obj X) = c.hom.app X := by
  refine ⟨ff.preimageIso c, ?_⟩
  intro X
  exact congr_app (ff.map_preimage c.hom) X

omit [EssentiallySmall.{r} C] in
private theorem restrictionColimits (φ : R ⟶ S) :
    PreservesColimitsOfSize.{0, 0} (siteTensorRestriction φ : 𝓜 S ⥤ 𝓜 R) := by
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
    have : ReflectsColimitsOfShape D (SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (SheafOfModules.toSheaf.{r} _)
  exact ⟨fun {D} instD ↦ @hcolim D instD⟩

private theorem tensorTotal_mapAux
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    let T := F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    (T.map f).app Q ≫ (T.obj P').map g =
      HomologicalComplex.mapBifunctorMap f g F (.up ℤ) := by
  simp only [Functor.map₂HomologicalComplex, HomologicalComplex.mapBifunctorMap,
    Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    ← HomologicalComplex₂.total.map_comp]

private local instance (A : Sheaf J CommRingCat.{r}) (I : Type r) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

private theorem tensorTotal_map
    (A : Sheaf J CommRingCat.{r})
    {P P' Q Q' : CochainComplex (𝓜 A) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    letI := SheafOfModules.monoidalCategory A
    ((SiteTensorComplexFunctor A).map f).app Q ≫
        ((SiteTensorComplexFunctor A).obj P').map g =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (𝓜 A)) (.up ℤ) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.cochainModulesPreadditive A
  exact tensorTotal_mapAux (curriedTensor (𝓜 A)) f g

private def tensorCancellationBicomplexIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    (TR.obj P).obj (UC.obj Q) ≅
      (U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj ((TS.obj (EC.obj P)).obj Q) := by
  exact HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ a (P.X i) (Q.X j)) (by
          intro j j' hj
          change (a (P.X i) (Q.X j)).hom ≫
              U.map ((E₀.obj (P.X i)) ◁ Q.d j j') =
            (P.X i) ◁ U.map (Q.d j j') ≫ (a (P.X i) (Q.X j')).hom
          have h := ha (𝟙 (P.X i)) (Q.d j j')
          simpa only [E₀.map_id, id_tensorHom] using h.symm)) (by
        intro i i' hi
        ext j : 1
        change (a (P.X i) (Q.X j)).hom ≫
            U.map ((E₀.map (P.d i i')) ▷ (Q.X j)) =
          (P.d i i') ▷ U.obj (Q.X j) ≫ (a (P.X i') (Q.X j)).hom
        have h := ha (P.d i i') (𝟙 (Q.X j))
        simpa only [Functor.map_id, tensorHom_id] using h.symm)

private def tensorCancellationComplexIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    (TR.obj P).obj (UC.obj Q) ≅ UC.obj ((TS.obj (EC.obj P)).obj Q) := by
  exact HomologicalComplex₂.total.mapIso
    (tensorCancellationBicomplexIso E₀ U a ha P Q) (.up ℤ) ≪≫
    HomologicalComplex₂.mapTotalIso U
      ((((curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P)).obj Q) (.up ℤ)

private theorem tensorCancellationComplexIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f
        ((U.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor A) (.up ℤ) ≫
      (tensorCancellationComplexIso E₀ U a ha P' Q').hom =
    (tensorCancellationComplexIso E₀ U a ha P Q).hom ≫
      (U.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap
          ((E₀.mapHomologicalComplex (.up ℤ)).map f) g (curriedTensor B) (.up ℤ)) := by
  let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let UU := U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)
  let bd := tensorCancellationBicomplexIso E₀ U a ha
  let dr := (TR.map f).app (UC.obj Q) ≫ (TR.obj P').map (UC.map g)
  let ds := (TS.map (EC.map f)).app Q ≫ (TS.obj (EC.obj P')).map g
  have hn : dr ≫ (bd P' Q').hom = (bd P Q).hom ≫ UU.map ds := by
    ext i j : 2
    change (((f.f i) ▷ U.obj (Q.X j)) ≫ (P'.X i) ◁ U.map (g.f j)) ≫
        (a (P'.X i) (Q'.X j)).hom =
      (a (P.X i) (Q.X j)).hom ≫
        U.map ((E₀.map (f.f i)) ▷ (Q.X j) ≫ E₀.obj (P'.X i) ◁ g.f j)
    simpa only [tensorHom_def] using ha (f.f i) (g.f j)
  change HomologicalComplex₂.total.map dr (.up ℤ) ≫
      HomologicalComplex₂.total.map (bd P' Q').hom (.up ℤ) ≫ _ =
    (HomologicalComplex₂.total.map (bd P Q).hom (.up ℤ) ≫ _) ≫ _
  rw [← HomologicalComplex₂.total.map_comp_assoc, hn,
    HomologicalComplex₂.total.map_comp, Category.assoc]
  have ht := HomologicalComplex₂.mapTotalIso_hom_naturality U ds (.up ℤ)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [HomologicalComplex.mapBifunctorMap, Category.assoc] using
      congrArg (fun t ↦ HomologicalComplex₂.total.map (bd P Q).hom (.up ℤ) ≫ t) ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCancellationComplexIso_ι_inv
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) (i j : ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    U.map (((TS.obj (EC.obj P)).obj Q).ιTotal (.up ℤ) i j (i+j) rfl) ≫
        (tensorCancellationComplexIso E₀ U a ha P Q).inv.f (i+j) =
      (a (P.X i) (Q.X j)).inv ≫
        ((TR.obj P).obj (UC.obj Q)).ιTotal (.up ℤ) i j (i+j) rfl := by
  dsimp only
  let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let DS := (TS.obj (EC.obj P)).obj Q
  let bd := tensorCancellationBicomplexIso E₀ U a ha P Q
  change U.map (DS.ιTotal (.up ℤ) i j (i+j) rfl) ≫
      (HomologicalComplex₂.mapTotalXIso U DS (.up ℤ) (i+j)).inv ≫
        (HomologicalComplex₂.total.map bd.inv (.up ℤ)).f (i+j) = _
  rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc]
  exact HomologicalComplex₂.ιTotal_map
    (K := (U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj DS)
    (L := (TR.obj P).obj (UC.obj Q)) (φ := bd.inv) (c₁₂ := (.up ℤ))
    (i₁ := i) (i₂ := j) (i₁₂ := i+j) (h := rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComplexCancellation
    (φ : R ⟶ S) (E₀ : 𝓜 R ⥤ 𝓜 S) [E₀.Additive]
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M M' : 𝓜 R} (f : M ⟶ M'),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj M').symm)
    [(siteTensorRestriction φ).Additive] :
    let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
    let UC := U.mapHomologicalComplex (.up ℤ)
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    ∃ b : ∀ (P : CochainComplex (𝓜 R) ℤ) (Q : CochainComplex (𝓜 S) ℤ),
      ((SiteTensorComplexFunctor R).obj P).obj (UC.obj Q) ≅
        UC.obj (((SiteTensorComplexFunctor S).obj (EC.obj P)).obj Q),
      (∀ {P P' : CochainComplex (𝓜 R) ℤ} {Q Q' : CochainComplex (𝓜 S) ℤ}
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (((SiteTensorComplexFunctor R).map f).app (UC.obj Q) ≫
          ((SiteTensorComplexFunctor R).obj P').map (UC.map g)) ≫ (b P' Q').hom =
        (b P Q).hom ≫ UC.map
          (((SiteTensorComplexFunctor S).map (EC.map f)).app Q ≫
            ((SiteTensorComplexFunctor S).obj (EC.obj P')).map g)) ∧
      (∀ (P : CochainComplex (𝓜 R) ℤ) (Q : CochainComplex (𝓜 S) ℤ)
        (i j : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V)
        (s : S.obj.obj V) (n : (Q.X j).val.obj V),
        ((b P Q).inv.f (i + j)).val.app V
          (siteTotalTmul (EC.obj P) Q i j V
            (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n) =
        siteTotalTmul P (UC.obj Q) i j V x (s • n)) := by
  dsimp only
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.cochainModulesPreadditive R
  let := SheafOfModules.cochainModulesPreadditive S
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  have : PreservesColimitsOfSize.{0, 0} U := restrictionColimits φ
  let TR := (curriedTensor (𝓜 R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor (𝓜 S)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UU := U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)
  obtain ⟨a, ha, hasec⟩ := ordinaryTensorCancellation φ E₀ hobj hmap
  let b := tensorCancellationComplexIso E₀ U a ha
  refine ⟨b, ?_, ?_⟩
  · intro P P' Q Q' f g
    rw [tensorTotal_map R f (UC.map g), tensorTotal_map S (EC.map f) g]
    exact tensorCancellationComplexIso_naturality E₀ U a ha f g
  · intro P Q i j V x s n
    let DR := (TR.obj P).obj (UC.obj Q)
    let DS := (TS.obj (EC.obj P)).obj Q
    have hi := tensorCancellationComplexIso_ι_inv E₀ U a ha P Q i j
    have hh := congrArg (fun f ↦ f.val.app V
      (siteMonoidalTmul (E₀.obj (P.X i)) (Q.X j) V
        (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n)) hi
    change ((b P Q).inv.f (i+j)).val.app V
        (siteTotalTmul (EC.obj P) Q i j V
          (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n) =
      (DR.ιTotal (.up ℤ) i j (i+j) rfl).val.app V
        ((a (P.X i) (Q.X j)).inv.val.app V
          (siteMonoidalTmul (E₀.obj (P.X i)) (Q.X j) V
            (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n)) at hh
    have hs := hasec (P.X i) (Q.X j) V x s n
    have hs' := congrArg
      (fun z ↦ (DR.ιTotal (.up ℤ) i j (i+j) rfl).val.app V z) hs
    exact hh.trans hs'

end TensorProof

attribute [local instance] siteSectionModule

end CategoryTheory
