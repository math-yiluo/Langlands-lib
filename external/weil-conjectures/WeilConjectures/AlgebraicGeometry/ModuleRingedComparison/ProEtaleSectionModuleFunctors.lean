/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FinalRingedUnitMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Normalized tensors on the existing pro-etale module functors

## Main definitions

- `coefficientMap`: the structural section-ring map adjunct to the condensed coefficient map.
- `pushforward`, `pullback`, `adjunction`: the actual ringed module operations and adjunction.
- `ordinaryTensorComparison`, `totalComparison`: uniquely normalized tensor comparisons.
- `pushforwardComposition`, `pullbackComposition`: geometric pasting and its adjunction mate.
- `extension`, `openAdjunction`: the actual open extension and restriction adjunction.

## References

* Stacks Project, Sites, Tag 00YV
* Modules on Sites, Tags 03EK, 03EL, 03D7, 03DI and 03DJ
* Cohomology on Sites, Tags 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem laxMonoidal_ext_mu {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (m n : F.LaxMonoidal) (h : ∀ X Y, m.μ X Y = n.μ X Y) : m = n := by
  let Rm : MonObj (F.obj (𝟙_ C)) := by
    letI := m
    exact F.monObjObj (𝟙_ C)
  let Rn : MonObj (F.obj (𝟙_ C)) := by
    letI := n
    exact F.monObjObj (𝟙_ C)
  have hmul : Rm.mul = Rn.mul :=
    congrArg (fun k ↦ k ≫ F.map (λ_ (𝟙_ C)).hom) (h (𝟙_ C) (𝟙_ C))
  have hε := congrArg (fun p : MonObj (F.obj (𝟙_ C)) ↦ p.one) (MonObj.ext Rm Rn hmul)
  change m.ε ≫ F.map (𝟙 (𝟙_ C)) = n.ε ≫ F.map (𝟙 (𝟙_ C)) at hε
  apply Functor.LaxMonoidal.ext
  · exact (cancel_mono (F.map (𝟙 (𝟙_ C)))).mp hε
  · exact funext fun X ↦ funext fun Y ↦ h X Y

private theorem internalPureTensor_hom_ext (X : Scheme.{u})
    (M N H : internalModules Λ X) {f g : M ⊗ N ⟶ H}
    (h : ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (f.hom.hom.app U) (internalPureTensor Λ X M N U x y) =
        (g.hom.hom.app U) (internalPureTensor Λ X M N U x y)) : f = g := by
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  ext U t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x y => exact h U x y

private theorem internalPushNormalized_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m n : (CondensedRing.lowerStar Λ f).LaxMonoidal)
    (hm : InternalPushNormalized Λ f m) (hn : InternalPushNormalized Λ f n) : m = n := by
  apply laxMonoidal_ext_mu
  intro M N
  apply internalPureTensor_hom_ext Λ Y
  intro U x y
  exact (hm M N U x y).trans (hn M N U x y).symm

@[instance_reducible]
private noncomputable def canonicalInternalPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).LaxMonoidal := by
  letI : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal

private theorem mapMod_tensorπ_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫
        ((ProEtale.upperStar Ab.{u + 1} f).mapModTensorIso M N).inv.hom =
      Functor.OplaxMonoidal.δ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
        Mod.tensorObjπ
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj M)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj N) := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  apply (cancel_mono (F.mapModTensorIso M N).hom.hom).mp
  rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id]
  change F.map (Mod.tensorObjπ M N) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.assoc, F.tensorπ_mapModTensorIso_hom_hom M N, ← Category.assoc,
    Functor.Monoidal.δ_μ, Category.id_comp]

-- The scalar-extension and tensor comparison instances involve large coefficient types.
private theorem upperStar_tensorπ_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    let A := ProEtale.upperStar Ab.{u + 1} f
    let T := A.mapMod (condensedRingObj Λ Y)
    let E := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)
    A.map (Mod.tensorObjπ M N) ≫
        Mod.extendUnitHom (condensedPullbackHom Λ f) (T.obj (M ⊗ N)) ≫
        ((CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N).hom =
      Functor.OplaxMonoidal.δ A M.X N.X ≫
        Mod.tensorObjπ
          ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj (T.obj M))
          ((Mod.comap (asIso (condensedPullbackHom Λ f)).inv).obj (T.obj N)) ≫
        ((E.inv.app (T.obj M) ⊗ₘ E.inv.app (T.obj N))).hom := by
  dsimp only
  let A := ProEtale.upperStar Ab.{u + 1} f
  let T := A.mapMod (condensedRingObj Λ Y)
  let φ := condensedPullbackHom Λ f
  let E := Mod.extendScalarsIsoComapInv φ
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction φ).unit.naturality
      (Functor.OplaxMonoidal.δ T M N))
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    ] at hn
  change A.map (Mod.tensorObjπ M N) ≫ Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    (((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)) ≫
      Functor.OplaxMonoidal.δ (Mod.extendScalars φ) (T.obj M) (T.obj N)).hom = _
  rw [Mod.comp_hom', ← Category.assoc, ← Category.assoc]
  change (Functor.OplaxMonoidal.δ T M N).hom ≫
    Mod.extendUnitHom φ (T.obj M ⊗ T.obj N) =
    Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    ((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)).hom at hn
  rw [Category.assoc (A.map (Mod.tensorObjπ M N)), ← hn]
  rw [Functor.Monoidal.transport_δ, Mod.comp_hom', Mod.comp_hom']
  simp only [Iso.symm_inv, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% (CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f)]
  have hδ : (Functor.OplaxMonoidal.δ T M N).hom =
      (A.mapModTensorIso M N).inv.hom := rfl
  rw [← Category.assoc, ← Category.assoc, hδ, mapMod_tensorπ_delta Λ f M N]
  have hc : Mod.tensorObjπ (T.obj M) (T.obj N) ≫
      (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).inv.hom =
      Mod.tensorObjπ ((Mod.comap (asIso φ).inv).obj (T.obj M))
        ((Mod.comap (asIso φ).inv).obj (T.obj N)) := by
    apply (cancel_mono (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).hom.hom).mp
    rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id]
    change Mod.tensorObjπ (T.obj M) (T.obj N) ≫ 𝟙 _ = _
    rw [Category.comp_id, Mod.tensorπ_comapTensorIso_hom_hom]
  change ((Functor.OplaxMonoidal.δ A M.X N.X ≫ Mod.tensorObjπ (T.obj M) (T.obj N)) ≫
    (Mod.comapTensorIso (asIso φ).inv (T.obj M) (T.obj N)).inv.hom) ≫ _ = _
  simpa only [Category.assoc] using congrArg
    (fun k ↦ Functor.OplaxMonoidal.δ A M.X N.X ≫ k ≫
      ((E.inv.app (T.obj M) ⊗ₘ E.inv.app (T.obj N))).hom) hc

private theorem counit_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ X) :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj
          ((CondensedRing.lowerStar Λ f).obj M)) ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counit.app M.X := by
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ f
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  apply (a.homEquiv _ _).injective
  have hi : adj.homEquiv _ _ (adj.counit.app M) = 𝟙 _ := by
    have h := (adj.homEquiv _ M).apply_symm_apply (𝟙 _)
    rw [adj.homEquiv_symm_id] at h
    exact h
  have h := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ f
    ((CondensedRing.lowerStar Λ f).obj M) M (adj.counit.app M)
  change (adj.homEquiv _ _ (adj.counit.app M)).hom = _ at h
  rw [hi] at h
  have ha := (a.homEquiv _ M.X).apply_symm_apply (𝟙 _)
  rw [a.homEquiv_symm_id] at ha
  rw [Adjunction.homEquiv_unit]
  exact h.symm.trans ha.symm

private theorem normalized_of_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : ∀ M N : internalModules Λ X,
      Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
          ((CondensedRing.lowerStar Λ f).obj N) ≫
        ((canonicalInternalPush Λ f).μ M N).hom =
      Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)) :
    InternalPushNormalized Λ f (canonicalInternalPush Λ f) := by
  intro M N U x y
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have h := NatTrans.IsMonoidal.tensor
    (τ := (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom) M.X N.X
  simp only [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    id_tensorHom_id, Category.id_comp, Category.comp_id, Functor.LaxMonoidal.comp_μ] at h
  have hp := congrArg (fun k ↦ (k.hom.app U)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((CondensedRing.lowerStar Λ f).obj M).X
      ((CondensedRing.lowerStar Λ f).obj N).X).app U) (x ⊗ₜ[ℤ] y))) (hc M N)
  have hU := congrArg (fun k ↦ (k.app U) (x ⊗ₜ[ℤ] y)) h
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      M.X N.X).app (F.op.obj U)) (x ⊗ₜ[ℤ] y) =
    ((Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X).hom.app U)
      (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        ((CondensedRing.lowerStar Λ f).obj M).X
        ((CondensedRing.lowerStar Λ f).obj N).X).app U) (x ⊗ₜ[ℤ] y)) at hU
  exact hp.trans (congrArg (fun z ↦
    (((ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N)).hom.app U) z) hU.symm)

private theorem tensorπ_natural {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] [HasCoequalizers C]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
    [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
    {R : C} [MonObj R] [IsCommMonObj R] {M N P Q : Mod C R}
    (g : M ⟶ P) (h : N ⟶ Q) :
    Mod.tensorObjπ M N ≫ (g ⊗ₘ h).hom =
      (g.hom ⊗ₘ h.hom) ≫ Mod.tensorObjπ P Q := by
  rw [MonoidalCategory.tensorHom_def, Mod.comp_hom',
    Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft, ← Category.assoc,
    ← MonoidalCategory.tensorHom_def]

-- The comparison expands scalar extension only in this underlying-sheaf calculation.
private theorem canonical_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) :
    Mod.tensorObjπ ((CondensedRing.lowerStar Λ f).obj M)
        ((CondensedRing.lowerStar Λ f).obj N) ≫
      ((canonicalInternalPush Λ f).μ M N).hom =
    Functor.LaxMonoidal.μ (ProEtale.lowerStar Ab.{u + 1} f) M.X N.X ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  let : (CondensedRing.upperStar Λ f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal
  let A := ProEtale.upperStar Ab.{u + 1} f
  let G := ProEtale.lowerStar Ab.{u + 1} f
  let H := CondensedRing.lowerStar Λ f
  let T := A.mapMod (condensedRingObj Λ Y)
  let φ := condensedPullbackHom Λ f
  let E := Mod.extendScalarsIsoComapInv φ
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ f
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  let cM := adj.counit.app M
  let cN := adj.counit.app N
  have hu (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (A.obj (condensedRingObj Λ Y))) :
      (E.inv.app K).hom = Mod.extendUnitHom φ K := by
    apply (cancel_mono (E.hom.app K).hom).mp
    rw [← Mod.comp_hom', E.inv_hom_id_app]
    exact (CondensedRing.extendUnitHom_extendScalarsIsoComapInv_hom_app Λ f K).symm
  have hM : (E.inv.app (T.obj (H.obj M)) ≫ cM).hom = a.counit.app M.X := by
    rw [Mod.comp_hom', hu]
    exact counit_underlying Λ f M
  have hN : (E.inv.app (T.obj (H.obj N)) ≫ cN).hom = a.counit.app N.X := by
    rw [Mod.comp_hom', hu]
    exact counit_underlying Λ f N
  have h := congrArg (fun k ↦ k ≫ (cM ⊗ₘ cN).hom)
    (upperStar_tensorπ_delta Λ f (H.obj M) (H.obj N))
  simp only [Category.assoc] at h
  have ht : ((E.inv.app (T.obj (H.obj M)) ⊗ₘ E.inv.app (T.obj (H.obj N)))).hom ≫
      (cM ⊗ₘ cN).hom =
      ((E.inv.app (T.obj (H.obj M)) ≫ cM) ⊗ₘ
        (E.inv.app (T.obj (H.obj N)) ≫ cN)).hom := by
    rw [← Mod.comp_hom', tensorHom_comp_tensorHom]
  rw [ht] at h
  have hn := tensorπ_natural (E.inv.app (T.obj (H.obj M)) ≫ cM)
    (E.inv.app (T.obj (H.obj N)) ≫ cN)
  rw [hM, hN] at hn
  have hr := congrArg (fun k ↦ Functor.OplaxMonoidal.δ A (H.obj M).X (H.obj N).X ≫ k) hn
  have hh := h.trans hr
  have hμ : a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (G.obj M.X) (G.obj N.X) ≫
      (a.counit.app M.X ⊗ₘ a.counit.app N.X)) =
      Functor.LaxMonoidal.μ G M.X N.X := by
    apply (a.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (a.map_μ_comp_counit_app_tensor M.X N.X).symm
  let g := Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f)
    (H.obj M) (H.obj N) ≫ (cM ⊗ₘ cN)
  have hm := CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom Λ f
    (H.obj M ⊗ H.obj N) (M ⊗ N) g
  change (adj.homEquiv _ _ g).hom = a.homEquiv _ _
    (Mod.extendUnitHom φ (T.obj (H.obj M ⊗ H.obj N)) ≫ g.hom) at hm
  change Mod.tensorObjπ (H.obj M) (H.obj N) ≫ (adj.homEquiv _ _ g).hom = _
  rw [hm]
  calc
    _ = a.homEquiv _ _ (A.map (Mod.tensorObjπ (H.obj M) (H.obj N)) ≫
        Mod.extendUnitHom φ (T.obj (H.obj M ⊗ H.obj N)) ≫ g.hom) := by
      rw [Adjunction.homEquiv_naturality_left]
    _ = a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (H.obj M).X (H.obj N).X ≫
        (a.counit.app M.X ⊗ₘ a.counit.app N.X) ≫ Mod.tensorObjπ M N) := by
      apply congrArg
      convert hh using 1 <;> rfl
    _ = a.homEquiv _ _ (Functor.OplaxMonoidal.δ A (G.obj M.X) (G.obj N.X) ≫
        (a.counit.app M.X ⊗ₘ a.counit.app N.X)) ≫ G.map (Mod.tensorObjπ M N) := by
      rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
      rfl
    _ = _ := congrArg (fun k ↦ k ≫ G.map (Mod.tensorObjπ M N)) hμ

private theorem canonicalInternalPush_normalized {X Y : Scheme.{u}} (f : X ⟶ Y) :
    InternalPushNormalized Λ f (canonicalInternalPush Λ f) :=
  normalized_of_projection Λ f (canonical_projection Λ f)

private theorem canonicalInternalPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := canonicalInternalPush Λ f
    (CondensedRing.upperStarLowerStarAdjunction Λ f).leftAdjointOplaxMonoidal =
      (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal := by
  exact (CondensedRing.upperStarLowerStarAdjunction Λ f).laxMonoidalEquivOplaxMonoidal
    |>.apply_symm_apply (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal

private theorem internalPushLax_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y)
    :
    internalPushLax Λ f = canonicalInternalPush Λ f := by
  apply internalPushNormalized_unique Λ f
  · exact (internalPushNormalized_existsUnique Λ f).exists.choose_spec
  · exact canonicalInternalPush_normalized Λ f
private theorem internalPullOplax_eq_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPullOplax Λ f = (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal := by
  change (CondensedRing.upperStarLowerStarAdjunction Λ f).laxMonoidalEquivOplaxMonoidal
    (internalPushLax Λ f) = _
  rw [internalPushLax_eq_canonical Λ f]
  exact canonicalInternalPull_eq Λ f

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] Mod.monoidalCategoryStruct
  InternalAbelianSheafModule.comparison_tensorIso
  InternalAbelianSheafModule.comparison_unitIso
  InternalAbelianSheafModule.comparison_totalIso

attribute [local irreducible] Adjunction.leftAdjointOplaxMonoidal
  Adjunction.rightAdjointLaxMonoidal

attribute [local irreducible] canonicalInternalPush CondensedRing.monoidal_upperStar
  Mod.extendScalars CondensedRing.upperStarLowerStarAdjunction

private theorem existsUnique_of_normalized_pairing {A : Sort*} {P Q : A → Prop}
    (h : ∃ a, P a ∧ Q a ∧ ∀ b, P b → b = a) : ∃! a, P a := by
  obtain ⟨a, ha, _, hu⟩ := h
  exact ⟨a, ha, hu⟩

attribute [local irreducible] Mod.inducingFunctorData SheafOfModules.monoidalCategory

private theorem ordinaryTensorComparison_eq (X : Scheme.{u})
    (M N : internalModules Λ X) :
    InternalAbelianSheafModule.comparison_tensorIso
        (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N =
      ordinaryTensorComparison Λ X M N := by
  apply (ordinaryTensorComparison_existsUnique Λ X M N).unique
  · exact InternalAbelianSheafModule.comparison_tensorIso_tmul
      (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N
  · exact (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec

attribute [local irreducible] ordinaryTensorComparison

private theorem pullTensor_tensorComparison_apply (X : Scheme.{u}) (M N : internalModules Λ X)
    (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((ordinaryTensorComparison Λ X M N).hom.val.app U)
        (internalPureTensor Λ X M N U x y) =
      sectionPureTensor Λ X ((equivalence Λ X).functor.obj M)
        ((equivalence Λ X).functor.obj N) U x y :=
  by
    simpa only [ordinaryTensorComparison] using
      (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose_spec U x y

private theorem pullTensor_changeIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (e e' : ∀ M N : C, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (he : ∀ M N, e M N = e' M N)
    (hn : ∀ (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (e M' N').hom = (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N') :
    F.map (f ⊗ₘ g) ≫ (e' M' N').hom = (e' M N).hom ≫ (F.map f ⊗ₘ F.map g) := by
  rw [← he M N, ← he M' N']
  exact hn M M' N N' f g

private theorem ordinaryTensorComparison_natural (X : Scheme.{u})
    (M M' N N' : internalModules Λ X) (f : M ⟶ M') (g : N ⟶ N') :
    (equivalence Λ X).functor.map (f ⊗ₘ g) ≫ (ordinaryTensorComparison Λ X M' N').hom =
      (ordinaryTensorComparison Λ X M N).hom ≫
        ((equivalence Λ X).functor.map f ⊗ₘ (equivalence Λ X).functor.map g) := by
  exact pullTensor_changeIso (equivalence Λ X).functor
    (fun A B ↦ InternalAbelianSheafModule.comparison_tensorIso
      (Scheme.ProEt.topology X) (condensedRingObj Λ X) A B)
    (ordinaryTensorComparison Λ X) (ordinaryTensorComparison_eq Λ X)
    (fun A A' B B' h k ↦ InternalAbelianSheafModule.comparison_tensorIso_natural
      (Scheme.ProEt.topology X) (condensedRingObj Λ X) A A' B B' h k) M M' N N' f g

section PullTensorProof

section PullTensorTransport

set_option backward.isDefEq.respectTransparency true

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
  {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
  {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
  {B' : Type u₄} [Category.{v₄} B'] [MonoidalCategory B']

omit [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory A']
  [MonoidalCategory B'] in
private theorem pullTensor_hom_mate_transport
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

private theorem pullTensor_mate_formula
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R) [R.LaxMonoidal] (M N : A) :
    a.homEquiv _ _ (a.leftAdjointOplaxMonoidal.δ M N) =
      (a.unit.app M ⊗ₘ a.unit.app N) ≫ Functor.LaxMonoidal.μ R (L.obj M) (L.obj N) := by
  rw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.apply_symm_apply]

private theorem pullTensor_mate_transport
    (E : A ⥤ A') (F : B ⥤ B') (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (b : L' ⊣ R')
    [R.LaxMonoidal] [R'.LaxMonoidal]
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (e : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (g : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (d : ∀ M N, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
    (hn : ∀ {M M' N N'} (s : M ⟶ M') (t : N ⟶ N'),
      E.map (s ⊗ₘ t) ≫ (e M' N').hom =
        (e M N).hom ≫ (E.map s ⊗ₘ E.map t))
    (hunit : ∀ M, E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      R'.map (γ.hom.app M) = b.unit.app (E.obj M))
    (hpair : ∀ M N, (e (R.obj M) (R.obj N)).hom ≫
      (β.hom.app M ⊗ₘ β.hom.app N) ≫ Functor.LaxMonoidal.μ R' (F.obj M) (F.obj N) =
        E.map (Functor.LaxMonoidal.μ R M N) ≫ β.hom.app (M ⊗ N) ≫ R'.map (g M N).hom)
    (hmt : ∀ M N, a.homEquiv _ _ (d M N) =
      (a.unit.app M ⊗ₘ a.unit.app N) ≫ Functor.LaxMonoidal.μ R (L.obj M) (L.obj N))
    :
    (∀ M N, F.map (d M N) ≫ (g (L.obj M) (L.obj N)).hom ≫
      (γ.hom.app M ⊗ₘ γ.hom.app N) =
        γ.hom.app (M ⊗ N) ≫ L'.map (e M N).hom ≫
          b.leftAdjointOplaxMonoidal.δ (E.obj M) (E.obj N)) := by
  have hc := pullTensor_hom_mate_transport E F L R a L' R' b β γ hunit
  intro M N
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

private theorem pullTensor_isIso_of_square
    (E : A ⥤ A') [E.EssSurj] (F : B ⥤ B') (L : A ⥤ B) (L' : A' ⥤ B')
    [L'.OplaxMonoidal] (γ : L ⋙ F ≅ E ⋙ L')
    (e : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (g : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (d : ∀ M N, L.obj (M ⊗ N) ⟶ L.obj M ⊗ L.obj N)
    (hd : ∀ M N, IsIso (d M N))
    (hs : ∀ M N, F.map (d M N) ≫ (g (L.obj M) (L.obj N)).hom ≫
      (γ.hom.app M ⊗ₘ γ.hom.app N) =
        γ.hom.app (M ⊗ N) ≫ L'.map (e M N).hom ≫
          Functor.OplaxMonoidal.δ L' (E.obj M) (E.obj N)) (M N : A') :
    IsIso (Functor.OplaxMonoidal.δ L' M N) := by
  have hi (X₀ Y₀ : A) : IsIso (Functor.OplaxMonoidal.δ L' (E.obj X₀) (E.obj Y₀)) := by
    have := hd X₀ Y₀
    have : IsIso (γ.hom.app (X₀ ⊗ Y₀) ≫ L'.map (e X₀ Y₀).hom ≫
        Functor.OplaxMonoidal.δ L' (E.obj X₀) (E.obj Y₀)) := by
      rw [← hs X₀ Y₀]
      infer_instance
    have : IsIso (L'.map (e X₀ Y₀).hom ≫
        Functor.OplaxMonoidal.δ L' (E.obj X₀) (E.obj Y₀)) :=
      IsIso.of_isIso_comp_left (γ.hom.app (X₀ ⊗ Y₀)) _
    exact IsIso.of_isIso_comp_left (L'.map (e X₀ Y₀).hom) _
  let eM := E.objObjPreimageIso M
  let eN := E.objObjPreimageIso N
  have := hi (E.objPreimage M) (E.objPreimage N)
  have hn := Functor.OplaxMonoidal.δ_natural L' eM.hom eN.hom
  have : IsIso (L'.map (eM.hom ⊗ₘ eN.hom) ≫ Functor.OplaxMonoidal.δ L' M N) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (L'.map (eM.hom ⊗ₘ eN.hom)) _

private theorem pullTensor_mate_isIso
    (E : A ⥤ A') [E.EssSurj] (F : B ⥤ B')
    (L : A ⥤ B) (R : B ⥤ A) (a : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (b : L' ⊣ R')
    [R.LaxMonoidal] [R'.LaxMonoidal]
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (e : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (g : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hn : ∀ (M M' N N' : A) (s : M ⟶ M') (t : N ⟶ N'),
      E.map (s ⊗ₘ t) ≫ (e M' N').hom =
        (e M N).hom ≫ (E.map s ⊗ₘ E.map t))
    (hunit : ∀ M, E.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
      R'.map (γ.hom.app M) = b.unit.app (E.obj M))
    (hpair : ∀ M N, (e (R.obj M) (R.obj N)).hom ≫
      (β.hom.app M ⊗ₘ β.hom.app N) ≫ Functor.LaxMonoidal.μ R' (F.obj M) (F.obj N) =
        E.map (Functor.LaxMonoidal.μ R M N) ≫ β.hom.app (M ⊗ N) ≫ R'.map (g M N).hom)
    (hd : ∀ M N, IsIso (a.leftAdjointOplaxMonoidal.δ M N)) (M N : A') :
    IsIso (b.leftAdjointOplaxMonoidal.δ M N) := by
  let := b.leftAdjointOplaxMonoidal
  exact pullTensor_isIso_of_square E F L L' γ e g
    (fun M N ↦ a.leftAdjointOplaxMonoidal.δ M N) hd
    (pullTensor_mate_transport E F L R a L' R' b β γ e g
      (fun M N ↦ a.leftAdjointOplaxMonoidal.δ M N)
      (fun {M M' N N'} s t ↦ hn M M' N N' s t) hunit hpair
      (pullTensor_mate_formula L R a)) M N

end PullTensorTransport

private theorem pullTensor_sectionTensor_natural (X : Scheme.{u})
    {M M' N N' : modules Λ X} (g : M ⟶ M') (h : N ⟶ N') (U : X.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    ((g ⊗ₘ h).val.app U) (sectionPureTensor Λ X M N U x y) =
      sectionPureTensor Λ X M' N' U ((g.val.app U) x) ((h.val.app U) y) :=
  InternalAbelianSheafModule.comparison_sectionTmul_natural
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) g h U x y

private theorem pullTensor_pushComparison_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ X) (U : Y.ProEtᵒᵖ) (x : M.X.obj.obj
      ((InternalModuleOperations.siteMap f).op.obj U)) :
    (((pushComparison Λ f).hom.app M).val.app U) x = x :=
  (InternalModuleOperations.lowerComparison_existsUnique Λ f).exists.choose_spec M U x

private theorem pullTensor_internalPush_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U)
    (y : ((CondensedRing.lowerStar Λ f).obj N).X.obj.obj U) :
    (((internalPushLax Λ f).μ M N).hom.hom.app U)
        (internalPureTensor Λ Y _ _ U x y) =
      internalPureTensor Λ X M N ((InternalModuleOperations.siteMap f).op.obj U) x y :=
  (internalPushNormalized_existsUnique Λ f).exists.choose_spec M N U x y

section GeneratorFormula

universe w v v'

-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify

private theorem pullTensor_sectionTmul_eq {C : Type v} [Category.{v'} C]
    (J : GrothendieckTopology C) [UnivLE.{max v v', w}]
    [HasSheafify J AddCommGrpCat.{w}] [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
    (R : Sheaf J AddCommGrpCat.{w}) [MonObj R] [IsCommMonObj R]
    (M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (InternalAbelianSheafModule.sectionRingSheaf J R))) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    InternalAbelianSheafModule.comparison_sectionTmul J R M N U x y =
      CochainPullback.moduleTmul
        (R := InternalAbelianSheafModule.sectionRingSheaf J R) M N U x y := by
  exact Eq.refl (CochainPullback.moduleTmul
    (R := InternalAbelianSheafModule.sectionRingSheaf J R) M N U x y)

end GeneratorFormula

private theorem pullTensor_push_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((pushforward Λ f).obj M).val.obj U)
    (y : ((pushforward Λ f).obj N).val.obj U) :
    (((pushLax Λ f).μ M N).val.app U) (sectionPureTensor Λ Y _ _ U x y) =
      sectionPureTensor Λ X M N ((InternalModuleOperations.siteMap f).op.obj U) x y := by
  have h := (pushNormalized_existsUnique Λ f).exists.choose_spec M N U x y
  exact (congrArg (fun z ↦ (((pushLax Λ f).μ M N).val.app U) z)
      (pullTensor_sectionTmul_eq (Scheme.ProEt.topology Y) (condensedRingObj Λ Y)
        _ _ U x y)).trans
    (h.trans (pullTensor_sectionTmul_eq (Scheme.ProEt.topology X) (condensedRingObj Λ X)
      M N ((InternalModuleOperations.siteMap f).op.obj U) x y).symm)

attribute [local irreducible] internalPushLax pushLax
  InternalAbelianSheafModule.comparison_internalTmul
  InternalAbelianSheafModule.comparison_sectionTmul
  InternalModuleOperations.lowerComparison InternalModuleOperations.upperComparison

private theorem pullTensor_hom_ext (X : Scheme.{u})
    (M N : internalModules Λ X) (H : modules Λ X)
    {g h : (equivalence Λ X).functor.obj (M ⊗ N) ⟶ H}
    (he : ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
      (g.val.app U) (internalPureTensor Λ X M N U x y) =
        (h.val.app U) (internalPureTensor Λ X M N U x y)) : g = h := by
  exact InternalAbelianSheafModule.comparison_internalTensor_hom_ext
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N he

set_option backward.isDefEq.respectTransparency true in
private theorem pullTensor_push_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ X) :
    (ordinaryTensorComparison Λ Y
        ((CondensedRing.lowerStar Λ f).obj M) ((CondensedRing.lowerStar Λ f).obj N)).hom ≫
      ((pushComparison Λ f).hom.app M ⊗ₘ (pushComparison Λ f).hom.app N) ≫
      (pushLax Λ f).μ ((equivalence Λ X).functor.obj M)
        ((equivalence Λ X).functor.obj N) =
    (equivalence Λ Y).functor.map ((internalPushLax Λ f).μ M N) ≫
      (pushComparison Λ f).hom.app (M ⊗ N) ≫
      (pushforward Λ f).map (ordinaryTensorComparison Λ X M N).hom := by
  let : Category.{u} (MorphismProperty.Over @WeaklyEtale ⊤ Y) :=
    MorphismProperty.Comma.instCategory
    (𝟭 Scheme.{u}) (Functor.fromPUnit Y) @WeaklyEtale ⊤ ⊤
  let : Category.{u} (MorphismProperty.Over @WeaklyEtale ⊤ X) :=
    MorphismProperty.Comma.instCategory
    (𝟭 Scheme.{u}) (Functor.fromPUnit X) @WeaklyEtale ⊤ ⊤
  apply pullTensor_hom_ext Λ Y
  intro U x y
  change (((pushLax Λ f).μ _ _).val.app U)
      (((((pushComparison Λ f).hom.app M ⊗ₘ
        (pushComparison Λ f).hom.app N)).val.app U)
        (((ordinaryTensorComparison Λ Y _ _).hom.val.app U)
          (internalPureTensor Λ Y _ _ U x y))) =
    (((ordinaryTensorComparison Λ X M N).hom.val.app
      ((InternalModuleOperations.siteMap f).op.obj U)))
      ((((pushComparison Λ f).hom.app (M ⊗ N)).val.app U)
        ((((internalPushLax Λ f).μ M N).hom.hom.app U)
          (internalPureTensor Λ Y _ _ U x y)))
  let MY := (CondensedRing.lowerStar Λ f).obj M
  let NY := (CondensedRing.lowerStar Λ f).obj N
  let EX := (equivalence Λ X).functor
  let EY := (equivalence Λ Y).functor
  let W := (InternalModuleOperations.siteMap f).op.obj U
  let g := (pushComparison Λ f).hom.app M
  let h := (pushComparison Λ f).hom.app N
  let p := ((pushLax Λ f).μ (EX.obj M) (EX.obj N)).val.app U
  let q := (ordinaryTensorComparison Λ X M N).hom.val.app W
  have ht := pullTensor_tensorComparison_apply Λ Y MY NY U x y
  have hn := pullTensor_sectionTensor_natural Λ Y g h U x y
  have hg : (g.val.app U) x = x := by
    simpa only [g] using pullTensor_pushComparison_apply Λ f M U x
  have hh : (h.val.app U) y = y := by
    simpa only [h] using pullTensor_pushComparison_apply Λ f N U y
  rw [hg, hh] at hn
  have hl := (congrArg (fun z ↦ p (((g ⊗ₘ h).val.app U) z)) ht).trans
    ((congrArg p hn).trans (pullTensor_push_apply Λ f (EX.obj M) (EX.obj N) U x y))
  have hr := (congrArg q (pullTensor_pushComparison_apply Λ f (M ⊗ N) U
      ((((internalPushLax Λ f).μ M N).hom.hom.app U)
        (internalPureTensor Λ Y MY NY U x y)))).trans
    ((congrArg q (pullTensor_internalPush_apply Λ f M N U x y)).trans
      (pullTensor_tensorComparison_apply Λ X M N W x y))
  exact hl.trans hr.symm

attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence

end PullTensorProof

attribute [local irreducible] internalPullMonoidal pullMonoidal
  internalPushLax pushLax internalPullOplax pullOplax

private theorem map_jointly_epi {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] {A : C} {I : Type*}
    (S : I → C) (ι : ∀ i, S i ⟶ A)
    (hι : ∀ {Z : C} (f g : A ⟶ Z), (∀ i, ι i ≫ f = ι i ≫ g) → f = g)
    {B : D} {f g : F.obj A ⟶ B}
    (h : ∀ i, F.map (ι i) ≫ f = F.map (ι i) ≫ g) : f = g := by
  let e := F.objObjPreimageIso B
  apply (cancel_mono e.inv).mp
  let f' := F.preimage (f ≫ e.inv)
  let g' := F.preimage (g ≫ e.inv)
  have hfg : f' = g' := by
    apply hι
    intro i
    apply F.map_injective
    simpa only [Functor.map_comp, f', g', Functor.map_preimage, ← Category.assoc]
      using congrArg (fun k ↦ k ≫ e.inv) (h i)
  simpa only [f', g', Functor.map_preimage] using congrArg F.map hfg

private theorem total_normalization_unique
    {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
    [MonoidalCategory D] [MonoidalCategory D']
    [MonoidalPreadditive D] [MonoidalPreadditive D']
    (F : D ⥤ D') [F.Additive] [F.Full] [F.Faithful] [F.EssSurj]
    (e : ∀ M N : D, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (he : ∀ (M M' N N' : D) (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (e M' N').hom = (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (P Q : CochainComplex D ℤ)
    [hasMap : CochainComplex.HasMapBifunctor P Q (curriedTensor D)]
    [hasMap' : CochainComplex.HasMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D')]
    [presTotal : F.PreservesTotalComplex
      ((((curriedTensor D).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj Q)
      (.up ℤ)] :
    ∃! t : (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor D)) ≅
      CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D'),
      ∀ (p q n : ℤ) (h : p + q = n),
        F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor D) p q n h) ≫ t.hom.f n =
          (e (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D') p q n h := by
  let t := InternalAbelianSheafModule.comparison_totalIso F e he P Q
  have ht := InternalAbelianSheafModule.comparison_totalIso_ι F e he P Q
  refine ⟨t, ht, ?_⟩
  intro s hs
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro n
  apply map_jointly_epi F
    (fun i : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦ P.X i.val.1 ⊗ Q.X i.val.2)
    (fun i ↦ CochainComplex.ιMapBifunctor P Q (curriedTensor D)
      i.val.1 i.val.2 n i.property)
  · intro Z a b hab
    exact HomologicalComplex.mapBifunctor.hom_ext fun p q h ↦ hab ⟨(p, q), h⟩
  · rintro ⟨⟨p, q⟩, h⟩
    exact (hs p q n h).trans (ht p q n h).symm

private theorem total_preserves
    {D D' : Type*} [Category D] [Category D'] [Preadditive D] [Preadditive D']
    (F : D ⥤ D') [F.Additive] [PreservesColimitsOfSize.{0, 0} F]
    (K : HomologicalComplex₂ D (.up ℤ) (.up ℤ)) :
    F.PreservesTotalComplex K (.up ℤ) := by
  intro n
  infer_instance

attribute [local instance 4000] total_preserves

set_option backward.isDefEq.respectTransparency true in
-- The concrete total tensors carry large category and universe instances.
/-- Extension by zero is additive, since all its three specified factors are additive. -/
@[instance] theorem extension_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extension Λ j).Additive := by
  exact (openAdjunction Λ j).left_adjoint_additive

/-- Extension by zero preserves finite limits. -/
@[instance] theorem extension_preservesFiniteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (extension Λ j) := by
  exact ((InternalModuleOperations.internal_module_operations_transport Λ).2.2.2.2.1 j).1.mp
    (inferInstance : PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j))

/-- Extension by zero preserves finite colimits. -/
@[instance] theorem extension_preservesFiniteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (extension Λ j) := by
  let := (openAdjunction Λ j).isLeftAdjoint
  exact inferInstance

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
