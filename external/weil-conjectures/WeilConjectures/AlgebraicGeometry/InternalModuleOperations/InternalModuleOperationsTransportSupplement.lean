/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.CompatibleSquareComponents
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport

/-!
# Transport of internal module operations to sectionwise modules

The sectionwise pushforward uses the actual section-ring homomorphism induced by eta_f.
Pullback is its canonical left adjoint, hence the sheafified tensor-formula pullback.
Open extension is the canonical left adjoint of restriction. Unique characterizations fix
all comparisons; in particular no arbitrary natural isomorphism is used for base change.

## References

* Nagata density normalization, sheaves proof, Steps 1--2
* Stacks Project, Modules on Sites, Tags 03D6 and 03D7
* Categories, Tag 0B65
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u uA vA uB vB uC vC uD vD uE vE uAb vAb uBb vBb uCb vCb uDb vDb

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale
namespace InternalModuleOperations

private theorem comparison_existsUnique
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R') :
    ∃! c : L ⋙ H.functor ≅ E.functor ⋙ L',
      (mateEquiv a b (.mk _ _ _ _ c.inv)) = r.hom := by
  obtain ⟨c, hc, huniq, _⟩ := exists_equivalenceAdjunctionComparison E H a b r
  exact ⟨c, hc, fun d hd ↦ huniq d hd⟩

private theorem presheafPushforward_isRightAdjoint
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (RX : Dᵒᵖ ⥤ RingCat.{u + 1}) (RY : Cᵒᵖ ⥤ RingCat.{u + 1})
    (ψ : RY ⟶ G.op ⋙ RX) : (PresheafOfModules.pushforward.{u + 1} ψ).IsRightAdjoint := by
  let eX : PresheafOfModules.{u + 1} RX ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := D)) RX
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := D)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let eY : PresheafOfModules.{u + 1} RY ≌
      PresheafOfModules.{u + 1} ((AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY) :=
    { functor := PresheafOfModules.pushforward₀ (AsSmall.down.{u, u + 1, 0} (C := C)) RY
      inverse := PresheafOfModules.pushforward₀ (AsSmall.up.{u, u + 1, 0} (C := C)) _
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  let F := AsSmall.down.{u, u + 1, 0} (C := C) ⋙ G ⋙
    AsSmall.up.{u, u + 1, 0} (C := D)
  let φ : (AsSmall.down.{u, u + 1, 0} (C := C)).op ⋙ RY ⟶
      F.op ⋙ (AsSmall.down.{u, u + 1, 0} (C := D)).op ⋙ RX :=
    Functor.whiskerLeft (AsSmall.down.{u, u + 1, 0} (C := C)).op ψ
  have : (PresheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint := inferInstance
  have : eX.functor.IsRightAdjoint := eX.symm.toAdjunction.isRightAdjoint
  have : eY.inverse.IsRightAdjoint := eY.toAdjunction.isRightAdjoint
  have : (eX.functor ⋙ PresheafOfModules.pushforward φ ⋙ eY.inverse).IsRightAdjoint :=
    inferInstance
  exact this

private theorem sectionRingMap_existsUnique
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : C ⥤ D) [F.IsContinuous J K]
    (RX : Sheaf K Ab.{u + 1}) (RY : Sheaf J Ab.{u + 1})
    [MonObj RX] [IsCommMonObj RX] [MonObj RY] [IsCommMonObj RY]
    (ψ : RY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj RX) [IsMonHom ψ] :
    let BX := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (sectionRingSheaf.{u + 1, u + 1, u} K RX)
    let BY := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (sectionRingSheaf.{u + 1, u + 1, u} J RY)
    ∃! φ : BY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj BX,
      ∀ (V : Cᵒᵖ) (r : BY.obj.obj V), (φ.hom.app V).hom r = (ψ.hom.app V).hom r := by
  dsimp only
  let BX := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} K RX)
  let BY := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} J RY)
  let AX := Mon.mk RX
  let AY := Mon.mk RY
  let IY := sheafToPresheaf J Ab.{u + 1}
  let IX := sheafToPresheaf K Ab.{u + 1}
  let P := F.sheafPushforwardContinuous Ab.{u + 1}
    J K
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let e : IX ⋙ W ≅ P ⋙ IY :=
    Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F Ab.{u + 1} J K
  let h : IY.mapMon.obj AY ⟶
      (IX ⋙ W).mapMon.obj AX :=
    IY.mapMon.map
      ({ hom := ψ
         isMonHom_hom := inferInstance } :
        Mon.mk RY ⟶ P.mapMon.obj AX) ≫
      (Functor.mapMonCompIso (F := P) (G := IY)).inv.app _ ≫
        (Functor.mapMonNatIso e).inv.app _
  have he : e.inv.app RX = 𝟙 _ := by
    apply (cancel_epi (e.hom.app RX)).mp
    rw [e.hom_inv_id_app]
    simp only [e,
      Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
      Category.comp_id]
    rfl
  let τ : IY.obj RY ⟶
      (IX ⋙ W).obj RX := ψ.hom
  have hh : h.hom = τ := by
    change ψ.hom ≫
      e.inv.app RX = τ
    rw [he]
    rfl
  let φ : BY ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      J K).obj (BX) :=
    ⟨Functor.whiskerRight (Monoidal.MonFunctorCategoryEquivalence.functor.map h)
      monToRing⟩
  have hφ : ∀ (V : Cᵒᵖ) (r : (BY).obj.obj V),
      (φ.hom.app V).hom r = (ψ.hom.app V).hom r := by
    intro V r
    change ((h.hom.app V).hom r) = _
    rw [hh]
    rfl
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (hψ V r).trans (hφ V r).symm

private theorem section_action {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J Ab.{u + 1}] [HasSheafify K Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] [(K.W (A := Ab.{u + 1})).IsMonoidal]
    (F : C ⥤ D) [F.IsContinuous J K]
    (RX : Sheaf K Ab.{u + 1}) (RY : Sheaf J Ab.{u + 1})
    (N : Sheaf K Ab.{u + 1})
    (ψ : RY ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj RX)
    (a : RX ⊗ N ⟶ N) (V : Cᵒᵖ) (r : RY.obj.obj V)
    (m : N.obj.obj (F.op.obj V)) :
    ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1}) RY
      ((F.sheafPushforwardContinuous Ab.{u + 1} J K).obj N)).app V ≫
      (ψ ▷ _ ≫ Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous Ab.{u + 1} J K)
        RX N ≫ (F.sheafPushforwardContinuous Ab.{u + 1} J K).map a).hom.app V).hom
        (r ⊗ₜ[ℤ] m) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) RX N).app (F.op.obj V) ≫
      a.hom.app (F.op.obj V)).hom ((ψ.hom.app V).hom r ⊗ₜ[ℤ] m) := by
  let IY := sheafToPresheaf J Ab.{u + 1}
  let P := F.sheafPushforwardContinuous Ab.{u + 1} J K
  have hn := congr_app (Functor.LaxMonoidal.μ_natural_left IY ψ (P.obj N)) V
  simp only [NatTrans.comp_app] at hn
  have ht := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    F Ab.{u + 1} J K RX N V
  change ((Functor.LaxMonoidal.μ IY RY (P.obj N)).app V ≫
    (ψ ▷ P.obj N).hom.app V ≫ (Functor.LaxMonoidal.μ P RX N).hom.app V ≫
    (P.map a).hom.app V).hom (r ⊗ₜ[ℤ] m) = _
  erw [← reassoc_of% hn, reassoc_of% ht]
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf K Ab.{u + 1}) RX N).app
    (F.op.obj V) ≫ a.hom.app (F.op.obj V)).hom
      ((ψ.hom.app V ▷ N.obj.obj (F.op.obj V)).hom (r ⊗ₜ[ℤ] m)) = _
  rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul]

private theorem pushforward_comp_existsUnique
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E}
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
    (R : Sheaf L RingCat.{u}) (S : Sheaf K RingCat.{u}) (T : Sheaf J RingCat.{u})
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat K L).obj R)
    (χ : T ⟶ (H.sheafPushforwardContinuous RingCat J L).obj R)
    (κ : H ≅ F ⋙ G)
    (h : ∀ (U : Cᵒᵖ) (r : T.obj.obj U),
      (R.obj.map (κ.hom.app U.unop).op).hom
        ((ψ.hom.app (F.op.obj U)).hom ((φ.hom.app U).hom r)) =
          (χ.hom.app U).hom r) :
    ∃! c : SheafOfModules.pushforward.{vA} ψ ⋙ SheafOfModules.pushforward φ ≅
        SheafOfModules.pushforward χ,
      ∀ (M : SheafOfModules.{vA} R) (U : Cᵒᵖ)
        (x : ((SheafOfModules.pushforward φ).obj
          ((SheafOfModules.pushforward ψ).obj M)).val.obj U),
        ((c.hom.app M).val.app U).hom x = M.val.map (κ.hom.app U.unop).op x := by
  let : (F ⋙ G).IsContinuous J L := Functor.isContinuous_comp _ _ _ K _
  have hring :
      (φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ) ≫
        (Functor.sheafPushforwardContinuousNatTrans κ.hom RingCat J L).app R = χ := by
    ext U r
    exact h U r
  let c := SheafOfModules.pushforwardComp φ ψ ≪≫
    SheafOfModules.pushforwardCongr₂ _ κ hring
  have hc : ∀ (M : SheafOfModules.{vA} R) (U : Cᵒᵖ)
      (x : ((SheafOfModules.pushforward φ).obj
        ((SheafOfModules.pushforward ψ).obj M)).val.obj U),
      ((c.hom.app M).val.app U).hom x = M.val.map (κ.hom.app U.unop).op x := by
    intro M U x
    rfl
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply Iso.ext
  ext M U x
  exact (hd M U x).trans (hc M U x).symm

private theorem comparison_unit_counit
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ≌ C) (H : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (r : R ⋙ E.functor ≅ H.functor ⋙ R')
    (c : L ⋙ H.functor ≅ E.functor ⋙ L')
    (hc : (mateEquiv a b c.inv) = r.hom) :
    (∀ M, E.functor.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      R'.map (c.hom.app M) = b.unit.app (E.functor.obj M)) ∧
    (∀ N, L'.map (r.inv.app N) ≫ c.inv.app (R.obj N) ≫
      H.functor.map (a.counit.app N) = b.counit.app (H.functor.obj N)) := by
  have hi : ((mateEquiv a b).symm r.hom) = c.inv := by
    rw [← hc]
    exact ((mateEquiv a b).symm_apply_apply c.inv)
  constructor
  · intro M
    have h := unit_mateEquiv_symm a b r.hom M
    change _ = b.unit.app (E.functor.obj M) ≫
      R'.map (((mateEquiv a b).symm r.hom).app M) at h
    rw [hi] at h
    rw [← Category.assoc, h, Category.assoc, ← R'.map_comp]
    simp
  · intro N
    have h := mateEquiv_counit_symm a b r.hom N
    change _ = ((mateEquiv a b).symm r.hom).app (R.obj N) ≫
      H.functor.map (a.counit.app N) at h
    rw [hi] at h
    rw [← h, ← Category.assoc, ← L'.map_comp]
    simp

private theorem preserves_finite_limits_iff
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ≌ C) (H : B ≌ D) (F : A ⥤ B) (G : C ⥤ D)
    (c : F ⋙ H.functor ≅ E.functor ⋙ G) :
    PreservesFiniteLimits F ↔ PreservesFiniteLimits G := by
  constructor
  · intro h
    have : PreservesFiniteLimits (E.functor ⋙ G) := preservesFiniteLimits_of_natIso c
    have : PreservesFiniteLimits (E.inverse ⋙ E.functor ⋙ G) := inferInstance
    exact preservesFiniteLimits_of_natIso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E.counitIso G ≪≫ G.leftUnitor)
  · intro h
    have : PreservesFiniteLimits (F ⋙ H.functor) := preservesFiniteLimits_of_natIso c.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F H.functor

private theorem preserves_finite_colimits_iff
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ≌ C) (H : B ≌ D) (F : A ⥤ B) (G : C ⥤ D)
    (c : F ⋙ H.functor ≅ E.functor ⋙ G) :
    PreservesFiniteColimits F ↔ PreservesFiniteColimits G := by
  constructor
  · intro h
    have : PreservesFiniteColimits (E.functor ⋙ G) := preservesFiniteColimits_of_natIso c
    have : PreservesFiniteColimits (E.inverse ⋙ E.functor ⋙ G) := inferInstance
    exact preservesFiniteColimits_of_natIso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight E.counitIso G ≪≫ G.leftUnitor)
  · intro h
    have : PreservesFiniteColimits (F ⋙ H.functor) := preservesFiniteColimits_of_natIso c.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F H.functor

private theorem inverseMate_transport
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {Ab : Type uAb} [Category.{vAb} Ab] {Bb : Type uBb} [Category.{vBb} Bb]
    {Cb : Type uCb} [Category.{vCb} Cb] {Db : Type uDb} [Category.{vDb} Db]
    (EA : A ≌ Ab) (EB : B ≌ Bb) (EC : C ≌ Cb) (ED : D ≌ Db)
    {J : A ⥤ B} {U : B ⥤ A} {J' : C ⥤ D} {U' : D ⥤ C}
    {Jb : Ab ⥤ Bb} {Ub : Bb ⥤ Ab} {Jb' : Cb ⥤ Db} {Ub' : Db ⥤ Cb}
    (adj : J ⊣ U) (adj' : J' ⊣ U') (adjb : Jb ⊣ Ub) (adjb' : Jb' ⊣ Ub')
    (u : U ⋙ EA.functor ≅ EB.functor ⋙ Ub)
    (u' : U' ⋙ EC.functor ≅ ED.functor ⋙ Ub')
    (j : J ⋙ EB.functor ≅ EA.functor ⋙ Jb)
    (j' : J' ⋙ ED.functor ≅ EC.functor ⋙ Jb')
    (hj : (mateEquiv adj adjb j.inv) = u.hom)
    (hj' : (mateEquiv adj' adjb' j'.inv) = u'.hom)
    (P : A ⥤ C) (Q : B ⥤ D) (Pb : Ab ⥤ Cb) (Qb : Bb ⥤ Db)
    (p : P ⋙ EC.functor ≅ EA.functor ⋙ Pb)
    (q : Q ⋙ ED.functor ≅ EB.functor ⋙ Qb)
    (b : U ⋙ P ⟶ Q ⋙ U') (bb : Ub ⋙ Pb ⟶ Qb ⋙ Ub')
    (hb : ∀ Y : B,
      p.hom.app (U.obj Y) ≫ Pb.map (u.hom.app Y) ≫ bb.app (EB.functor.obj Y) =
        EC.functor.map (b.app Y) ≫ u'.hom.app (Q.obj Y) ≫ Ub'.map (q.hom.app Y)) :
    Functor.whiskerRight (((mateEquiv adj adj').symm b)) ED.functor ≫
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ q ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight j _ ≪≫
            Functor.associator _ _ _).hom =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ j' ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p _ ≪≫
          Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft EA.functor (((mateEquiv adjb adjb').symm bb)) ∧
      (IsIso (((mateEquiv adjb adjb').symm bb)) →
        IsIso (((mateEquiv adj adj').symm b))) := by
  obtain ⟨hm, hi⟩ := equivalenceAdjunctionComparison_inverseMate
    EA EB EC ED adj adj' adjb adjb' u u' j j' hj hj' P Q Pb Qb p q b bb hb
  refine ⟨?_, hi.mpr⟩
  apply NatTrans.ext
  funext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc] using hm M

private theorem coefficient_comp_apply
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (RZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (a : RY ⟶ (ProEtale.lowerStar Ab.{u + 1} f).obj RX)
    (b : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} g).obj RY)
    (c : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} (f ≫ g)).obj RX)
    (h : c = b ≫ (ProEtale.lowerStar Ab.{u + 1} g).map a ≫
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app RX)
    (V : Z.ProEtᵒᵖ) (r : RZ.obj.obj V) :
    (RX.obj.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app V.unop).op).hom
        ((a.hom.app (Opposite.op
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop))).hom
          ((b.hom.app V).hom r)) = (c.hom.app V).hom r := by
  have he := congrArg (fun z ↦ (z.hom.app V).hom r) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
    ProEtale.lowerStar_map_hom_app', ProEtale.lowerStarComp_hom_app_hom_app] at he
  exact he.symm

private theorem scheme_pushforward_comp_existsUnique
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (BX : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (BY : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1})
    (BZ : Sheaf (Scheme.ProEt.topology Z) RingCat.{u + 1})
    (φ : BY ⟶ (ProEtale.lowerStar RingCat.{u + 1} f).obj BX)
    (ψ : BZ ⟶ (ProEtale.lowerStar RingCat.{u + 1} g).obj BY)
    (χ : BZ ⟶ (ProEtale.lowerStar RingCat.{u + 1} (f ≫ g)).obj BX)
    (h : ∀ (V : Z.ProEtᵒᵖ) (r : BZ.obj.obj V),
      (BX.obj.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g).hom.app V.unop).op).hom
          ((φ.hom.app (Opposite.op
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop))).hom
              ((ψ.hom.app V).hom r)) = (χ.hom.app V).hom r) :
    ∃! c : SheafOfModules.pushforward.{u + 1}
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) φ ⋙
      SheafOfModules.pushforward
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) ψ ≅
        SheafOfModules.pushforward (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (f ≫ g)) χ,
      ∀ (M : SheafOfModules.{u + 1} BX) (V : Z.ProEtᵒᵖ)
        (m : ((SheafOfModules.pushforward
          (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) ψ).obj
            ((SheafOfModules.pushforward
              (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) φ).obj M)).val.obj V),
        ((c.hom.app M).val.app V).hom m =
          (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
            ((SheafOfModules.toSheaf BX).obj M)).hom.app V).hom m := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let H := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (f ≫ g)
  let κ := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g
  obtain ⟨c, hc, huniq⟩ := pushforward_comp_existsUnique
    F G H BX BY BZ ψ φ χ κ h
  have hc' (M : SheafOfModules.{u + 1} BX) (V : Z.ProEtᵒᵖ)
      (m : ((SheafOfModules.pushforward
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) ψ).obj
          ((SheafOfModules.pushforward
            (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) φ).obj M)).val.obj V) :
      ((c.hom.app M).val.app V).hom m =
        (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
          ((SheafOfModules.toSheaf BX).obj M)).hom.app V).hom m := by
    rw [ProEtale.lowerStarComp_hom_app_hom_app]
    exact hc M V m
  refine ⟨c, hc', ?_⟩
  intro d hd
  apply huniq d
  intro M V m
  have he := hd M V m
  rw [ProEtale.lowerStarComp_hom_app_hom_app] at he
  exact he

private theorem reconstructed_pushforward_comp_existsUnique
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (RX : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (RY : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (RZ : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    [MonObj RX] [IsCommMonObj RX] [MonObj RY] [IsCommMonObj RY]
    [MonObj RZ] [IsCommMonObj RZ]
    (a : RY ⟶ (ProEtale.lowerStar Ab.{u + 1} f).obj RX)
    (b : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} g).obj RY)
    (c : RZ ⟶ (ProEtale.lowerStar Ab.{u + 1} (f ≫ g)).obj RX)
    (h : c = b ≫ (ProEtale.lowerStar Ab.{u + 1} g).map a ≫
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app RX)
    (φ : ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) RY)) ⟶
      (ProEtale.lowerStar RingCat.{u + 1} f).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) RX)))
    (ψ : ((sheafCompose (Scheme.ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Z) RZ)) ⟶
      (ProEtale.lowerStar RingCat.{u + 1} g).obj
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y) RY)))
    (χ : ((sheafCompose (Scheme.ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Z) RZ)) ⟶
      (ProEtale.lowerStar RingCat.{u + 1} (f ≫ g)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) RX)))
    (hφ : ∀ V r, (φ.hom.app V).hom r = (a.hom.app V).hom r)
    (hψ : ∀ V r, (ψ.hom.app V).hom r = (b.hom.app V).hom r)
    (hχ : ∀ V r, (χ.hom.app V).hom r = (c.hom.app V).hom r) :
    ∃! e : SheafOfModules.pushforward.{u + 1}
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) φ ⋙
      SheafOfModules.pushforward
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) ψ ≅
      SheafOfModules.pushforward
        (F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (f ≫ g)) χ,
      ∀ M V m, ((e.hom.app M).val.app V).hom m =
        (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
          ((SheafOfModules.toSheaf _).obj M)).hom.app V).hom m := by
  apply scheme_pushforward_comp_existsUnique
  intro V r
  rw [hφ, hψ, hχ]
  exact coefficient_comp_apply f g RX RY RZ a b c h V r

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem coefficientMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V) :
    ((coefficientMap Λ f).hom.app V).hom r =
      ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  unfold coefficientMap
  exact (coefficientMap_existsUnique Λ f).exists.choose_spec V r













private theorem lowerComparison_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Y.ProEtᵒᵖ)
    (m : ((lowerStar Λ f).obj ((equivalence Λ X).functor.obj M)).val.obj V) :
    (((lowerComparison Λ f).hom.app M).val.app V).hom m = m := by
  unfold lowerComparison
  exact (lowerComparison_existsUnique Λ f).exists.choose_spec M V m

private theorem lowerComp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u + 1} (ring Λ X)) (V : Z.ProEtᵒᵖ)
    (m : ((lowerStar Λ g).obj ((lowerStar Λ f).obj M)).val.obj V) :
    (((lowerComp Λ f g).hom.app M).val.app V).hom m =
      (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
        ((SheafOfModules.toSheaf (ring Λ X)).obj M)).hom.app V).hom m := by
  unfold lowerComp
  exact (lowerComp_existsUnique Λ f g).exists.choose_spec M V m

private theorem lowerComp_compatible {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (lowerComparison Λ g).hom.app ((CondensedRing.lowerStar Λ f).obj M) ≫
        (lowerStar Λ g).map ((lowerComparison Λ f).hom.app M) ≫
        (lowerComp Λ f g).hom.app ((equivalence Λ X).functor.obj M) =
      (equivalence Λ Z).functor.map ((CondensedRing.lowerStarComp Λ f g).hom.app M) ≫
        (lowerComparison Λ (f ≫ g)).hom.app M := by
  ext V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply,
    lowerComparison_apply]
  change (((lowerComp Λ f g).hom.app ((equivalence Λ X).functor.obj M)).val.app V).hom
      ((((lowerComparison Λ f).hom.app M).val.app ((siteMap g).op.obj V)).hom m) = _
  rw [lowerComparison_apply, lowerComp_apply]
  erw [lowerComparison_apply]
  change _ = (((CondensedRing.lowerStarComp Λ f g).hom.app M).hom.hom.app V).hom m
  rw [CondensedRing.lowerStarComp_hom_app_hom]
  rfl


private theorem equivalence_additive (T : Scheme.{u}) :
    (equivalence Λ T).functor.Additive :=
  { map_add := by intros; ext V x; rfl }

private theorem upperComparison_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
      (.mk _ _ _ _ (upperComparison Λ f).inv)) =
      (lowerComparison Λ f).hom := by
  unfold upperComparison
  exact (upperComparison_existsUnique Λ f).exists.choose_spec





attribute [local irreducible] squareData

private theorem square_compatible {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperComparison Λ g').hom.app ((CondensedRing.upperStar Λ j).obj M) ≫
        (upperStar Λ g').map ((upperComparison Λ j).hom.app M) ≫
        (sectionSquare Λ sq).hom.app ((equivalence Λ T).functor.obj M) =
      (equivalence Λ U').functor.map ((internalSquare Λ sq).hom.app M) ≫
        (upperComparison Λ j').hom.app ((CondensedRing.upperStar Λ g).obj M) ≫
        (upperStar Λ j').map ((upperComparison Λ g).hom.app M) := by
  exact (squareData Λ sq).compatible M

attribute [local irreducible] internalSquare sectionSquare





private theorem openComparison_mate {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openAdjunction Λ j) (.mk _ _ _ _ (openComparison Λ j).inv)) =
      (upperComparison Λ j).hom := by
  unfold openComparison
  exact (openComparison_existsUnique Λ j).exists.choose_spec


end InternalModuleOperations
end AlgebraicGeometry.ProEtale
