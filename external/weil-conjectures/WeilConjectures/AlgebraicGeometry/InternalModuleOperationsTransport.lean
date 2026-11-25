/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

public import WeilConjectures.CategoryTheory.CompatibleSquareComponents
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
/-!
# Transport of internal module operations to sectionwise modules

Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Categories, Tag 0B65.
(auxiliary; not a blueprint node).

The sectionwise pushforward uses the actual section-ring homomorphism induced by eta_f.
Pullback is its canonical left adjoint, hence the sheafified tensor-formula pullback.
Open extension is the canonical left adjoint of restriction. Unique characterizations fix
all comparisons; in particular no arbitrary natural isomorphism is used for base change.
-/

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

private instance pullback_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).IsContinuous
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overPullback f

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reconstructed section-ring sheaf B_T, using the recorded reconstruction.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
noncomputable abbrev ring (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T))

/-- The fixed internal/sectionwise equivalence E_T, not a new equivalence.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
noncomputable abbrev equivalence (T : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ≌
      SheafOfModules.{u + 1} (ring Λ T) :=
  sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (condensedRingObj Λ T)

/-- The base-change functor on the small pro-etale sites.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable abbrev siteMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  MorphismProperty.Over.pullback @WeaklyEtale ⊤ f

/-- Continuity of the existing base-change functor, exposed at this abbreviation.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
instance siteMap_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (siteMap f).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overPullback f

/-- The adjunct of alpha_f induces the unique section-ring homomorphism with its given
underlying additive map.
Source: Stacks 03D6 (auxiliary; not a blueprint node).
Proof: Step 2. Reconstruct multiplication and unit by evaluating the tensor action on pure
section tensors. Monoidality of eta_f gives preservation of multiplication and unit;
its naturality gives restriction compatibility. Faithfulness of the forgetful ring functor
makes this lift unique. The underlying pushforward is evaluation at V times_Y X. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! φ : ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V),
        (φ.hom.app V).hom r = ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  let := siteMap_continuous f
  exact sectionRingMap_existsUnique.{u} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (siteMap f) (condensedRingObj Λ X) (condensedRingObj Λ Y)
    (condensedPushforwardHom Λ f)

/-- The canonical section-ring map B_Y -> f_* B_X, fixed by eta_f on every section.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ring Λ Y ⟶ ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring Λ X) :=
  (coefficientMap_existsUnique Λ f).exists.choose

private theorem coefficientMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V) :
    ((coefficientMap Λ f).hom.app V).hom r =
      ((condensedPushforwardHom Λ f).hom.app V).hom r := by
  unfold coefficientMap
  exact (coefficientMap_existsUnique Λ f).exists.choose_spec V r

/-- Ordinary direct image with scalar restriction along the adjunct of alpha_f.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable abbrev lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := siteMap f) (coefficientMap Λ f)

/-- The canonical direct-image comparison is uniquely the identity on underlying sheaves.
Source: Stacks 03D6 (auxiliary; not a blueprint node).
Proof: Steps 1--2. E preserves underlying sections and maps. The internal lax action is
eta_f(r) times n, precisely scalar restriction in the sectionwise direct image. Thus the
identity sheaf map and its inverse are linear and natural. Their underlying maps determine
them uniquely by faithfulness. -/
theorem lowerComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! r : CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
        (equivalence Λ X).functor ⋙ lowerStar Λ f,
      ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (V : Y.ProEtᵒᵖ) (m : ((lowerStar Λ f).obj ((equivalence Λ X).functor.obj M)).val.obj V),
        ((r.hom.app M).val.app V).hom m = m := by
  classical
  let L := CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor
  let R := (equivalence Λ X).functor ⋙ lowerStar Λ f
  have h (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V)
      (m : (R.obj M).val.obj V) :
      ((ModuleCat.smul ((L.obj M).val.obj V) r).asHom.hom) m =
        ((ModuleCat.smul ((R.obj M).val.obj V) r).asHom.hom) m := by
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)
      (((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj M.X)).app V ≫
      (condensedPushforwardHom Λ f ▷ _ ≫ Functor.LaxMonoidal.μ
        ((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))
        (condensedRingObj Λ X) M.X ≫
          ((siteMap f).sheafPushforwardContinuous Ab.{u + 1}
            (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
              (Mod.act M.X)).hom.app V).hom (r ⊗ₜ[ℤ] m) = _
    rw [section_action]
    change ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) M.X).app ((siteMap f).op.obj V) ≫
      (Mod.act M.X).hom.app ((siteMap f).op.obj V)).hom
        (((condensedPushforwardHom Λ f).hom.app V).hom r ⊗ₜ[ℤ] m) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) M.X).app ((siteMap f).op.obj V) ≫
        (Mod.act M.X).hom.app ((siteMap f).op.obj V)).hom
          (((coefficientMap Λ f).hom.app V).hom r ⊗ₜ[ℤ] m)
    have hc : ((coefficientMap Λ f).hom.app V).hom r =
        ((condensedPushforwardHom Λ f).hom.app V).hom r :=
      coefficientMap_apply Λ f V r
    rw [hc]
  let q (M) : L.obj M ⟶ R.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (R.obj M).val)
      (𝟙 _) (fun V r m ↦ h M V r m)⟩
  let p (M) : R.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (R.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun V r m ↦ (h M V r m).symm)⟩
  let c : L ≅ R := NatIso.ofComponents
    (fun M ↦ { hom := q M, inv := p M,
               hom_inv_id := by ext V m; rfl,
               inv_hom_id := by ext V m; rfl })
    (fun α ↦ by ext V m; rfl)
  refine ⟨c, ?_, ?_⟩
  · intro M V m
    rfl
  · intro d hd
    apply Iso.ext
    ext M V m
    exact hd M V m

/-- The identity-on-sections direct-image comparison.
Source: Stacks 03D6 (auxiliary; not a blueprint node). -/
noncomputable def lowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.lowerStar Λ f ⋙ (equivalence Λ Y).functor ≅
      (equivalence Λ X).functor ⋙ lowerStar Λ f :=
  (lowerComparison_existsUnique Λ f).exists.choose

end InternalModuleOperations
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.InternalModuleOperations

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct

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

end

end AlgebraicGeometry.ProEtale.InternalModuleOperations

namespace AlgebraicGeometry.ProEtale.InternalModuleOperations

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj TensorProduct
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

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

/-- Presheaf pullback exists in the coefficient universe even though the small pro-etale
site has object universe u+1 and morphism universe u.
Source: the tensor-formula construction in Stacks 03D7
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: transport both sites and their presheaves to coefficient-sized small models.
On these models the presheaf pullback is the left Kan extension and sectionwise scalar
extension; its Hom bijection sends m to 1 tensor m. Transport that adjunction back.
No equality between the original site object and morphism universes is imposed. -/
@[instance]
theorem presheafLowerStar_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u + 1}
      (F := siteMap f) (coefficientMap Λ f).hom).IsRightAdjoint := by
  exact presheafPushforward_isRightAdjoint (siteMap f) (ring Λ X).obj (ring Λ Y).obj
    (coefficientMap Λ f).hom

/-- The canonical sectionwise ringed-topos pullback, constructed by presheaf pullback
and sheafification: inverse image followed by B_X tensor_{f^{-1}B_Y} (-).
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev upperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u + 1} (ring Λ Y) ⥤ SheafOfModules.{u + 1} (ring Λ X) :=
  SheafOfModules.forget (ring Λ Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := siteMap f) (coefficientMap Λ f).hom ⋙
      PresheafOfModules.sheafification (R₀ := (ring Λ X).obj) (𝟙 (ring Λ X).obj)

/-- The tensor-formula sectionwise adjunction, with its sheafification Hom bijection.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar Λ f ⊣ lowerStar Λ f :=
  SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := siteMap f) (coefficientMap Λ f)

/-- The mate of the direct-image comparison is invertible and uniquely fixes pullback.
Source: Stacks 03D7, Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Steps 3--4. Conjugate the specified internal adjunction by E. The two left
adjoints of the identified direct image are uniquely isomorphic by the unit equation
situation-conventions. Undo the conjugation. The mate equation below
is exactly the Hom-transposition identity; evaluating it on identities gives both unit
and counit equations, by lem-weil-pbc-adjunction-of-natural-bijection. -/
theorem upperComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
        (equivalence Λ Y).functor ⋙ upperStar Λ f,
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
        (.mk _ _ _ _ c.inv)) =
        (lowerComparison Λ f).hom := by
  exact comparison_existsUnique (equivalence Λ Y) (equivalence Λ X)
    (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
    (lowerComparison Λ f)

/-- The pullback comparison normalized by the actual specified adjunctions.
Source: Stacks 03D7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar Λ f ⋙ (equivalence Λ X).functor ≅
      (equivalence Λ Y).functor ⋙ upperStar Λ f :=
  (upperComparison_existsUnique Λ f).exists.choose

/-- For an open immersion, sectionwise restriction admits extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Conjugate the given internal open-extension adjunction by the fixed
E equivalences, and identify its right adjoint using upperComparison. This supplies
the sectionwise left adjoint, characterized uniquely by its extension-by-zero universal
property. The same underlying abelian extension by zero carries the transported action. -/
@[instance]
theorem upperStar_isRightAdjoint {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : (upperStar Λ j).IsRightAdjoint := by
  have : (CondensedRing.upperStar Λ j).IsRightAdjoint :=
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).isRightAdjoint
  have : (CondensedRing.upperStar Λ j ⋙ (equivalence Λ U).functor).IsRightAdjoint :=
    inferInstance
  have : ((equivalence Λ T).functor ⋙ upperStar Λ j).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (upperComparison Λ j)
  exact (Functor.isRightAdjoint_comp_iff_right
    (equivalence Λ T).functor (upperStar Λ j)).mp inferInstance

/-- Sectionwise extension by zero, the canonical left adjoint of restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev extension {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (upperStar Λ j).leftAdjoint

/-- The sectionwise open-extension adjunction to restriction.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable abbrev openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  Adjunction.ofIsRightAdjoint (upperStar Λ j)

/-- The canonical open-extension comparison, normalized by the specified adjunctions.
Source: blueprint module-lower-shriek, Extension by zero clause; Categories 0B65
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 5. Apply unit-normalized uniqueness of left adjoints again to the internal
open adjunction and the sectionwise one, with upperComparison identifying the right
adjoints. The mate equation identifies the Hom bijections, units and counits. -/
theorem openComparison_existsUnique {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    ∃! o : CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
        (equivalence Λ U).functor ⋙ extension Λ j,
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ o.inv)) = (upperComparison Λ j).hom := by
  exact comparison_existsUnique (equivalence Λ U) (equivalence Λ T)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) (openAdjunction Λ j)
    (upperComparison Λ j)

/-- The uniquely adjunction-normalized comparison for extension by zero.
Source: blueprint module-lower-shriek, Extension by zero clause
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def openComparison {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ T).functor ≅
      (equivalence Λ U).functor ⋙ extension Λ j :=
  (openComparison_existsUnique Λ j).exists.choose

/-- The sectionwise direct-image composition comparison is the ordinary sheaf comparison.
Source: blueprint module-upper-star-comp; Stacks 03D6
(blueprint: lem-sfb-internal-module-operations-transport).
Proof: Step 6. Evaluation rebrackets the iterated fibre product. The two scalar actions
agree by compatibility of eta_f with composition, so the underlying abelian comparison
is linear, natural and invertible. Faithfulness gives uniqueness. -/
theorem lowerComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! c : lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g),
      ∀ (M : SheafOfModules.{u + 1} (ring Λ X)) (V : Z.ProEtᵒᵖ)
        (m : ((lowerStar Λ g).obj ((lowerStar Λ f).obj M)).val.obj V),
        ((c.hom.app M).val.app V).hom m =
          (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
            ((SheafOfModules.toSheaf (ring Λ X)).obj M)).hom.app V).hom m := by
  exact reconstructed_pushforward_comp_existsUnique f g
    (condensedRingObj Λ X) (condensedRingObj Λ Y) (condensedRingObj Λ Z)
    (condensedPushforwardHom Λ f) (condensedPushforwardHom Λ g)
    (condensedPushforwardHom Λ (f ≫ g)) (condensedPushforwardHom_comp Λ f g)
    (coefficientMap Λ f) (coefficientMap Λ g) (coefficientMap Λ (f ≫ g))
    (coefficientMap_apply Λ f) (coefficientMap_apply Λ g)
    (coefficientMap_apply Λ (f ≫ g))

/-- The canonical sectionwise direct-image composition comparison.
Source: Stacks 03D6 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def lowerComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lowerStar Λ f ⋙ lowerStar Λ g ≅ lowerStar Λ (f ≫ g) :=
  (lowerComp_existsUnique Λ f g).exists.choose

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

/-- The sectionwise pullback-composition comparison, conjugate to direct-image composition.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def upperComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    upperStar Λ (f ≫ g) ≅ upperStar Λ g ⋙ upperStar Λ f :=
  (Adjunction.leftAdjointCompIso (adjunction Λ g) (adjunction Λ f)
    (adjunction Λ (f ≫ g)) (lowerComp Λ f g)).symm

private theorem equivalence_additive (T : Scheme.{u}) :
    (equivalence Λ T).functor.Additive :=
  { map_add := by intros; ext V x; rfl }

private theorem upperComparison_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
      (.mk _ _ _ _ (upperComparison Λ f).inv)) =
      (lowerComparison Λ f).hom := by
  unfold upperComparison
  exact (upperComparison_existsUnique Λ f).exists.choose_spec

/-- The fixed pullback compositors commute with the normalized equivalence comparison.
Source: node Step 6 and normalized adjunction-comparison clause (2).
Proof: the direct-image compatibility holds on sections. Apply compositor compatibility
of mates; the conjugates of both chosen pullback compositors are the direct-image
compositors by their definitions.
(blueprint: lem-sfb-internal-module-operations-transport) -/
theorem upperComp_compatible {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (equivalence Λ X).functor.map ((CondensedRing.upperStarComp Λ f g).inv.app M) ≫
        (upperComparison Λ (f ≫ g)).hom.app M =
      (upperComparison Λ f).hom.app ((CondensedRing.upperStar Λ g).obj M) ≫
        (upperStar Λ f).map ((upperComparison Λ g).hom.app M) ≫
        (upperComp Λ f g).inv.app ((equivalence Λ Z).functor.obj M) := by
  refine equivalenceAdjunctionComparison_compositor
    (equivalence Λ Z) (equivalence Λ Y) (equivalence Λ X)
    (L01 := CondensedRing.upperStar Λ g) (R10 := CondensedRing.lowerStar Λ g)
    (L12 := CondensedRing.upperStar Λ f) (R21 := CondensedRing.lowerStar Λ f)
    (L02 := CondensedRing.upperStar Λ (f ≫ g))
    (R20 := CondensedRing.lowerStar Λ (f ≫ g))
    (Lb01 := upperStar Λ g) (Rb10 := lowerStar Λ g)
    (Lb12 := upperStar Λ f) (Rb21 := lowerStar Λ f)
    (Lb02 := upperStar Λ (f ≫ g)) (Rb20 := lowerStar Λ (f ≫ g))
    (CondensedRing.upperStarLowerStarAdjunction Λ g)
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
    (adjunction Λ g) (adjunction Λ f) (adjunction Λ (f ≫ g))
    (lowerComparison Λ g) (lowerComparison Λ f) (lowerComparison Λ (f ≫ g))
    (upperComparison Λ g) (upperComparison Λ f) (upperComparison Λ (f ≫ g))
    (upperComparison_mate Λ g) (upperComparison_mate Λ f)
    (upperComparison_mate Λ (f ≫ g))
    (CondensedRing.lowerStarComp Λ f g) (lowerComp Λ f g)
    (lowerComp_compatible Λ f g)
    (CondensedRing.upperStarComp Λ f g).symm (upperComp Λ f g).symm ?_ ?_ M
  · change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  · unfold upperComp
    change conjugateEquiv _ _ ((conjugateEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _

/-- The actual square isomorphisms paired with their transport equation.
Source: the node proof Step 6. Both data fields are the original compositor, equality
isomorphism, and compositor composite. The proof field records their compatibility.
(blueprint: lem-sfb-internal-module-operations-transport) -/
noncomputable def squareData {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :=
  compatibleSquareComponents (equivalence Λ T).functor (equivalence Λ U').functor
    (CondensedRing.upperStar Λ) (upperStar Λ) (upperComparison Λ) sq.w
    (CondensedRing.upperStarComp Λ g' j).symm (upperComp Λ g' j).symm
    (CondensedRing.upperStarComp Λ j' g) (upperComp Λ j' g)
    (fun M ↦ (upperStar Λ g').obj ((equivalence Λ U).functor.obj
      ((CondensedRing.upperStar Λ j).obj M)))
    (fun M ↦ (upperStar Λ j').obj ((equivalence Λ T').functor.obj
      ((CondensedRing.upperStar Λ g).obj M)))
    (fun M ↦ (upperComparison Λ g').hom.app ((CondensedRing.upperStar Λ j).obj M))
    (fun M ↦ (upperStar Λ g').map ((upperComparison Λ j).hom.app M))
    (fun M ↦ (upperComparison Λ j').hom.app ((CondensedRing.upperStar Λ g).obj M))
    (fun M ↦ (upperStar Λ j').map ((upperComparison Λ g).hom.app M))
    (by intro M; exact upperComp_compatible Λ g' j M)
    (by intro M; exact upperComp_compatible Λ j' g M)

/-- The actual internal pullback-composition comparison around a scheme square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ j ⋙ CondensedRing.upperStar Λ g' ≅
      CondensedRing.upperStar Λ g ⋙ CondensedRing.upperStar Λ j' :=
  (squareData Λ sq).internal

/-- The sectionwise pullback-composition comparison around the same square.
Source: blueprint module-upper-star-comp
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionSquare {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ j ⋙ upperStar Λ g' ≅ upperStar Λ g ⋙ upperStar Λ j' :=
  (squareData Λ sq).sectionwise

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

/-- The internal open-extension base-change map, with the specified unit and counit.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def internalBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j' ⟶
      CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g :=
  ((mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j')).symm
      (.mk _ _ _ _ (internalSquare Λ sq).hom))

/-- The sectionwise map is the same adjunction mate of pullback composition.
Source: Stacks 07A7 and the node proof Step 7
(blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def sectionBaseChange {U' U T' T : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ T'} {j : U ⟶ T} {g : T' ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : ChosenCartesianSquare g' j' j g) :
    upperStar Λ g' ⋙ extension Λ j' ⟶ extension Λ j ⋙ upperStar Λ g :=
  ((mateEquiv (openAdjunction Λ j) (openAdjunction Λ j')).symm
    (.mk _ _ _ _ (sectionSquare Λ sq).hom))

/-- Comparison of the source of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeSourceComparison {U' U T' : Scheme.{u}}
    (g' : U' ⟶ U) (j' : U' ⟶ T') [IsOpenImmersion j'] :
    (CondensedRing.upperStar Λ g' ⋙ CondensedRing.openImmersionLowerShriek Λ j') ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (upperStar Λ g' ⋙ extension Λ j') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (openComparison Λ j') ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (upperComparison Λ g') _ ≪≫
      Functor.associator _ _ _

/-- Comparison of the target of the open-extension base-change transformation.
Source: node proof Step 7 (blueprint: lem-sfb-internal-module-operations-transport). -/
noncomputable def baseChangeTargetComparison {U T T' : Scheme.{u}}
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g) ⋙
        (equivalence Λ T').functor ≅
      (equivalence Λ U).functor ⋙ (extension Λ j ⋙ upperStar Λ g) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (upperComparison Λ g) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (openComparison Λ j) _ ≪≫
      Functor.associator _ _ _

private theorem openComparison_mate {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openAdjunction Λ j) (.mk _ _ _ _ (openComparison Λ j).inv)) =
      (upperComparison Λ j).hom := by
  unfold openComparison
  exact (openComparison_existsUnique Λ j).exists.choose_spec

/-- Internal module operations agree canonically with sectionwise operations, including
specified adjunctions, open-extension mates and exactness.
Source: blueprint main-20261015, Nagata density normalization sheaves proof, Steps 1--2;
Stacks 03D6, 03D7, 0B65 and 07A7
(blueprint: lem-sfb-internal-module-operations-transport).

Proof (the eight steps of the DAG node):
1. E_T preserves underlying section groups and maps. Its action formula is
   a(r tensor m), so it and its inverse preserve addition and zero of morphisms
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence,
   det-def-sfb-sheaf-tensor-structure).
2. Both direct images evaluate N on V times_T T'. The lax tensor map sends pure
   tensors to the same tensors there. Their actions are eta_f(r) times n, where
   eta_f is f_* alpha_f after the abelian unit (proposition-topos-functoriality--2,
   def-sfb-finite-lower-star-lax-monoidal, prose-03-02,
   sk-def-sfb-coefficient-morphisms). Thus lowerComparison is the identity on sections.
3. Conjugate the specified internal adjunction by E, and use the unique unit-normalized
   left-adjoint comparison (situation-conventions), with the sectionwise
   adjunction of lem-weil-pbc-ringed-topoi-module-adjunction.
4. Naturality of the Hom bijections gives the mate equation, hence the displayed unit
   and counit equations (lem-weil-pbc-adjunction-of-natural-bijection).
5. Repeat for the given internal open-extension adjunction
   (sk-def-sfb-module-lower-shriek) and the sectionwise extension-by-zero adjunction.
6. The direct-image comparisons commute with composition because their section maps
   are identities, and both compositions rebracket the same fibre product. Conjugation
   is injective, so the pullback comparisons commute with composition too
   (def-sfb-module-lower-star-comp, def-sfb-module-upper-star-comp,
   def-weil-pbc-adjunction-conjugate).
7. The open-extension map is the inverse mate of pullback composition: insert eta_j,
   apply the square comparison, then contract epsilon_j'. Steps 4--6 identify each
   factor, yielding the displayed transformation equation (def-weil-pbc-adjunction-mate).
8. The additive equivalences and their inverses preserve finite limits and colimits
   (lem-galois-equivalence-preserves-limits, situation-conventions).
   They therefore preserve and reflect exact sequences and exactness of operations.
   The transformation equation conjugates base change by isomorphisms; equivalences
   reflect isomorphisms, so sectionwise invertibility implies internal invertibility.
-/
theorem internal_module_operations_transport :
    (∀ (T : Scheme.{u}),
      (equivalence Λ T).functor.Additive ∧ (equivalence Λ T).inverse.Additive ∧
      PreservesFiniteLimits (equivalence Λ T).functor ∧
      PreservesFiniteColimits (equivalence Λ T).functor ∧
      PreservesFiniteLimits (equivalence Λ T).inverse ∧
      PreservesFiniteColimits (equivalence Λ T).inverse ∧
      (∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj Λ T))),
        (S.map (equivalence Λ T).functor).Exact ↔ S.Exact) ∧
      (∀ (S : ShortComplex (SheafOfModules.{u + 1} (ring Λ T))),
        (S.map (equivalence Λ T).inverse).Exact ↔ S.Exact)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (mateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
          (.mk _ _ _ _ (upperComparison Λ f).inv)) = (lowerComparison Λ f).hom ∧
      (∀ M,
        (equivalence Λ Y).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app M) ≫
          (lowerComparison Λ f).hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          (lowerStar Λ f).map ((upperComparison Λ f).hom.app M) =
        (adjunction Λ f).unit.app ((equivalence Λ Y).functor.obj M)) ∧
      (∀ N,
        (upperStar Λ f).map ((lowerComparison Λ f).inv.app N) ≫
          (upperComparison Λ f).inv.app ((CondensedRing.lowerStar Λ f).obj N) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app N) =
        (adjunction Λ f).counit.app ((equivalence Λ X).functor.obj N))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
        (openAdjunction Λ j) (.mk _ _ _ _ (openComparison Λ j).inv)) =
        (upperComparison Λ j).hom ∧
      (∀ M,
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M) ≫
          (upperComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≫
          (upperStar Λ j).map ((openComparison Λ j).hom.app M) =
        (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj M)) ∧
      (∀ N,
        (extension Λ j).map ((upperComparison Λ j).inv.app N) ≫
          (openComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj N) ≫
          (equivalence Λ T).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) =
        (openAdjunction Λ j).counit.app ((equivalence Λ T).functor.obj N))) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (PreservesFiniteLimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteLimits (upperStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.upperStar Λ f) ↔
        PreservesFiniteColimits (upperStar Λ f)) ∧
      (PreservesFiniteLimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteLimits (lowerStar Λ f)) ∧
      (PreservesFiniteColimits (CondensedRing.lowerStar Λ f) ↔
        PreservesFiniteColimits (lowerStar Λ f))) ∧
    (∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
      (PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteLimits (extension Λ j)) ∧
      (PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ↔
        PreservesFiniteColimits (extension Λ j))) ∧
    (∀ {U' U T' T : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : ChosenCartesianSquare g' j' j g),
      Functor.whiskerRight (internalBaseChange Λ sq) (equivalence Λ T').functor ≫
          (baseChangeTargetComparison Λ j g).hom =
        (baseChangeSourceComparison Λ g' j').hom ≫
          Functor.whiskerLeft (equivalence Λ U).functor (sectionBaseChange Λ sq) ∧
      (IsIso (sectionBaseChange Λ sq) → IsIso (internalBaseChange Λ sq))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T
    let E := equivalence Λ T
    have : E.functor.Additive := equivalence_additive Λ T
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, ?_⟩
    · intro S
      exact S.exact_map_iff_of_faithful E.functor
    · intro S
      exact S.exact_map_iff_of_faithful E.inverse
  · intro X Y f
    exact ⟨upperComparison_mate Λ f, comparison_unit_counit (equivalence Λ Y) (equivalence Λ X)
      (L := CondensedRing.upperStar Λ f) (R := CondensedRing.lowerStar Λ f)
      (L' := upperStar Λ f) (R' := lowerStar Λ f)
      (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
      (lowerComparison Λ f) (upperComparison Λ f) (upperComparison_mate Λ f)⟩
  · intro U T j _
    exact ⟨openComparison_mate Λ j, comparison_unit_counit (equivalence Λ U) (equivalence Λ T)
      (L := CondensedRing.openImmersionLowerShriek Λ j)
      (R := CondensedRing.upperStar Λ j) (L' := extension Λ j) (R' := upperStar Λ j)
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) (openAdjunction Λ j)
      (upperComparison Λ j) (openComparison Λ j) (openComparison_mate Λ j)⟩
  · intro X Y f
    exact ⟨preserves_finite_limits_iff (equivalence Λ Y) (equivalence Λ X) _ _
        (upperComparison Λ f),
      preserves_finite_colimits_iff (equivalence Λ Y) (equivalence Λ X) _ _
        (upperComparison Λ f),
      preserves_finite_limits_iff (equivalence Λ X) (equivalence Λ Y) _ _
        (lowerComparison Λ f),
      preserves_finite_colimits_iff (equivalence Λ X) (equivalence Λ Y) _ _
        (lowerComparison Λ f)⟩
  · intro U T j _
    exact ⟨preserves_finite_limits_iff (equivalence Λ U) (equivalence Λ T) _ _
        (openComparison Λ j),
      preserves_finite_colimits_iff (equivalence Λ U) (equivalence Λ T) _ _
        (openComparison Λ j)⟩
  · intro U' U T' T g' j' j g _ _ sq
    exact inverseMate_transport
      (equivalence Λ U) (equivalence Λ T) (equivalence Λ U') (equivalence Λ T')
      (J := CondensedRing.openImmersionLowerShriek Λ j)
      (U := CondensedRing.upperStar Λ j)
      (J' := CondensedRing.openImmersionLowerShriek Λ j')
      (U' := CondensedRing.upperStar Λ j')
      (Jb := extension Λ j) (Ub := upperStar Λ j)
      (Jb' := extension Λ j') (Ub' := upperStar Λ j')
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j')
      (openAdjunction Λ j) (openAdjunction Λ j')
      (upperComparison Λ j) (upperComparison Λ j')
      (openComparison Λ j) (openComparison Λ j')
      (openComparison_mate Λ j) (openComparison_mate Λ j')
      (CondensedRing.upperStar Λ g') (CondensedRing.upperStar Λ g)
      (upperStar Λ g') (upperStar Λ g)
      (upperComparison Λ g') (upperComparison Λ g)
      (internalSquare Λ sq).hom (sectionSquare Λ sq).hom (square_compatible Λ sq)

end

end AlgebraicGeometry.ProEtale.InternalModuleOperations
