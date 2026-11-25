/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.InverseImageAction.SignedLineModuleInverseImageAction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.SignedLineSheafPullbackUnitPresentation
import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.SignedLineModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SignedLineSheafPullbackForgetComparison
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
/-! # Restricting the abelian inverse-image adjunction to modules
Source: Stacks Project, Modules on Sites, Tag 03D3.
(blueprint: lem-pur-signed-line-module-inverse-image-adjunction).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLinePullbackConstruction
open CategoryTheory.SignedLinePullbackConstruction
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {A : Sheaf J RingCat.{max u v w}} {B : Sheaf K RingCat.{max u v w}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{max u v w} J K).obj B)
  [(pushforward.{max u v w} φ).IsRightAdjoint]
open MonoidalCategory
private noncomputable def scalarAction (M : SheafOfModules.{max u v w} B) :
    (sheafCompose K (CategoryTheory.forget RingCat.{max u v w})).obj B ⊗
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj ((toSheaf B).obj M) ⟶
      (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj ((toSheaf B).obj M) :=
  ⟨{ app := fun U ↦ ↾fun x ↦
       @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x.1 x.2
     naturality := by
       intro U V i
       ext x
       exact (M.val.map_smul i x.1 x.2).symm }⟩
variable (hgen : ∀ (M : SheafOfModules.{max u v w} A) (T : Sheaf K (Type (max u v w)))
  (a b : (sheafCompose K (CategoryTheory.forget RingCat.{max u v w})).obj B ⊗
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj
      ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M)) ⟶ T),
  (∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
    a.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) =
      b.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) → a = b)
include hgen in
private theorem linear_of_adjunct_linear
    (M : SheafOfModules.{max u v w} A) (N : SheafOfModules.{max u v w} B)
    (a : InverseImageAction φ M)
    (α : (sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M) ⟶
      (toSheaf B).obj N)
    (hβ : ∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
      ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).homEquiv _ _ α).hom.app U
        (r • m) =
        @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
          (φ.hom.app U r)
          (((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).homEquiv _ _ α).hom.app
            U m)) :
    ∀ (V : Dᵒᵖ) (r : B.obj.obj V) (m : a.toModule.val.obj V),
      α.hom.app V (r • m) =
        @SMul.smul (B.obj.obj V) (N.val.obj V) inferInstance r (α.hom.app V m) := by
  let t := (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).map α
  have hmaps : scalarAction a.toModule ≫ t =
      (𝟙 _ ⊗ₘ t) ≫ scalarAction N := by
    apply hgen M
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj ((toSheaf B).obj N))
      (scalarAction a.toModule ≫ t) ((𝟙 _ ⊗ₘ t) ≫ scalarAction N)
    intro U r m
    change α.hom.app (F.op.obj U)
      ((show B.obj.obj (F.op.obj U) from φ.hom.app U r) •
        (show a.toModule.val.obj (F.op.obj U) from
          ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) = _
    rw [← a.unit_smul U r m]
    exact hβ U r m
  intro V r m
  exact congrArg (fun q ↦ q.hom.app V (r, m)) hmaps
include hgen in
/-- Identify module pullback after constructing its action and testing scalar maps on units.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-pur-signed-line-module-inverse-image-adjunction).
Proof: The unit is linear by the action hypothesis. The scalar-pair testing property
shows that an abelian map is linear whenever its adjunct is linear: compare its two
scalar-action composites on pairs of unit sections. Lift the abelian inverse-image
maps using this criterion. Faithfulness proves the functor laws. The abelian hom
bijection restricts to linear maps in both directions, naturally. This gives a module
adjunction to the specified scalar-restricted pushforward. Uniqueness of left adjoints
identifies it with Mathlib's pullback. Forgetting gives the stated comparison. -/
private theorem inverseImage_underlying_of_actions
    (actions : ∀ M : SheafOfModules.{max u v w} A, InverseImageAction φ M) :
    ∃ e : pullback.{max u v w} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{max u v w} J K,
      ∀ M : SheafOfModules.{max u v w} A,
        (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
          (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).map (e.hom.app M) =
            (sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
              ((toSheaf A).obj M) := by
  let La := sheafPullback F AddCommGrpCat.{max u v w} J K
  let Ra := F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K
  let adj := sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K
  let P := toSheaf A
  let Q := toSheaf B
  let T := pushforward.{max u v w} φ
  let obj (M : SheafOfModules.{max u v w} A) := (actions M).toModule
  let lift (M : SheafOfModules.{max u v w} A) (N : SheafOfModules.{max u v w} B)
      (α : La.obj (P.obj M) ⟶ Q.obj N)
      (hβ : ∀ U (r : A.obj.obj U) (m : M.val.obj U),
        (adj.homEquiv _ _ α).hom.app U (r • m) =
          @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
            (φ.hom.app U r) ((adj.homEquiv _ _ α).hom.app U m)) : obj M ⟶ N :=
    ⟨PresheafOfModules.homMk α.hom
      (linear_of_adjunct_linear φ hgen M N (actions M) α hβ)⟩
  let η (M : SheafOfModules.{max u v w} A) : M ⟶ T.obj (obj M) :=
    ⟨PresheafOfModules.homMk (adj.unit.app (P.obj M)).hom
      (fun U r m ↦ (actions M).unit_smul U r m)⟩
  let map {M N : SheafOfModules.{max u v w} A} (g : M ⟶ N) : obj M ⟶ obj N :=
    lift M (obj N) (La.map (P.map g)) (by
      intro U r m
      change (adj.homEquiv (P.obj M) (La.obj (P.obj N))
        (La.map (P.map g))).hom.app U (r • m) =
        @SMul.smul (B.obj.obj (F.op.obj U)) ((obj N).val.obj (F.op.obj U)) inferInstance
          (φ.hom.app U r) ((adj.homEquiv (P.obj M) (La.obj (P.obj N))
            (La.map (P.map g))).hom.app U m)
      have h : adj.homEquiv _ _ (La.map (P.map g)) =
          P.map g ≫ adj.unit.app (P.obj N) := by
        rw [Adjunction.homEquiv_unit, adj.unit_naturality]
      rw [h]
      change (η N).val.app U (g.val.app U (r • m)) = _
      rw [(g.val.app U).hom.map_smul]
      exact ((η N).val.app U).hom.map_smul r (g.val.app U m))
  have hmap₀ {M N : SheafOfModules.{max u v w} A} (g : M ⟶ N) :
      Q.map (map g) = La.map (P.map g) := by
    ext U m
    rfl
  let L : SheafOfModules.{max u v w} A ⥤ SheafOfModules.{max u v w} B :=
    { obj := obj
      map := map
      map_id := by
        intro M
        apply Q.map_injective
        rw [hmap₀, P.map_id, La.map_id, Q.map_id]
        rfl
      map_comp := by
        intro M N O g h
        apply Q.map_injective
        rw [Q.map_comp, hmap₀, hmap₀, hmap₀]
        exact (P ⋙ La).map_comp g h }
  have hmap {M N : SheafOfModules.{max u v w} A} (g : M ⟶ N) :
      Q.map (L.map g) = La.map (P.map g) := hmap₀ g
  let e : L ⋙ Q ≅ P ⋙ La := NatIso.ofComponents
    (fun M ↦ (actions M).underlyingIso) (by
      intro M N g
      change Q.map (L.map g) ≫ 𝟙 _ = 𝟙 _ ≫ La.map (P.map g)
      simpa using hmap g)
  let d : T ⋙ P ≅ Q ⋙ Ra := Iso.refl _
  have hlin (M : SheafOfModules.{max u v w} A) (N : SheafOfModules.{max u v w} B)
      (α : La.obj (P.obj M) ⟶ Q.obj N) :
      (∃ h : L.obj M ⟶ N, Q.map h = e.hom.app M ≫ α) ↔
        ∃ k : M ⟶ T.obj N,
          P.map k ≫ d.hom.app N = adj.homEquiv _ _ α := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨η M ≫ T.map h, ?_⟩
      change adj.unit.app (P.obj M) ≫ Ra.map (Q.map h) ≫ 𝟙 _ = _
      change Q.map h = 𝟙 _ ≫ α at hh
      simp only [Category.id_comp] at hh
      rw [hh, Category.comp_id]
      rfl
    · rintro ⟨k, hk⟩
      have hk' : P.map k = adj.homEquiv _ _ α := by
        change P.map k ≫ 𝟙 _ = _ at hk
        simpa only [Category.comp_id] using hk
      refine ⟨lift M N α (fun U r m ↦ ?_), ?_⟩
      · rw [← hk']
        exact (k.val.app U).hom.map_smul r m
      · ext U m
        rfl
  obtain ⟨am, _, hu, _⟩ :=
    AlgebraicGeometry.adjunctionOfLinearLifts L T La Ra P Q adj e d hlin
  let q := (pullbackPushforwardAdjunction φ).leftAdjointUniq am
  refine ⟨Functor.isoWhiskerRight q Q ≪≫ e, ?_⟩
  intro M
  have hq := Adjunction.unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction φ) am M
  have h := congrArg P.map hq
  have hh : P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
      P.map (T.map (q.hom.app M)) = P.map (am.unit.app M) := by
    simpa only [Functor.map_comp] using h
  have hu0 : P.map (am.unit.app M) = adj.unit.app (P.obj M) := by
    have hu' := hu M
    change P.map (am.unit.app M) ≫ 𝟙 _ =
      adj.unit.app (P.obj M) ≫ Ra.map (𝟙 _) at hu'
    erw [Ra.map_id] at hu'
    exact (Category.comp_id _).symm.trans (hu'.trans (Category.comp_id _))
  change P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
    Ra.map (Q.map (q.hom.app M) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  change P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
    P.map (T.map (q.hom.app M)) = _
  exact hh.trans hu0
/-- A ring unit presenting the set inverse image identifies the underlying module pullback.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-pur-signed-line-module-inverse-image-adjunction).
Proof: the canonical abelian/set comparison is compatible with its unit. Pair this
presentation with the given ring presentation. It both constructs scalar actions and
shows that linearity can be tested on unit pairs. Apply the restricted adjunction
comparison proved above. The unit equation for leftAdjointUniq identifies the chosen
module unit, followed by this comparison, with the original abelian unit. -/
theorem inverseImage_underlying_of_ring_presentation
    [(CategoryTheory.forget AddCommGrpCat.{max u v w}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (CategoryTheory.forget AddCommGrpCat.{max u v w})]
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type (max u v w)) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{max u v w})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{max u v w})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{max u v w})).map φ) :
    ∃ e : pullback.{max u v w} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{max u v w} J K,
      ∀ M : SheafOfModules.{max u v w} A,
        (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
          (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).map (e.hom.app M) =
            (sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app
              ((toSheaf A).obj M) := by
  let ea := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{max u v w})
  let pa (M : SheafOfModules.{max u v w} A) : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj ((toSheaf A).obj M))
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj
        ((sheafPullback F AddCommGrpCat.{max u v w} J K).obj ((toSheaf A).obj M))) :=
    { unit := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v w})).map
        ((sheafAdjunctionContinuous F AddCommGrpCat.{max u v w} J K).unit.app ((toSheaf A).obj M))
      iso := ea.app ((toSheaf A).obj M)
      equation := fun U x ↦ by
        have h := sheafPullbackForgetIso_unit J K F
          (CategoryTheory.forget AddCommGrpCat.{max u v w}) ((toSheaf A).obj M)
        exact congrArg (fun t ↦ t.hom.app U x) h }
  apply inverseImage_underlying_of_actions φ
    (fun M Z a b h ↦ ?_) (fun M ↦ Classical.choice
      (inverseImageAction_of_presentations φ M pr hr (pa M) rfl))
  apply (pr.tensor (pa M)).hom_ext a b
  intro U x
  change a.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2) =
    b.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2)
  rw [hr]
  exact h U x.1 x.2

end SheafOfModules.SignedLinePullbackConstruction
