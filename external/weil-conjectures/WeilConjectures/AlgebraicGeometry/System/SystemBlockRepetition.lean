/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.System.SystemBlockDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Block.BlockOpenExtensionAssembly
import WeilConjectures.AlgebraicGeometry.Block.BlockGeometricCore
import WeilConjectures.AlgebraicGeometry.Block.BlockGeometricAdjunctionAssembly
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Exact block repetition of ordinary derived semilinear systems

Source: Zheng, Construction 4.1 (printed p. 21) and the geometric morphism paragraph
preceding Lemma 4.10 (printed p. 23); finite-block generalization in the DAG;
Stacks Tags 08BJ, 070I, 070Y, 079P, 09T5
(blueprint: lem-pur-system-block-repetition).

Indices here start at zero: index n denotes the paper's index n+1. The actual
module-sheaf categories are `SemilinearSections.Systems`, with ordinary unbounded
localizations `DS`. Section formulas specify the functors, not just their objects
in the derived category. Derived comparisons are normalized before evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ u h w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (t : SystemBlockMap)

private theorem blockPushforward_exact (k : ℕ →o ℕ)
    {S R : Sheaf (coefficientSequenceTopology J) RingCat.{r}}
    (φ : S ⟶ ((blockSite (C := C) k).sheafPushforwardContinuous RingCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology J)).obj R) :
    (SheafOfModules.pushforward.{r} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{r} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{r} φ) := by
  refine ⟨⟨by intros; ext U x; rfl⟩, ?_, ?_⟩
  · let T := SheafOfModules.forget.{r} S ⋙ PresheafOfModules.toPresheaf S.obj
    have : PreservesFiniteLimits (SheafOfModules.pushforward.{r} φ ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{r} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (blockSite (C := C) k).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let : (blockSite (C := C) k).IsCocontinuous
        (coefficientSequenceTopology J) (coefficientSequenceTopology J) :=
      ⟨fun hS ↦ hS⟩
    let : ∀ (F : (ℕ × C)ᵒᵖ ⥤ AddCommGrpCat.{r}),
        (blockSite (C := C) k).op.HasPointwiseRightKanExtension F := fun F X ↦ by
      let : HasLimitsOfShape (StructuredArrow X (blockSite (C := C) k).op)
          AddCommGrpCat.{r} := HasLimitsOfShape.of_essentiallySmall _ _
      infer_instance
    let H := (blockSite (C := C) k).sheafPushforwardContinuous AddCommGrpCat.{r}
      (coefficientSequenceTopology J) (coefficientSequenceTopology J)
    have : PreservesColimitsOfSize.{0, 0} H :=
      ((blockSite (C := C) k).sheafAdjunctionCocontinuous AddCommGrpCat.{r}
        (coefficientSequenceTopology J)
          (coefficientSequenceTopology J)).leftAdjoint_preservesColimits
    let T := SheafOfModules.toSheaf.{r} S
    have : PreservesFiniteColimits (SheafOfModules.pushforward.{r} φ ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf.{r} R ⋙ H)
      infer_instance
    have : ReflectsFiniteColimits T :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

private theorem pushforwardObjHEq
    {D₀ : Type u₁} {D₁ : Type u₂} [Category.{v₁} D₀] [Category.{v₂} D₁]
    {J₀ : GrothendieckTopology D₀} {J₁ : GrothendieckTopology D₁}
    (F : D₀ ⥤ D₁) [F.IsContinuous J₀ J₁]
    {R : Sheaf J₁ RingCat.{r}} {S : Sheaf J₀ RingCat.{r}}
    (e : S = (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).obj R)
    (M : SheafOfModules.{r} R) (U : D₀ᵒᵖ) :
    HEq (((SheafOfModules.pushforward (eqToHom e)).obj M).val.obj U)
      (M.val.obj (F.op.obj U)) := by
  subst S
  rfl

private theorem pushforwardAdjunct
    {D₀ : Type u₁} {D₁ : Type u₂} [Category.{v₁} D₀] [Category.{v₂} D₁]
    {J₀ : GrothendieckTopology D₀} {J₁ : GrothendieckTopology D₁}
    {F : D₀ ⥤ D₁} {G : D₁ ⥤ D₀} [F.IsContinuous J₀ J₁] [G.IsContinuous J₁ J₀]
    {S : Sheaf J₀ RingCat.{r}} {R : Sheaf J₁ RingCat.{r}} (adj : F ⊣ G)
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{r} J₁ J₀).obj S)
    (h₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom)
    (h₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj)
    (P : SheafOfModules.{r} R) (M : SheafOfModules.{r} S)
    (f : (SheafOfModules.pushforward φ).obj P ⟶ M) (U : D₁ᵒᵖ)
    (x : P.val.obj U) :
    ((((SheafOfModules.pushforwardPushforwardAdj adj φ ψ h₁ h₂).homEquiv P M) f).val.app U)
      x = (f.val.app (G.op.obj U)) (P.val.map (adj.counit.app U.unop).op x) := rfl

private theorem transportedPushforwardAdjunction
    {D₀ : Type u₁} {D₁ : Type u₂} [Category.{v₁} D₀] [Category.{v₂} D₁]
    {J₀ : GrothendieckTopology D₀} {J₁ : GrothendieckTopology D₁}
    {F : D₀ ⥤ D₁} {G : D₁ ⥤ D₀} [F.IsContinuous J₀ J₁] [G.IsContinuous J₁ J₀]
    {S : Sheaf J₀ RingCat.{r}} {R : Sheaf J₁ RingCat.{r}} (adj : F ⊣ G)
    (e : S = (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).obj R)
    (d : R = (G.sheafPushforwardContinuous RingCat.{r} J₁ J₀).obj S)
    (hunit : ∀ X : D₀, ∃ h : X = G.obj (F.obj X), adj.unit.app X = eqToHom h)
    (hcounit : ∀ Y : D₁, ∃ h : G.obj (F.obj (G.obj Y)) = G.obj Y,
      G.map (adj.counit.app Y) = eqToHom h) :
    ∃ a : SheafOfModules.pushforward.{r} (eqToHom e) ⊣
        SheafOfModules.pushforward.{r} (eqToHom d),
      ∀ (P : SheafOfModules.{r} R) (M : SheafOfModules.{r} S)
        (f : (SheafOfModules.pushforward (eqToHom e)).obj P ⟶ M) (U : D₁ᵒᵖ)
        (x : P.val.obj U),
        (((a.homEquiv P M) f).val.app U) x =
          (f.val.app (G.op.obj U)) (P.val.map (adj.counit.app U.unop).op x) := by
  let φ := eqToHom e
  let ψ := eqToHom d
  have h₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map (adj.counit.app U.unop).op =
      ψ.hom.app U ≫ φ.hom.app (G.op.obj U)
    apply (cancel_mono (ψ.hom.app (F.op.obj (G.op.obj U)))).mp
    erw [ψ.hom.naturality]
    obtain ⟨h, hh⟩ := hcounit U.unop
    change ψ.hom.app U ≫ S.obj.map (G.map (adj.counit.app U.unop)).op = _
    rw [hh, eqToHom_op, eqToHom_map]
    simp only [φ, ψ, ObjectProperty.eqToHom_hom, eqToHom_app,
      eqToHom_trans]
  have h₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    obtain ⟨h, hh⟩ := hunit U.unop
    change φ.hom.app U ≫ ψ.hom.app (F.op.obj U) ≫
      S.obj.map (adj.unit.app U.unop).op = 𝟙 _
    rw [hh, eqToHom_op, eqToHom_map]
    simp only [φ, ψ, ObjectProperty.eqToHom_hom, eqToHom_app,
      eqToHom_trans, eqToHom_refl]
  exact ⟨SheafOfModules.pushforwardPushforwardAdj adj φ ψ h₁ h₂,
    pushforwardAdjunct adj φ ψ h₁ h₂⟩

private theorem pushforwardEvaluationComparison
    {D₀ : Type u₁} {D₁ : Type u₂} {D₂ : Type u₃}
    [Category.{v₁} D₀] [Category.{v₂} D₁] [Category.{v₃} D₂]
    {J₀ : GrothendieckTopology D₀} {J₁ : GrothendieckTopology D₁}
    {J₂ : GrothendieckTopology D₂} (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂)
    [F.IsContinuous J₀ J₁] [G.IsContinuous J₁ J₂] [(F ⋙ G).IsContinuous J₀ J₂]
    {T : Sheaf J₀ RingCat.{r}} {S : Sheaf J₁ RingCat.{r}} {R : Sheaf J₂ RingCat.{r}}
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J₁ J₂).obj R)
    (ε : T ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{r} J₀ J₂).obj R)
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).map ψ = ε) :
    ∃ δ : SheafOfModules.pushforward.{r} ψ ⋙ SheafOfModules.pushforward.{r} φ ≅
        SheafOfModules.pushforward.{r} ε,
      ∀ (M : SheafOfModules.{r} R) (U : D₀ᵒᵖ)
        (x : ((SheafOfModules.pushforward.{r} ψ ⋙
          SheafOfModules.pushforward.{r} φ).obj M).val.obj U),
        HEq (((δ.hom.app M).val.app U) x) x := by
  exact ⟨SheafOfModules.pushforwardComp φ ψ ≪≫ SheafOfModules.pushforwardCongr h,
    fun _ _ _ ↦ HEq.rfl⟩

private theorem pushforwardEvaluationEquality
    {D₀ : Type u₁} {D₁ : Type u₂} {D₂ : Type u₃}
    [Category.{v₁} D₀] [Category.{v₂} D₁] [Category.{v₃} D₂]
    {J₀ : GrothendieckTopology D₀} {J₁ : GrothendieckTopology D₁}
    {J₂ : GrothendieckTopology D₂} (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂)
    [F.IsContinuous J₀ J₁] [G.IsContinuous J₁ J₂] [(F ⋙ G).IsContinuous J₀ J₂]
    {T : Sheaf J₀ RingCat.{r}} {S : Sheaf J₁ RingCat.{r}} {R : Sheaf J₂ RingCat.{r}}
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat.{r} J₁ J₂).obj R)
    (ε : T ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{r} J₀ J₂).obj R)
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).map ψ = ε) :
    SheafOfModules.pushforward.{r} ψ ⋙ SheafOfModules.pushforward.{r} φ =
      SheafOfModules.pushforward.{r} ε := by
  change SheafOfModules.pushforward.{r} (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{r} J₀ J₁).map ψ) = _
  rw [h]

attribute [local irreducible] systemRing ringPresheaf rings in
/-- Exact endpoint/repetition adjunction on the dependency's actual module-sheaf categories.
Source: Zheng 4.1, finite-block generalization; Stacks 08BJ
(blueprint: lem-pur-system-block-repetition).
Proof: on the sequence site ℕ × C of lem-coef-semilinear-derived-sections, the
first-endpoint reindexing a is left adjoint to the block reindexing t: the unit has
index i ≤ t(a(i)) = i, the counit has index a(t(m)) ≤ m, both with identity vertical
components, and the triangle identities hold by thinness of ℕ. After applying t the
counit and the unit are equality transports, since t(a(i)) = i; so the two ring
equations of Mathlib's SheafOfModules.pushforwardPushforwardAdj hold for the endpoint
and repetition ring identifications, giving blockEndpoint ⊣ blockRepeat. Its unit at
(m,U) is the transition P_m(U) → P_(a(t(m)))(U), which is the adjunct formula.
Composition of pushforwards gives the evaluation isomorphisms, identity on sections.
Reindexing pushforwards are additive and exact (blockPushforward_exact). For acyclic H,
E H is acyclic; Hom_K(H,R I)=Hom_K(E H,I)=0 for K-injective I
(Adjunction.preservesKInjectiveComplexes), which proves the final clause. -/
theorem systemBlockRepetition : Nonempty (SystemBlockRepetition J B τ t) := by
  let siteAdj : blockSite (C := C) t.endpoints ⊣ blockSite t.index :=
    { unit :=
        { app := fun X ↦ Prod.mkHom
            (homOfLE (le_of_eq ((systemBlockMap_endpoints t).1 X.1).symm)) (𝟙 X.2)
          naturality := by
            intros
            apply Prod.hom_ext
            · exact Subsingleton.elim _ _
            · simp [blockSite] }
      counit :=
        { app := fun X ↦ Prod.mkHom
            (homOfLE ((systemBlockMap_endpoints t).2.2.1 X.1).1) (𝟙 X.2)
          naturality := by
            intros
            apply Prod.hom_ext
            · exact Subsingleton.elim _ _
            · simp [blockSite] }
      left_triangle_components := by
        intros
        apply Prod.hom_ext
        · exact Subsingleton.elim _ _
        · simp [blockSite]
      right_triangle_components := by
        intros
        apply Prod.hom_ext
        · exact Subsingleton.elim _ _
        · simp [blockSite] }
  let φ := eqToHom (blockEndpointRing J B τ t).symm
  let ψ := eqToHom (blockRepeatRing J B τ t).symm
  have hunit : ∀ X : ℕ × C,
      ∃ h : X = (blockSite t.index).obj ((blockSite t.endpoints).obj X),
        siteAdj.unit.app X = eqToHom h := by
    intro X
    refine ⟨Prod.ext ((systemBlockMap_endpoints t).1 X.1).symm rfl, ?_⟩
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp [siteAdj]
  have hcounit : ∀ Y : ℕ × C,
      ∃ h : (blockSite t.index).obj
          ((blockSite t.endpoints).obj ((blockSite t.index).obj Y)) =
          (blockSite t.index).obj Y,
        (blockSite t.index).map (siteAdj.counit.app Y) = eqToHom h := by
    intro Y
    refine ⟨Prod.ext ((systemBlockMap_endpoints t).1 (t.index Y.1)) rfl, ?_⟩
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp [siteAdj, blockSite]
  obtain ⟨adj, hadj⟩ := transportedPushforwardAdjunction siteAdj
    (blockEndpointRing J B τ t).symm (blockRepeatRing J B τ t).symm hunit hcounit
  let adj' : blockEndpoint J B τ t ⊣ blockRepeat J B τ t := adj
  have hr := blockPushforward_exact J t.index ψ
  have he := blockPushforward_exact J t.endpoints φ
  let : (blockRepeat J B τ t).Additive := hr.1
  let : (blockEndpoint J B τ t).Additive := he.1
  let : PreservesFiniteLimits (blockEndpoint J B τ t) := he.2.1
  let : PreservesFiniteColimits (blockEndpoint J B τ t) := he.2.2
  let : (blockRepeat J B τ t).PreservesKInjectiveComplexes :=
    adj'.preservesKInjectiveComplexes
  have evalExists (m : ℕ) :
      ∃ ev : blockRepeat J B τ t ⋙ evaluation J (blockCoefficients B t)
          (blockTransitions J B τ t) m ≅ evaluation J B τ (t.index m),
        ∀ (M : Systems J B τ) (U : Cᵒᵖ)
          (x : ((evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m).obj
            ((blockRepeat J B τ t).obj M)).val.obj U),
          HEq (((ev.hom.app M).val.app U) x) x := by
    let θ := eqToHom (evaluation_ring J (blockCoefficients B t)
      (blockTransitions J B τ t) m).symm
    have := Functor.isContinuous_comp (Prod.sectR m C) (blockSite (C := C) t.index)
      J (coefficientSequenceTopology J) (coefficientSequenceTopology J)
    have hp : θ ≫ ((Prod.sectR m C).sheafPushforwardContinuous RingCat.{r}
        J (coefficientSequenceTopology J)).map ψ =
        eqToHom (evaluation_ring J B τ (t.index m)).symm := by
      simp only [θ, ψ, eqToHom_map, eqToHom_trans]
    exact pushforwardEvaluationComparison (Prod.sectR m C) (blockSite (C := C) t.index)
      θ ψ (eqToHom (evaluation_ring J B τ (t.index m)).symm) hp
  choose ev hev using evalExists
  refine ⟨{
    repetition := blockRepeat J B τ t
    repetition_canonical := rfl
    endpoint := blockEndpoint J B τ t
    endpoint_canonical := rfl
    evaluation := ev
    evaluation_sections := hev
    repeat_restrictions := by intros; rfl
    endpoint_sections := by
      intro P i U
      exact pushforwardObjHEq (blockSite (C := C) t.endpoints)
        (blockEndpointRing J B τ t).symm P (op (i, U.unop))
    endpoint_maps := by intros; rfl
    first_monotone := t.firstMonotone
    endpoint_restrictions := by intros; rfl
    adjunction := adj'
    adjunct := ?_
    repeat_additive := hr.1
    repeat_limits := hr.2.1
    repeat_colimits := hr.2.2
    endpoint_additive := he.1
    endpoint_limits := he.2.1
    endpoint_colimits := he.2.2
    kinjective := by intro I hI; let : I.IsKInjective := hI; infer_instance }⟩
  intro P M f m U h x y hy
  apply (heq_of_eq (hadj P M f (op (m, U.unop)) x)).trans
  exact heq_of_eq (congrArg (fun z ↦ (f.val.app (op (t.index m, U.unop))) z)
    (eq_of_heq hy).symm)

section GeometricSystems

omit [EssentiallySmall.{r} C]

variable {C' : Type c} [Category.{v} C']
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (B₀ : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ₀ : ∀ n : ℕ, B₀ (n + 1) ⟶ B₀ n)
  (A : Data.{c, v, r} J B₀ τ₀)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (G : Geometry.{c, v, r} J B₀ τ₀ A J' uInv uPush adjSet)
  (RX : SystemBlockRepetition J' G.coefficients G.coefficientTransition t)
  (RY : SystemBlockRepetition J B₀ τ₀ t)

/-- The actual repeated geometric functors on the repeated coefficient categories.
All level realizations are fixed to the given topos morphism. The square is the
identity on sections, including all transitions, before localization.
Source: Zheng 4.1 and paragraph preceding 4.10
(blueprint: lem-pur-system-block-repetition). -/
structure SystemBlockGeometry where
  /-- Levelwise inverse image for D, on the actual repeated coefficient rings. -/
  pull : Systems J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) ⥤
    Systems J' (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t)
  /-- Levelwise direct image for D. -/
  push : Systems J' (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t) ⥤
    Systems J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t)
  /-- The ordinary geometric adjunction. -/
  adjunction : pull ⊣ push
  /-- Exact additive inverse image. -/
  [pull_additive : pull.Additive]
  /-- Left exactness of inverse image. -/
  [pull_limits : PreservesFiniteLimits pull]
  /-- Right exactness of inverse image. -/
  [pull_colimits : PreservesFiniteColimits pull]
  /-- Additivity of direct image. -/
  [push_additive : push.Additive]
  /-- Resolutions on the actual repeated source system category. -/
  [resolutions : Abelian.HasKInjectiveResolutions
    (Systems J' (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t))]
  /-- Every pullback component is the specified inverse image, not an arbitrary map. -/
  pull_evaluation : ∀ m : ℕ,
    pull ⋙ evaluation J' (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t) m ≅
    evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m ⋙
      (G.inverseImage (t.index m)).modules
  /-- Every pushforward component is the specified direct image. -/
  push_evaluation : ∀ m : ℕ,
    push ⋙ evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m ≅
    evaluation J' (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t) m ⋙
      G.levelPush (t.index m)
  /-- The strict ordinary inverse-image identity, with canonical section realization. -/
  pull_square : G.pull ⋙ RX.repetition ≅ RY.repetition ⋙ pull
  /-- The strict ordinary direct-image identity. -/
  push_square : RX.repetition ⋙ push ≅ G.push ⋙ RY.repetition
  /-- The direct-image comparison is the identity on every section. -/
  push_square_sections : ∀ (M : Systems J' G.coefficients G.coefficientTransition)
    (U : (ℕ × C)ᵒᵖ)
    (x : ((RX.repetition ⋙ push).obj M).val.obj U),
    HEq (((push_square.hom.app M).val.app U) x) x
  /-- The inverse-image comparison is the identity on every section. -/
  pull_square_sections : ∀ (M : Systems J B₀ τ₀) (U : (ℕ × C')ᵒᵖ)
    (x : ((G.pull ⋙ RX.repetition).obj M).val.obj U),
    HEq (((pull_square.hom.app M).val.app U) x) x
  /-- The ordinary units are the identical level units. -/
  unit : ∀ M : Systems J B₀ τ₀,
    RY.repetition.map (G.ordinaryAdjunction.unit.app M) ≫
        push_square.inv.app (G.pull.obj M) ≫ push.map (pull_square.hom.app M) =
      adjunction.unit.app (RY.repetition.obj M)
  /-- The ordinary counits are the identical level counits. -/
  counit : ∀ N : Systems J' G.coefficients G.coefficientTransition,
    pull.map (push_square.inv.app N) ≫ adjunction.counit.app (RX.repetition.obj N) =
      pull_square.inv.app (G.push.obj N) ≫
        RX.repetition.map (G.ordinaryAdjunction.counit.app N)

section
attribute [local irreducible] evaluation systemRing ringPresheaf rings

end

attribute [instance] SystemBlockGeometry.pull_additive SystemBlockGeometry.pull_limits
  SystemBlockGeometry.pull_colimits SystemBlockGeometry.push_additive

/-- All supplied exact block functors preserve K-injectives, so the canonical
comparison is available directly on the actual system categories.
Source: Zheng 4.1 finite-block generalization; Stacks 070Y
(blueprint: lem-pur-system-block-repetition). -/
def SystemBlockGeometry.comparison
    (H : SystemBlockGeometry J t J' B₀ τ₀ A uInv uPush adjSet G RX RY) :=
  letI := H.resolutions
  blockDerivedComparison RX.repetition RY.repetition G.push H.push H.push_square

end GeometricSystems
section OpenLocalization

omit [EssentiallySmall.{r} C]

variable [EssentiallySmall.{max c v r} C]
  (B₀ : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ₀ : ∀ n : ℕ, B₀ (n + 1) ⟶ B₀ n) (U : C)

/-- The ring identification for repetition after restriction to an open slice.
Source: Zheng 4.1, open-localization consequence (blueprint: lem-pur-system-block-repetition).
Proof: both section rings at (m,V→U) are B_(t(m))(V). Restriction to the slice
commutes with composition of tau, so all horizontal and vertical maps agree.
Functor and sheaf extensionality give the claimed equality. -/
theorem blockOpenRepeatRing :
    ((blockSite (C := Over U) t.index).sheafPushforwardContinuous RingCat.{max c v r}
      (coefficientSequenceTopology (J.over U))
      (coefficientSequenceTopology (J.over U))).obj
      (ring (coefficientSequenceTopology (J.over U))
        (systemRing (J.over U) (openRings.{c, v, r} J B₀ U)
          (openTransitions.{c, v, r} J B₀ τ₀ U))) =
    ring (coefficientSequenceTopology (J.over U))
      (systemRing (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U)) := by
  let cmp : rings J B₀ τ₀ ⋙ J.overPullback CommRingCat.{max c v r} U ⟶
      rings (J.over U) (openRings.{c, v, r} J B₀ U)
        (openTransitions.{c, v, r} J B₀ τ₀ U) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  have ht : blockTransitions (J.over U) (openRings.{c, v, r} J B₀ U)
      (openTransitions.{c, v, r} J B₀ τ₀ U) t =
      openTransitions.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U := by
    funext m
    have hh := cmp.naturality (homOfLE (t.index.monotone (Nat.le_succ m))).op
    dsimp only [cmp] at hh
    simp only [NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] at hh
    exact hh.symm
  have hh := blockRepeatRing (J.over U) (openRings.{c, v, r} J B₀ U)
    (openTransitions.{c, v, r} J B₀ τ₀ U) t
  rw [ht] at hh
  exact hh

/-- Actual restriction/repetition on the open sequence site, retaining its coefficient
presentation. It has exactly the data of blockRepeat on the restricted tower.
Source: Zheng 4.1, open-localization consequence (blueprint: lem-pur-system-block-repetition). -/
def blockOpenRepeat :
    Systems (J.over U) (openRings.{c, v, r} J B₀ U) (openTransitions.{c, v, r} J B₀ τ₀ U) ⥤
      Systems (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U) :=
  SheafOfModules.pushforward (F := blockSite (C := Over U) t.index)
    (eqToHom (blockOpenRepeatRing.{c, v, r} J t B₀ τ₀ U).symm)

attribute [local irreducible] systemRing ringPresheaf rings in
private theorem blockOpenRepeat_evaluationEqual (m : ℕ) :
    blockOpenRepeat.{c, v, r} J t B₀ τ₀ U ⋙ evaluation (J.over U)
        (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
          (blockTransitions J B₀ τ₀ t) U) m =
      evaluation (J.over U) (openRings.{c, v, r} J B₀ U)
        (openTransitions.{c, v, r} J B₀ τ₀ U) (t.index m) := by
  let θ := eqToHom (evaluation_ring (J.over U)
    (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
    (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
      (blockTransitions J B₀ τ₀ t) U) m).symm
  let ψ := eqToHom (blockOpenRepeatRing.{c, v, r} J t B₀ τ₀ U).symm
  have := Functor.isContinuous_comp (Prod.sectR m (Over U))
    (blockSite (C := Over U) t.index) (J.over U)
    (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology (J.over U))
  have hp : θ ≫ ((Prod.sectR m (Over U)).sheafPushforwardContinuous
      RingCat.{max c v r} (J.over U) (coefficientSequenceTopology (J.over U))).map ψ =
    eqToHom (evaluation_ring (J.over U) (openRings.{c, v, r} J B₀ U)
      (openTransitions.{c, v, r} J B₀ τ₀ U) (t.index m)).symm := by
    simp only [θ, ψ, eqToHom_map, eqToHom_trans]
  exact pushforwardEvaluationEquality (Prod.sectR m (Over U))
    (blockSite (C := Over U) t.index) θ ψ _ hp

private theorem blockOpenRepeat_restrictions
    (M : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
      (openTransitions.{c, v, r} J B₀ τ₀ U))
    {V W : (ℕ × Over U)ᵒᵖ} (f : V ⟶ W) :
    HEq (fun x ↦ ((blockOpenRepeat.{c, v, r} J t B₀ τ₀ U).obj M).val.map f x)
      (fun x ↦ M.val.map ((blockSite (C := Over U) t.index).map f.unop).op x) := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] evaluation systemRing ringPresheaf rings blockOpenRepeat in
/-- Exact extension by zero commutes with repetition. Both open presentations have
level restriction identifications that are the identity on sections; with their unit
and counit equations this fixes their extension evaluations `e_n j_! = j_! e_n`, so
no levelwise automorphism twists them. The normalization says that under these
actual level realizations the comparison is the identity on every component section.
Consequently it is the strict identity for the direct-sum and sheafification
realizations of the dependency, and commutes with reindexing.
Source: Zheng 4.1, ordinary levelwise operations, open-localization consequence
(blueprint: lem-pur-system-block-repetition).
Proof: extension by zero is the sheafification of the level direct-sum extension.
At (m,V) both sides extend the identical module M_(t(m)) and every component map
and transition is extended by the same j!. The summand identity respects gluing,
so defines the system comparison, with the asserted section normalization after
the dependency's level identifications. It is invertible by the reverse identity.
Exactness descends this ordinary identity termwise by
situation-conventions. A second repetition substitutes
s(m) into the same component identity, so gives the identical comparison and
commutes with the composition identifications; the identity map leaves it unchanged. -/
theorem blockRepeat_extensionByZero
    (R : SystemBlockRepetition J B₀ τ₀ t) :
    ∃ (O : OpenSystems.{c, v, r} J B₀ τ₀ U)
      (OD : OpenSystems.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U),
    (∀ (n : ℕ) N V x, HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x) ∧
    (∀ (n : ℕ) N V x, HEq (((OD.restrictionEvaluation n).hom.app N).val.app V x) x) ∧
    ∃! ξ : blockOpenRepeat.{c, v, r} J t B₀ τ₀ U ⋙ OD.extension ≅ O.extension ⋙ R.repetition,
      ∀ (m : ℕ)
        (P : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
          (openTransitions.{c, v, r} J B₀ τ₀ U)),
        HEq ((evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m).map
            (ξ.hom.app P) ≫ (R.evaluation m).hom.app (O.extension.obj P) ≫
            (O.extensionEvaluation (t.index m)).hom.app P)
          ((OD.extensionEvaluation m).hom.app
            ((blockOpenRepeat.{c, v, r} J t B₀ τ₀ U).obj P)) := by
  exact blockOpenExtensionComparison.{c, v, r} J B₀ τ₀ t U R
    (blockOpenRepeat.{c, v, r} J t B₀ τ₀ U)
    (blockOpenRepeat_evaluationEqual.{c, v, r} J t B₀ τ₀ U)
    (blockOpenRepeat_restrictions.{c, v, r} J t B₀ τ₀ U)

end OpenLocalization
end WeilConjectures.SemilinearSections
