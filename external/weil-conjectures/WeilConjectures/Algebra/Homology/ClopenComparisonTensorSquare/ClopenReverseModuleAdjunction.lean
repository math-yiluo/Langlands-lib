/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ClopenComparisonTensorSquare.ClopenComparisonTensorSquareData
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenOperationModels
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing

/-! # Existence of normalized clopen tensor data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

-- The right adjoint uses base change of test objects and the actual ring counit.
private abbrev push (m : Mode) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] (R : Sheaf (topology m X) CommRingCat.{u + 1}) :=
  direct m s R (restrictRing m s R) (openRightCoefficient m s R)

private theorem ordinaryPair_bijective {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (M : SheafOfModules.{u + 1} R) (W : X.ProEt) :
    Function.Bijective (fun x : M.val.obj (op W) ↦
      (M.val.map (ProEt.clopenTestInclusion s W).op x,
        M.val.map (ProEt.clopenTestInclusion c W).op x)) := by
  classical
  let Y : Bool → Scheme.{u} := Bool.rec U C
  let j : ∀ b, Y b ⟶ X := Bool.rec s c
  have hj : ∀ b, IsOpenImmersion (j b) := by
    intro b
    cases b <;> dsimp [j, Y] <;> infer_instance
  let : ∀ b, IsOpenImmersion (j b) := hj
  have hd : Pairwise (fun b d ↦ Disjoint
      (Set.range (fun x : Y b ↦ (j b).base x))
      (Set.range (fun x : Y d ↦ (j d).base x))) := by
    intro b d hbd
    cases b <;> cases d
    · exact (hbd rfl).elim
    · change Disjoint (Set.range s) (Set.range c)
      rw [hc]
      exact disjoint_compl_right
    · change Disjoint (Set.range c) (Set.range s)
      rw [hc]
      exact disjoint_compl_left
    · exact (hbd rfl).elim
  have hcover (x : X) : ∃ b, x ∈ Set.range (fun z : Y b ↦ (j b).base z) := by
    by_cases hx : x ∈ Set.range s
    · exact ⟨false, hx⟩
    · exact ⟨true, by change x ∈ Set.range c; rwa [hc]⟩
  have hb := @ProEt.clopenSections_bijective X Bool Y j hj hd hcover R M W
  constructor
  · intro x y hxy
    apply hb.1
    funext b
    cases b
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · intro x
    obtain ⟨z, hz⟩ := hb.2 (fun b ↦ match b with
      | false => x.1
      | true => x.2)
    exact ⟨z, Prod.ext (congrFun hz false) (congrFun hz true)⟩

private theorem sliceContinuous (X : Scheme.{u}) (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (ProEt.topology X) (topology .systems X) := by
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  rw [topology_systems_eq X]
  exact WeilConjectures.SemilinearSections.evaluationContinuous.{u + 1, u, u + 1}
    (ProEt.topology X) n

private def pairLinear (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : (Site m X)ᵒᵖ) :
    M.val.obj W →ₗ[R.obj.obj W]
      ((push m s R).obj ((restrict m s R).obj M)).val.obj W ×
        ((push m c R).obj ((restrict m c R).obj M)).val.obj W :=
  ((openRestrictionAdjunction m s R).unit.app M).val.app W |>.hom.prod
    (((openRestrictionAdjunction m c R).unit.app M).val.app W).hom

private theorem pair_bijective (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : (Site m X)ᵒᵖ) : Function.Bijective (pairLinear m s c R M W) := by
  cases m with
  | ordinary =>
    exact ordinaryPair_bijective s c hc _ M W.unop
  | systems =>
    rcases W with ⟨n, V⟩
    have := sliceContinuous X n
    let A := (sheafCompose (topology .systems X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let Rₙ := ((Prod.sectR n X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (topology .systems X)).obj A
    let Mₙ : SheafOfModules.{u + 1} Rₙ :=
      (SheafOfModules.pushforward (F := Prod.sectR n X.ProEt) (𝟙 Rₙ)).obj M
    exact ordinaryPair_bijective s c hc Rₙ Mₙ V

private theorem siteUnit_isIso (m : Mode) {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s] (W : Site m U) :
    IsIso ((openSiteAdjunction m s).unit.app W) := by
  cases m with
  | ordinary => exact ProEt.clopenDiagonal_isIso s W
  | systems =>
    change IsIso (Prod.mkHom (𝟙 W.1) (ProEt.clopenDiagonal s W.2))
    exact (CategoryTheory.isIso_prod_iff ℕ U.ProEt).2
      ⟨inferInstanceAs (IsIso (𝟙 W.1)), ProEt.clopenDiagonal_isIso s W.2⟩

private theorem counit_isIso (m : Mode) {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    IsIso (openRestrictionAdjunction m s R).counit := by
  have hsite (W : Site m U) : IsIso ((openSiteAdjunction m s).unit.app W) :=
    siteUnit_isIso m s W
  have hM (M : Mod (restrictRing m s R)) :
      IsIso ((openRestrictionAdjunction m s R).counit.app M) := by
    let f := ((openRestrictionAdjunction m s R).counit.app M).val
    have hW (W : (Site m U)ᵒᵖ) : IsIso (f.app W) := by
      apply (ConcreteCategory.isIso_iff_bijective _).2
      exact ConcreteCategory.bijective_of_isIso
        (M.val.presheaf.map ((openSiteAdjunction m s).unit.app W.unop).op)
    let e := PresheafOfModules.isoMk (fun W ↦ asIso (f.app W))
      (fun {_ _} g ↦ f.naturality g)
    have : IsIso f := by change IsIso e.hom; infer_instance
    have : IsIso ((SheafOfModules.forget _).map
        ((openRestrictionAdjunction m s R).counit.app M)) := ‹IsIso f›
    exact isIso_of_reflects_iso ((openRestrictionAdjunction m s R).counit.app M)
      (SheafOfModules.forget _)
  exact NatIso.isIso_of_isIso_app _

private def extendLinear (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : (Site m X)ᵒᵖ) :
    ((push m s R).obj ((restrict m s R).obj M)).val.obj W →ₗ[R.obj.obj W]
      M.val.obj W :=
  (LinearEquiv.ofBijective (pairLinear m s c R M W)
    (pair_bijective m s c hc R M W)).symm.toLinearMap.comp
      (LinearMap.inl (R.obj.obj W) _ _)

private theorem extend_fst (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : (Site m X)ᵒᵖ)
    (x : ((push m s R).obj ((restrict m s R).obj M)).val.obj W) :
    (((openRestrictionAdjunction m s R).unit.app M).val.app W)
      (extendLinear m s c hc R M W x) = x :=
  congrArg Prod.fst ((LinearEquiv.ofBijective (pairLinear m s c R M W)
    (pair_bijective m s c hc R M W)).apply_symm_apply (x, 0))

private theorem extend_snd (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : (Site m X)ᵒᵖ)
    (x : ((push m s R).obj ((restrict m s R).obj M)).val.obj W) :
    (((openRestrictionAdjunction m c R).unit.app M).val.app W)
      (extendLinear m s c hc R M W x) = 0 :=
  congrArg Prod.snd ((LinearEquiv.ofBijective (pairLinear m s c R M W)
    (pair_bijective m s c hc R M W)).apply_symm_apply (x, 0))

-- This is the morphism that inserts the first component and zero in the complement.
private def extensionCounit (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    restrict m s R ⋙ push m s R ⟶ 𝟭 (Mod R) where
  app M :=
    { val :=
        { app W := ModuleCat.ofHom
            (X := ((push m s R).obj ((restrict m s R).obj M)).val.obj W)
            (Y := M.val.obj W) (extendLinear m s c hc R M W)
          naturality := by
            intro V W f
            ext x
            apply (pair_bijective m s c hc R M W).injective
            apply Prod.ext
            · change (((openRestrictionAdjunction m s R).unit.app M).val.app W)
                  (extendLinear m s c hc R M W
                    (((push m s R).obj ((restrict m s R).obj M)).val.map f x)) =
                (((openRestrictionAdjunction m s R).unit.app M).val.app W)
                  (M.val.map f (extendLinear m s c hc R M V x))
              rw [extend_fst]
              have h := PresheafOfModules.naturality_apply
                ((openRestrictionAdjunction m s R).unit.app M).val f
                (extendLinear m s c hc R M V x)
              have h' := congrArg
                (fun y ↦ ((push m s R).obj ((restrict m s R).obj M)).val.map f y)
                (extend_fst m s c hc R M V x)
              exact h'.symm.trans h.symm
            · change (((openRestrictionAdjunction m c R).unit.app M).val.app W)
                  (extendLinear m s c hc R M W
                    (((push m s R).obj ((restrict m s R).obj M)).val.map f x)) =
                (((openRestrictionAdjunction m c R).unit.app M).val.app W)
                  (M.val.map f (extendLinear m s c hc R M V x))
              rw [extend_snd]
              have h := PresheafOfModules.naturality_apply
                ((openRestrictionAdjunction m c R).unit.app M).val f
                (extendLinear m s c hc R M V x)
              have h' := congrArg
                (fun y ↦ ((push m c R).obj ((restrict m c R).obj M)).val.map f y)
                (extend_snd m s c hc R M V x)
              exact (h.trans (h'.trans (map_zero _))).symm } }
  naturality {M N} f := by
    ext W x
    apply (pair_bijective m s c hc R N W).injective
    apply Prod.ext
    · change (((openRestrictionAdjunction m s R).unit.app N).val.app W)
          (extendLinear m s c hc R N W
            (((push m s R).map ((restrict m s R).map f)).val.app W x)) =
        (((openRestrictionAdjunction m s R).unit.app N).val.app W)
          (f.val.app W (extendLinear m s c hc R M W x))
      rw [extend_fst]
      have h := congrArg (fun a ↦ a.val.app W (extendLinear m s c hc R M W x))
        ((openRestrictionAdjunction m s R).unit.naturality f)
      change (((openRestrictionAdjunction m s R).unit.app N).val.app W)
          (f.val.app W (extendLinear m s c hc R M W x)) =
        (((push m s R).map ((restrict m s R).map f)).val.app W)
          ((((openRestrictionAdjunction m s R).unit.app M).val.app W)
            (extendLinear m s c hc R M W x)) at h
      rw [extend_fst] at h
      exact h.symm
    · change (((openRestrictionAdjunction m c R).unit.app N).val.app W)
          (extendLinear m s c hc R N W
            (((push m s R).map ((restrict m s R).map f)).val.app W x)) =
        (((openRestrictionAdjunction m c R).unit.app N).val.app W)
          (f.val.app W (extendLinear m s c hc R M W x))
      rw [extend_snd]
      have h := congrArg (fun a ↦ a.val.app W (extendLinear m s c hc R M W x))
        ((openRestrictionAdjunction m c R).unit.naturality f)
      change (((openRestrictionAdjunction m c R).unit.app N).val.app W)
          (f.val.app W (extendLinear m s c hc R M W x)) =
        (((push m c R).map ((restrict m c R).map f)).val.app W)
          ((((openRestrictionAdjunction m c R).unit.app M).val.app W)
            (extendLinear m s c hc R M W x)) at h
      rw [extend_snd, map_zero] at h
      exact h.symm

private theorem complementEmpty {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (V : U.ProEt) :
    IsEmpty (ProEt.clopenTestPiece c ((proEtaleOpenComposition s).obj V)).left := by
  constructor
  intro z
  have hd : Disjoint (Set.range s) (Set.range c) := by
    rw [hc]
    exact disjoint_compl_right
  exact Set.disjoint_left.mp hd
    ⟨V.hom (pullback.fst (V.hom ≫ s) c z), rfl⟩
    ⟨pullback.snd (V.hom ≫ s) c z,
      congrArg (fun f ↦ f z) (pullback.condition (f := V.hom ≫ s) (g := c)).symm⟩

private theorem complementSections_subsingleton (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R)
    (W : Site m U) :
    Subsingleton (((push m c R).obj ((restrict m c R).obj M)).val.obj
      (op ((openInclusion m s).obj W))) := by
  cases m with
  | ordinary =>
    have : IsEmpty ((proEtaleOpenComposition c).obj
        (ProEt.clopenTestPiece c ((proEtaleOpenComposition s).obj W))).left :=
      complementEmpty s c hc W
    exact ProEt.moduleSections_empty _ M
      ((proEtaleOpenComposition c).obj
        (ProEt.clopenTestPiece c ((proEtaleOpenComposition s).obj W)))
  | systems =>
    rcases W with ⟨n, V⟩
    have := sliceContinuous X n
    let A := (sheafCompose (topology .systems X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let Rₙ := ((Prod.sectR n X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (topology .systems X)).obj A
    let Mₙ : SheafOfModules.{u + 1} Rₙ :=
      (SheafOfModules.pushforward (F := Prod.sectR n X.ProEt) (𝟙 Rₙ)).obj M
    have : IsEmpty ((proEtaleOpenComposition c).obj
        (ProEt.clopenTestPiece c ((proEtaleOpenComposition s).obj V))).left :=
      complementEmpty s c hc V
    exact ProEt.moduleSections_empty Rₙ Mₙ
      ((proEtaleOpenComposition c).obj
        (ProEt.clopenTestPiece c ((proEtaleOpenComposition s).obj V)))

private theorem extensionCounit_restrict (m : Mode) {U C X : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ)
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) (M : Mod R) :
    (restrict m s R).map ((extensionCounit m s c hc R).app M) =
      (openRestrictionAdjunction m s R).counit.app ((restrict m s R).obj M) := by
  ext W x
  change extendLinear m s c hc R M (op ((openInclusion m s).obj W.unop)) x =
    M.val.map ((openInclusion m s).map ((openSiteAdjunction m s).unit.app W.unop)).op x
  apply (pair_bijective m s c hc R M (op ((openInclusion m s).obj W.unop))).injective
  apply Prod.ext
  · change (((openRestrictionAdjunction m s R).unit.app M).val.app
        (op ((openInclusion m s).obj W.unop)))
        (extendLinear m s c hc R M (op ((openInclusion m s).obj W.unop)) x) = _
    rw [extend_fst]
    have := siteUnit_isIso m s W.unop
    have : IsIso ((openInclusion m s).map
        ((openSiteAdjunction m s).unit.app W.unop)) := inferInstance
    have ht : (openSiteAdjunction m s).counit.app ((openInclusion m s).obj W.unop) ≫
        (openInclusion m s).map ((openSiteAdjunction m s).unit.app W.unop) = 𝟙 _ := by
      have hleft := (openSiteAdjunction m s).left_triangle_components W.unop
      have hi := IsIso.inv_eq_of_hom_inv_id hleft
      exact (congrArg (fun f ↦ f ≫ (openInclusion m s).map
        ((openSiteAdjunction m s).unit.app W.unop)) hi.symm).trans (IsIso.inv_hom_id _)
    change x = M.val.map ((openSiteAdjunction m s).counit.app
      ((openInclusion m s).obj W.unop)).op
        (M.val.map ((openInclusion m s).map
          ((openSiteAdjunction m s).unit.app W.unop)).op x)
    have h := M.val.map_comp_apply
      ((openInclusion m s).map ((openSiteAdjunction m s).unit.app W.unop)).op
      ((openSiteAdjunction m s).counit.app ((openInclusion m s).obj W.unop)).op x
    have h' : M.val.map
        (((openInclusion m s).map ((openSiteAdjunction m s).unit.app W.unop)).op ≫
          ((openSiteAdjunction m s).counit.app ((openInclusion m s).obj W.unop)).op)
        x = x := by
      change M.val.presheaf.map
        (((openInclusion m s).map ((openSiteAdjunction m s).unit.app W.unop)).op ≫
          ((openSiteAdjunction m s).counit.app ((openInclusion m s).obj W.unop)).op)
        x = x
      rw [← op_comp, ht, op_id]
      exact CategoryTheory.congr_fun (M.val.presheaf.map_id
        (op ((baseChange m s ⋙ openInclusion m s).obj
          ((openInclusion m s).obj W.unop)))) x
    exact h'.symm.trans h
  · have := complementSections_subsingleton m s c hc R M W.unop
    exact Subsingleton.elim _ _

private def oppositeAdjunction
    {D E : Type*} [Category D] [Category E]
    (r : D ⥤ E) (P : E ⥤ D) (b : r ⊣ P) [IsIso b.counit]
    (v : r ⋙ P ⟶ 𝟭 D)
    (hv : ∀ M, r.map (v.app M) = b.counit.app (r.obj M)) : P ⊣ r where
  unit := inv b.counit
  counit := v
  left_triangle_components N := by
    apply (b.homEquiv (P.obj N) N).symm.injective
    change r.map (P.map ((inv b.counit).app N) ≫ v.app (P.obj N)) ≫
        b.counit.app N = r.map (𝟙 _) ≫ b.counit.app N
    rw [Functor.map_comp, hv]
    have hn := b.counit.naturality ((inv b.counit).app N)
    change r.map (P.map ((inv b.counit).app N)) ≫
        b.counit.app (r.obj (P.obj N)) =
      b.counit.app N ≫ (inv b.counit).app N at hn
    rw [hn]
    simp
  right_triangle_components M := by
    rw [hv]
    simp

/-- An exact open extension has a normalized reverse adjunction on a clopen piece.
Source: Stacks 04TS, disjoint two-open module gluing.
(blueprint: lem-sf-clopen-reverse-module-adjunction).

Proof: decompose the ambient scheme into the image of s and its complementary
open. Ringed-module gluing identifies modules with pairs on those two pieces.
Restriction to s is projection onto the first coordinate. Insert a module in
that coordinate and zero in the second to construct extension. This is both
left and right adjoint to restriction. The ordinary open unit and reverse
counit have identity first coordinates, so their composite is identity.
Transport the coordinate adjunctions back through the gluing equivalence.
The insertion and projection maps commute with semilinear coefficient maps;
therefore the same equivalence and adjunctions exist on the vertical ringed
site in systems mode, before localization or evaluation. Exactness is
componentwise in the product module category. -/
theorem clopen_reverse_module_adjunction (m : Mode) {A X : Scheme.{u}}
    (s : A ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (R : Sheaf (topology m X) CommRingCat.{u + 1}) :
    ∃ e : OpenExtension m s R, ∃ ar : restrict m s R ⊣ e.ordinary,
      ∀ M, e.adjunction.unit.app M ≫ ar.counit.app M = 𝟙 M := by
  let O : X.Opens :=
    ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let c := O.ι
  have hc : Set.range c = (Set.range s)ᶜ := Scheme.Opens.range_ι O
  let b := openRestrictionAdjunction m s R
  have : IsIso b.counit := counit_isIso m s R
  let v := extensionCounit m s c hc R
  let a := oppositeAdjunction (restrict m s R) (push m s R) b v
    (extensionCounit_restrict m s c hc R)
  have : PreservesLimitsOfSize.{0, 0} (push m s R) := b.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{0, 0} (push m s R) := a.leftAdjoint_preservesColimits
  have hAdd : (push m s R).Additive := by
    constructor
    intro M N f g
    ext W x
    rfl
  let e : OpenExtension m s R :=
    { ordinary := push m s R
      adjunction := a
      sectionIso := fun M ↦ (asIso b.counit).app M
      sectionUnit := fun M ↦ by
        change (inv b.counit).app M ≫ b.counit.app M = 𝟙 M
        simp only [NatIso.isIso_inv_app, IsIso.inv_hom_id, Functor.id_obj]
      additive := hAdd
      limits := inferInstance
      colimits := inferInstance }
  refine ⟨e, b, ?_⟩
  intro M
  change (inv b.counit).app M ≫ b.counit.app M = 𝟙 M
  simp only [NatIso.isIso_inv_app, IsIso.inv_hom_id, Functor.id_obj]

end SheafOfModules.ClopenComparisonTensorSquare
