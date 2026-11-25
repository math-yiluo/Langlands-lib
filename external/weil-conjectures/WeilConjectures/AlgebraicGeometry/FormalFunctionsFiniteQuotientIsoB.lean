/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotient
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_scalar {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (n : ℕ) (a : Y.presheaf.stalk y) :
    (formalFunctionsFiniteι f y n).appTop.hom
      (((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
        (pullback.fst (Y.fromSpecStalk y) f).appTop).hom a) =
      formalFibreScalarMap f y n
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
          (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
              (Y.presheaf.stalk y)) a)) := by
  have h : formalFunctionsFiniteι f y n ≫ pullback.fst (Y.fromSpecStalk y) f =
      pullback.fst (formalFibreBaseMap Y y n) f ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n))) := by
    simp [formalFunctionsFiniteι]
  have hΓ := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at hΓ
  have hs := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n)))
  have hc : (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
      (pullback.fst (Y.fromSpecStalk y) f).appTop ≫
        (formalFunctionsFiniteι f y n).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (formalFibreIdeal Y y n)) ≫
        (Scheme.ΓSpecIso _).inv ≫ (pullback.fst (formalFibreBaseMap Y y n) f).appTop := by
    rw [hΓ, ← Category.assoc, ← hs, Category.assoc]
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]
  change (((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
    (pullback.fst (Y.fromSpecStalk y) f).appTop ≫
      (formalFunctionsFiniteι f y n).appTop).hom a) = _
  rw [hc]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
-- Scalar restriction and the two cohomology functors require extra elaboration steps.
/-- Finite quotient-system isomorphism and quotient-unit factorization.
Source: Stacks Project, Tag 02OD and Tag 089W.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-iso-b)
Proof: Construct the finite-level closed-immersion quotient identifications, apply
cohomology and the affine edge isomorphism, and check adjacent-level naturality.
The quotient-unit equation is the defining adjunction-unit equation. -/
theorem formalFunctions_finite_quotient_iso_b {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∃ b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
    ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
      (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z) =
        formalFunctionsFinitePullback f y F p n z := by
  classical
  dsimp only
  let X' := pullback (Y.fromSpecStalk y) f
  let f' := pullback.fst (Y.fromSpecStalk y) f
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let J := (Scheme.IdealSheafData.ofIdealTop
    ((maximalIdeal (Y.presheaf.stalk y)).map
      (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
  let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
  let S := formalCompletionSystem J F' ⋙ C
  let T := formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
    (algebraMap (Y.presheaf.stalk y)
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
  have hsheaf := formalFunctions_finite_sheaf_quotient f F y
  dsimp only at hsheaf
  have hc (n : ℕ) : IsClosedImmersion (formalFunctionsFiniteι f y n) :=
    (hsheaf n).1
  have he' (n : ℕ) : ∃ e : formalModuleQuotient J (n + 1) F' ≅
      (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F),
      formalModuleQuotientπ J (n + 1) F' ≫ e.hom = formalFunctionsFiniteFMap f y F n :=
    (hsheaf n).2
  choose e he using he'
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hqc : F.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  have hqc' (n : ℕ) :
      ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F).IsQuasicoherent := by
    let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (formalFibreι f y n))).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction (formalFibreι f y n))
    exact (SheafOfModules.isQuasicoherent (formalFibre f y n).ringCatSheaf).prop_of_iso
      (t.app F).symm (by infer_instance)
  have hiso (n : ℕ) : IsIso (Scheme.Modules.moduleCohomologyFMap
      (formalFunctionsFiniteι f y n) (e n).hom p) := by
    have : IsClosedImmersion (formalFunctionsFiniteι f y n) := hc n
    have := hqc' n
    have hedge := (Scheme.Modules.affine_morphism_cohomology_edge
      (formalFunctionsFiniteι f y n)
      ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)).2 p
    have := hedge.1
    have hn := Scheme.Modules.moduleCohomologyFMap_source_naturality
      (formalFunctionsFiniteι f y n) (e n).hom (𝟙 _) p
    set_option backward.isDefEq.respectTransparency false in
      rw [Category.comp_id (e n).hom] at hn
    rw [← hn]
    change IsIso (_ ≫ Scheme.Modules.moduleCohomologyEdgeMap _ _ p)
    infer_instance
  have hL (n : ℕ) : ∃ L : S.obj (op n) ⟶ T.obj (op n), IsIso L ∧
      ∀ x, L x = (Scheme.Modules.moduleCohomologyFMap
        (formalFunctionsFiniteι f y n) (e n).hom p).hom x := by
    obtain ⟨L, hL⟩ := (Scheme.Modules.moduleCohomologyFMap_basic_properties
      (formalFunctionsFiniteι f y n) (G := formalModuleQuotient J (n + 1) F')
      (F := (Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) (e n).hom p).1
    have : IsIso ((forget₂ _ AddCommGrpCat).map L) := by
      rw [hL]
      exact hiso n
    have : IsIso L := isIso_of_reflects_iso L (forget₂ _ AddCommGrpCat)
    let a := ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    let j := (formalFunctionsFiniteι f y n).appTop.hom
    let c := (formalFibreScalarMap f y n).comp
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom
    let r := algebraMap (Y.presheaf.stalk y)
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    have hca : c.comp r = j.comp a := by
      ext z
      exact (finite_scalar f y n z).symm
    let M := (RingedSpace.moduleCohomology (formalFibre f y n).toRingedSpace p).obj
      ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)
    let i₁ := ModuleCat.restrictScalarsComp'App a j (c.comp r) hca M
    let i₂ := ModuleCat.restrictScalarsComp'App r c (c.comp r) rfl M
    have : IsIso ((ModuleCat.restrictScalars a).map L) := by
      set_option backward.isDefEq.respectTransparency false in infer_instance
    have : IsIso i₁.inv := inferInstance
    have : IsIso i₂.hom := inferInstance
    refine ⟨(ModuleCat.restrictScalars a).map L ≫ i₁.inv ≫ i₂.hom, ?_, ?_⟩
    · set_option backward.isDefEq.respectTransparency false in infer_instance
    · intro x
      change L.hom x = _
      exact congrArg (fun k ↦ k.hom x) hL
  choose b hbi hb using hL
  have ht := formalFunctions_finite_quotient_transition f F y p (fun n ↦ (e n).hom) he
  have hn (n : ℕ) : S.map (homOfLE (Nat.le_succ n)).op ≫ b n =
      b (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (b n) ((S.map (homOfLE (Nat.le_succ n)).op) x) =
      (T.map (homOfLE (Nat.le_succ n)).op) ((b (n + 1)) x)
    exact (hb n _).trans ((ht n x).trans
      (congrArg (fun z : T.obj (op (n + 1)) ↦
        (T.map (homOfLE (Nat.le_succ n)).op) z) (hb (n + 1) x)).symm)
  let β : S ⟶ T := NatTrans.ofOpSequence b hn
  have hβ (n : ℕᵒᵖ) : IsIso (β.app n) := hbi n.unop
  have : IsIso β := (NatTrans.isIso_iff_isIso_app β).mpr hβ
  refine ⟨asIso β, ?_⟩
  intro n z
  change (b n) ((C.map (formalModuleQuotientπ J (n + 1) F')) z) = _
  rw [hb n ((C.map (formalModuleQuotientπ J (n + 1) F')) z)]
  have hq := Scheme.Modules.moduleCohomologyFMap_source_naturality
    (formalFunctionsFiniteι f y n) (formalModuleQuotientπ J (n + 1) F') (e n).hom p
  set_option backward.isDefEq.respectTransparency false in rw [he n] at hq
  exact congrArg (fun k ↦ k.hom z) hq
end AlgebraicGeometry
