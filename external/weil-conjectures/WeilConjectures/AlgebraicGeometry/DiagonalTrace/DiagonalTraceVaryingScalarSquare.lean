/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenTensorCoordinates
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation

/-! # Scalar restriction and direct image of strict finite systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v c w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local implicit_reducible] AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  Padic.coefficientExtensionIntegers
attribute [local irreducible] WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
open WeilConjectures AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.SpTowerClasses

private def residueLinearEquiv (l : ℕ) [Fact l.Prime] (n : ℕ)
    (M N : ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l]))
    (e : M ≃+ N)
    (hM : ∀ (z : ULift.{u + 1} ℤ_[l]) (x : M),
      z • x = ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x)
    (hN : ∀ (z : ULift.{u + 1} ℤ_[l]) (x : N),
      z • x = ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x) :
    M ≃ₗ[ULift.{u + 1} ℤ_[l]] N :=
  { e with
    map_smul' := by
      intro z x
      change e (z • x) = z • e x
      rw [hM, hN, map_nsmul] }

private def addSectionEquiv {C : Type c} [Category.{w} C]
    {J : GrothendieckTopology C} {M N : Sheaf J AddCommGrpCat.{v}}
    (e : M ≅ N) (U : Cᵒᵖ) : M.obj.obj U ≃+ N.obj.obj U where
  toFun := e.hom.hom.app U
  invFun := e.inv.hom.app U
  left_inv x := congrArg (fun a : M ⟶ M ↦ a.hom.app U x) e.hom_inv_id
  right_inv x := congrArg (fun a : N ⟶ N ↦ a.hom.app U x) e.inv_hom_id
  map_add' x y := map_add (e.hom.hom.app U).hom x y

private def liftResidueIso (l : ℕ) [Fact l.Prime] (n : ℕ) (T : AlgebraicGeometry.Scheme.{u})
    {C : Type c} [Category.{w} C] (F G : C ⥤ DiagonalMod l T)
    (e : F ⋙ diagonalForget l T ≅ G ⋙ diagonalForget l T)
    (hF : ∀ (M : C) (U : T.ProEtᵒᵖ) (z : ULift.{u + 1} ℤ_[l])
      (x : (F.obj M).obj.obj U), z • x =
        ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x)
    (hG : ∀ (M : C) (U : T.ProEtᵒᵖ) (z : ULift.{u + 1} ℤ_[l])
      (x : (G.obj M).obj.obj U), z • x =
        ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x) : F ≅ G := by
  let q := fun M U ↦ residueLinearEquiv l n ((F.obj M).obj.obj U)
    ((G.obj M).obj.obj U) (addSectionEquiv (e.app M) U) (hF M U) (hG M U)
  refine NatIso.ofComponents (fun M ↦
    { hom := { hom :=
        { app := fun U ↦ (q M U).toModuleIso.hom
          naturality := ?_ } }
      inv := { hom :=
        { app := fun U ↦ (q M U).toModuleIso.inv
          naturality := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_
  · intro U V a
    ext x
    exact congrArg (fun t ↦ t.hom x) ((e.hom.app M).hom.naturality a)
  · intro U V a
    ext x
    exact congrArg (fun t ↦ t.hom x) ((e.inv.app M).hom.naturality a)
  · ext U x
    exact congrArg (fun t ↦ t.hom.app U x) (e.app M).hom_inv_id
  · ext U x
    exact congrArg (fun t ↦ t.hom.app U x) (e.app M).inv_hom_id
  · intro M N a
    ext U x
    exact congrArg (fun t ↦ t.hom.app U x) (e.hom.naturality a)

private theorem liftResidueIso_hom_apply (l : ℕ) [Fact l.Prime] (n : ℕ)
    (T : AlgebraicGeometry.Scheme.{u}) {C : Type c} [Category.{w} C]
    (F G : C ⥤ DiagonalMod l T)
    (e : F ⋙ diagonalForget l T ≅ G ⋙ diagonalForget l T)
    (hF : ∀ (M : C) (U : T.ProEtᵒᵖ) (z : ULift.{u + 1} ℤ_[l])
      (x : (F.obj M).obj.obj U), z • x =
        ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x)
    (hG : ∀ (M : C) (U : T.ProEtᵒᵖ) (z : ULift.{u + 1} ℤ_[l])
      (x : (G.obj M).obj.obj U), z • x =
        ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x)
    (M : C) (U : T.ProEtᵒᵖ) (x : (F.obj M).obj.obj U) :
    ((liftResidueIso l n T F G e hF hG).hom.app M).hom.app U x =
      (e.hom.app M).hom.app U x := rfl

private theorem transport_square
    {A B C D A' B' C' D' : AddCommGrpCat.{v}}
    (hA : A = A') (hB : B = B') (hC : C = C') (hD : D = D')
    (s : A ⟶ B) (t : A' ⟶ B') (u : C ⟶ D) (v : C' ⟶ D')
    (e : A' ⟶ C') (f : B' ⟶ D')
    (hs : HEq s.hom t.hom) (hu : HEq u.hom v.hom) (ht : t ≫ f = e ≫ v) :
    s ≫ eqToHom hB ≫ f ≫ eqToHom hD.symm =
      eqToHom hA ≫ e ≫ eqToHom hC.symm ≫ u := by
  subst A'
  subst B'
  subst C'
  subst D'
  have hs' : s = t := AddCommGrpCat.hom_ext (eq_of_heq hs)
  have hu' : u = v := AddCommGrpCat.hom_ext (eq_of_heq hu)
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, hs', hu'] using ht

private theorem eqToHom_heq {A B : AddCommGrpCat.{v}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl

namespace AlgebraicGeometry.ProEtale.DiagonalTrace
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private theorem transport_push_sections {X S : Scheme.{u}} {f : X ⟶ S}
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (G : SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' ⥤ SpTowerShriek.S l E S)
    (hG : HEq g.push G)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology S) (SpTowerShriek.B l E S n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (B' n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology S) (SpTowerShriek.B l E S n), L ⊣ P)
    (hq : HEq q
      (⟨Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
        Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology S) (SpTowerShriek.B l E S n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology S) (SpTowerShriek.B l E S n), L ⊣ P))
    (cG : G ⋙ SpTowerShriek.ev l E S n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) B' τ' n ⋙ q.2.1)
    (hcG : HEq (g.ordinaryPushEvaluation n) cG)
    (h : ∀ (M : SemilinearSections.Systems.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) B' τ') (U : S.ProEtᵒᵖ)
        (x : ((SpTowerShriek.ev l E S n).obj (G.obj M)).val.obj U),
      HEq ((cG.hom.app M).val.app U x) x) :
    ∀ (M : SpTowerShriek.S l E X) (U : S.ProEtᵒᵖ)
      (x : ((SpTowerShriek.ev l E S n).obj (g.push.obj M)).val.obj U),
      HEq (((g.ordinaryPushEvaluation n).hom.app M).val.app U x) x := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hG
  cases eq_of_heq hq
  cases eq_of_heq hcG
  exact h

private theorem push_sections {X S : Scheme.{u}} {f : X ⟶ S}
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (M : SpTowerShriek.S l E X) (U : S.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E S n).obj (g.push.obj M)).val.obj U) :
    HEq (((g.ordinaryPushEvaluation n).hom.app M).val.app U x) x := by
  exact transport_push_sections l E b g n g.generic.coefficients
    g.generic.coefficientTransition g.coefficients g.transitions
    g.generic.push g.push_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n) (g.generic.ordinaryPushEvaluation n)
    (g.ordinaryPushEvaluation_eq n) (g.generic.ordinaryPushEvaluation_sections n) M U x

end AlgebraicGeometry.ProEtale.DiagonalTrace

private def restrictedAddHom {C : Type c} [Category.{w} C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    {M : SemilinearSections.Mod.{c, w, v} J R}
    {N : SemilinearSections.Mod.{c, w, v} J S}
    (a : M ⟶ (SemilinearSections.res.{c, w, v} φ).obj N) (U : Cᵒᵖ) :
    AddCommGrpCat.of (M.val.obj U) ⟶ AddCommGrpCat.of (N.val.obj U) :=
  AddCommGrpCat.ofHom (a.val.app U).hom.toAddMonoidHom

private theorem restrictedAddHom_heq {C : Type c} [Category.{w} C]
    [EssentiallySmall.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    {M : SemilinearSections.Mod.{c, w, v} J R}
    {N : SemilinearSections.Mod.{c, w, v} J S}
    (a : M ⟶ (SemilinearSections.res.{c, w, v} φ).obj N) (U : Cᵒᵖ) :
    HEq (restrictedAddHom φ a U).hom (a.val.app U).hom.toAddMonoidHom := by rfl

private theorem transition_addHom {C : Type c} [Category.{w} C]
    [EssentiallySmall.{v} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{v}) (τ : ∀ k, B (k + 1) ⟶ B k)
    (M : SemilinearSections.Systems.{c, w, v} J B τ) {m n : ℕ} (h : n ≤ m)
    (U : Cᵒᵖ) :
    HEq ((((SemilinearSections.transition.{c, w, v} J B τ h).app M).val.app U).hom.toAddMonoidHom)
      ((M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom.toAddMonoidHom) := by
  apply heq_of_eq
  ext x
  unfold SemilinearSections.transition
  exact congrFun (eq_of_heq
    ((SemilinearSections.transition_exists.{c, w, v} J B τ h).exists.choose_spec M U)) x

namespace AlgebraicGeometry.ProEtale.DiagonalTrace
private def pushAddHom (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) {M : Scheme.proEtaleRingModules S (Scheme.proEtaleConstantRing S A)}
    {N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    (a : M ⟶ (Scheme.proEtaleConstantRingPushforward A f).obj N) (U : S.ProEtᵒᵖ) :
    AddCommGrpCat.of (M.val.obj U) ⟶ AddCommGrpCat.of (N.val.obj (chart f U)) :=
  AddCommGrpCat.ofHom (a.val.app U).hom.toAddMonoidHom

variable (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
  (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
  (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
  (rS : Restriction l (ULift.{u} (Padic l)) S)
  (rX : Restriction l (ULift.{u} (Padic l)) X)

private def restrictionUnderlying (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) :
    r.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n) ⋙
        diagonalForget l T ≅
      SpTowerShriek.ev l (ULift.{u} (Padic l)) T n ⋙
        finiteForget l (ULift.{u} (Padic l)) T n := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ eqToIso (r.underlying M n U)) ?_)) ?_
  · intro U V a
    apply transport_addHom (r.underlying M n U) (r.underlying M n V)
    exact r.restrictions M n a
  · intro M N a
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply transport_addHom (r.underlying M n U) (r.underlying N n U)
    exact r.morphisms a n U

private def directImageUnderlying (n : ℕ) :
    Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l (ULift.{u} (Padic l)) n) f ⋙
        finiteForget l (ULift.{u} (Padic l)) S n ≅
      finiteForget l (ULift.{u} (Padic l)) X n ⋙ lowerStar AddCommGrpCat.{u + 1} f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def levelUnderlying (n : ℕ) :
    g.push ⋙ rS.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n) ⋙
        diagonalForget l S ≅
      rX.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⋙ diagonalForget l S :=
  Functor.isoWhiskerLeft g.push (restrictionUnderlying l S rS n) ≪≫
    Functor.isoWhiskerRight (g.ordinaryPushEvaluation n)
      (finiteForget l (ULift.{u} (Padic l)) S n) ≪≫
    Functor.isoWhiskerLeft (SpTowerShriek.ev l (ULift.{u} (Padic l)) X n)
      (directImageUnderlying l f n) ≪≫
    Functor.isoWhiskerRight (restrictionUnderlying l X rX n).symm
      (lowerStar AddCommGrpCat.{u + 1} f)

private def levelIso (n : ℕ) :
    g.push ⋙ rS.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n) ≅
      rX.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f :=
  liftResidueIso l n S _ _ (levelUnderlying l f b g rS rX n)
    (fun M U ↦ rS.scalars (g.push.obj M) n U)
    (fun M U ↦ rX.scalars M n (chart f U))

private theorem levelUnderlying_horizontal
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) {m n : ℕ} (h : n ≤ m) :
    (diagonalForget l S).map ((rS.F.obj (g.push.obj M)).map (homOfLE h).op) ≫
        (levelUnderlying l f b g rS rX n).hom.app M =
      (levelUnderlying l f b g rS rX m).hom.app M ≫
        (diagonalForget l S).map
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).map
            ((rX.F.obj M).map (homOfLE h).op)) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  let s := AddCommGrpCat.ofHom
    ((((rS.F.obj (g.push.obj M)).map (homOfLE h).op).hom.app U).hom.toAddMonoidHom)
  let φS := SemilinearSections.coefficientMap.{u + 1, u, u + 1}
    (Scheme.ProEt.topology S) (SpTowerShriek.B l (ULift.{u} (Padic l)) S)
    (SpTowerShriek.tau l (ULift.{u} (Padic l)) S) h
  let t := restrictedAddHom φS
    ((SpTowerShriek.horizontal l (ULift.{u} (Padic l)) S h).app (g.push.obj M)) U
  let u := AddCommGrpCat.ofHom
    ((((rX.F.obj M).map (homOfLE h).op).hom.app (chart f U)).hom.toAddMonoidHom)
  let φX := SemilinearSections.coefficientMap.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l (ULift.{u} (Padic l)) X)
    (SpTowerShriek.tau l (ULift.{u} (Padic l)) X) h
  let v := restrictedAddHom φX
    ((SpTowerShriek.horizontal l (ULift.{u} (Padic l)) X h).app M) (chart f U)
  let e := fun k ↦ pushAddHom (SpTowerShriek.R l (ULift.{u} (Padic l)) k) f
    ((g.ordinaryPushEvaluation k).hom.app M) U
  have ht : t ≫ e n = e m ≫ v := by
    ext x
    exact SpTowerShriek.push_horizontal l (ULift.{u} (Padic l)) f b g M h U x
  change s ≫ (eqToHom (rS.underlying (g.push.obj M) n U) ≫ e n ≫
      eqToHom (rX.underlying M n (chart f U)).symm) =
    (eqToHom (rS.underlying (g.push.obj M) m U) ≫ e m ≫
      eqToHom (rX.underlying M m (chart f U)).symm) ≫ u
  simpa only [Category.assoc] using transport_square
    (rS.underlying (g.push.obj M) m U) (rS.underlying (g.push.obj M) n U)
    (rX.underlying M m (chart f U)) (rX.underlying M n (chart f U))
    s t u v (e m) (e n)
    ((rS.transitions (g.push.obj M) h U).trans
      ((restrictedAddHom_heq φS
        ((SpTowerShriek.horizontal l (ULift.{u} (Padic l)) S h).app (g.push.obj M)) U).trans
        (transition_addHom (Scheme.ProEt.topology S)
          (SpTowerShriek.B l (ULift.{u} (Padic l)) S)
          (SpTowerShriek.tau l (ULift.{u} (Padic l)) S) (g.push.obj M) h U)).symm)
    ((rX.transitions M h (chart f U)).trans
      ((restrictedAddHom_heq φX
        ((SpTowerShriek.horizontal l (ULift.{u} (Padic l)) X h).app M) (chart f U)).trans
        (transition_addHom (Scheme.ProEt.topology X)
          (SpTowerShriek.B l (ULift.{u} (Padic l)) X)
          (SpTowerShriek.tau l (ULift.{u} (Padic l)) X) M h (chart f U))).symm) ht

private theorem levelIso_forget_hom (n : ℕ)
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) :
    (diagonalForget l S).map ((levelIso l f b g rS rX n).hom.app M) =
      (levelUnderlying l f b g rS rX n).hom.app M := by
  ext U x
  exact liftResidueIso_hom_apply l n S
    (g.push ⋙ rS.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n))
    (rX.F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DiagonalMod l X)).obj (op n) ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (levelUnderlying l f b g rS rX n)
    (fun M U ↦ rS.scalars (g.push.obj M) n U)
    (fun M U ↦ rX.scalars M n (chart f U)) M U x

private theorem levelIso_horizontal
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) {m n : ℕ} (h : n ≤ m) :
    (rS.F.obj (g.push.obj M)).map (homOfLE h).op ≫
        (levelIso l f b g rS rX n).hom.app M =
      (levelIso l f b g rS rX m).hom.app M ≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).map
          ((rX.F.obj M).map (homOfLE h).op) := by
  have : (diagonalForget l S).Faithful := by
    unfold diagonalForget
    infer_instance
  apply (diagonalForget l S).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    levelIso_forget_hom, levelIso_forget_hom]
  exact levelUnderlying_horizontal l f b g rS rX M h

private theorem levelIso_sections
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U) :
    HEq (((levelIso l f b g rS rX n).hom.app M).hom.app U x) x := by
  have he := congrArg (fun a ↦ a.hom.app U x)
    (levelIso_forget_hom l f b g rS rX n M)
  apply he.heq.trans
  change HEq ((eqToHom (rX.underlying M n (chart f U)).symm)
    (((g.ordinaryPushEvaluation n).hom.app M).val.app U
      ((eqToHom (rS.underlying (g.push.obj M) n U)) x))) x
  exact (eqToHom_heq (rX.underlying M n (chart f U)).symm _).trans
    ((push_sections l (ULift.{u} (Padic l)) b g n M U _).trans
      (eqToHom_heq (rS.underlying (g.push.obj M) n U) x))

/-- The varying direct-image square for any section-preserving residue restrictions.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
ordinary finite-coefficient direct-image comparison before right derivation.
(blueprint: lem-sfb-diagonal-trace-varying-scalar-square).

Proof: at level n, g.ordinaryPushEvaluation identifies the underlying sheaf with
evaluation on the pulled-back pro-etale chart. Its normalization is the identity
on sections, inherited from g.generic.ordinaryPushEvaluation_sections via the
specified coordinate equalities. The underlying fields of rS and rX identify the
additive groups on both sides with those same sections. Their scalar equations
make z act by the same natural-number multiple, the representative of its residue
modulo l^(n+1). Thus the normalized additive identity is Z_l-linear, with inverse
the same identity. Its naturality in the chart and in a module follows from the
restriction and morphism fields of rS and rX and naturality of ordinary evaluation.
For horizontal arrows apply g.ordinaryUnitTransition to the direct image of a
system and postcompose with the evaluated system counit. Ordinary unit evaluation
and the adjunction triangle identities identify its finite transpose with push
evaluation. Naturality of the counit and of finite transposition then identifies
the horizontal section maps.
The transitions fields of rS and rX therefore give horizontal naturality.
These equations assemble the level isomorphisms into a natural isomorphism of
strict systems, with the asserted identity on every section. No completed
coefficients or coefficient cones occur. The argument also covers identity maps,
empty sites, and level zero (the first positive quotient). -/
@[no_expose] def diagonalTraceVaryingScalarSquare (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X) :
    g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ (levelIso l f b g rS rX n.unop).app M) (by
      intro m n a
      have ha : a = (homOfLE (leOfHom a.unop)).op := Subsingleton.elim _ _
      cases ha
      exact levelIso_horizontal l f b g rS rX M (leOfHom a.unop))) (by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (levelIso l f b g rS rX n.unop).hom.naturality a)

/-- The varying scalar square is the identity on sections. -/
theorem diagonalTraceVaryingScalarSquare_hom_app_app_hom_app (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (rS : Restriction l (ULift.{u} (Padic l)) S)
    (rX : Restriction l (ULift.{u} (Padic l)) X)
    (M : Systems X (Arings l (ULift.{u} (Padic l)) X)) (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U) :
    HEq ((((diagonalTraceVaryingScalarSquare l f b g rS rX).hom.app M).app (op n)).hom.app U x)
      x :=
  levelIso_sections l f b g rS rX M n U x

end AlgebraicGeometry.ProEtale.DiagonalTrace
