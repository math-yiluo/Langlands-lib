/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleCoordinates
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Degreewise signed projection of module Čech cochains

Source: Stacks Project, Tags 01FK and 01FM.
(blueprint: lem-pc-ordered-cech-degreewise-projection)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Full tuple coordinate before pushforward and extension.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-degreewise-projection). -/
noncomputable def orderedCechNaturalCoordinate {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : X'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
    (s : Γ(D.X p, B)) : Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
  ((e p).hom ≫ Pi.π (fun z : Fin (p + 1) → ULift.{u} (Fin r) ↦
    ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
        (op (∏ᶜ fun l ↦ W₀ (z l)))) y).app (op B) s

/-- The signed finite sum in one degree on an open of the source scheme.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-degreewise-projection). -/
noncomputable def orderedCechNaturalProjectionValue {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : X'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
    (s : Γ(D.X p, B)) : Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (p + 1)),
    if h : StrictMono (fun l ↦ (y (σ l)).down) then
      (Equiv.Perm.sign σ : ℤ) •
        M.presheaf.map (homOfLE (le_inf (le_iInf fun l ↦
            (prod.fst ≫ Pi.π (fun k ↦ W₀ (y k)) (σ l)).le) prod.snd.le)).op
          (M.presheaf.map (orderedCechTupleOpenMap W₀ B
            (OrderEmbedding.ofStrictMono _ h)).op
              (orderedCechNaturalCoordinate M W₀ D e p B (fun l ↦ ⟨(y (σ l)).down⟩) s))
    else 0

/-- Coordinate condition for degreewise module maps; no differential condition is imposed.
Source: Stacks 01FK. (blueprint: lem-pc-ordered-cech-degreewise-projection). -/
def IsOrderedCechNaturalProjection {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (Q : ∀ p : ℕ, D.X p ⟶ D.X p) : Prop :=
  ∀ (p : ℕ) (B : X'.Opens) (s : Γ(D.X p, B))
    (y : Fin (p + 1) → ULift.{u} (Fin r)),
    orderedCechNaturalCoordinate M W₀ D e p B y ((Q p).app B s) =
      orderedCechNaturalProjectionValue M W₀ D e p B y s

set_option backward.isDefEq.respectTransparency false in
/-- The finite signed formula assembles into degreewise module-sheaf maps.
Source: Stacks 01FK, signed extension, and 01FM, the termwise map cπ.
(blueprint: lem-pc-ordered-cech-degreewise-projection).

Proof: In degree p project to each sorted tuple using e, restrict to its ordered
intersection, and then restrict back to the full tuple intersection, multiplying
by the sign. Sum over permutations passing the strict-increase filter. These are
additive natural transformations: naturality of e and coefficient restrictions
identifies the two composites for every inclusion of opens. The product universal
property assembles all tuple components; compose with e inverse. To check local
linearity, apply e and every tuple projection. The hypothesis hlinear makes each
input component semilinear over the corresponding projection to B. Semilinearity
of the two restrictions makes each summand semilinear over the full tuple projection
to B, since arrows between opens are unique. Integer multiplication commutes with
this scalar action, and finite sums preserve it. Coordinate injectivity then gives
linearity of the assembled map. Thus PresheafOfModules.homMk and the full forgetful
functor from module sheaves lift this actual natural transformation. No differential
compatibility is needed. If r = 0 the tuple product is empty and D.X p is zero; if
p + 1 > r all summands are zero. Both cases give the zero map. -/
theorem orderedCech_degreewise_projection_exists {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s)
    : ∃ Q : ∀ p : ℕ, D.X p ⟶ D.X p,
      IsOrderedCechNaturalProjection M W₀ D e Q := by
  classical
  have construction (p : ℕ) : ∃ q : D.X p ⟶ D.X p,
      ∀ (B : X'.Opens) (s : Γ(D.X p, B)) (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y (q.app B s) =
          orderedCechNaturalProjectionValue M W₀ D e p B y s := by
    let F := fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W₀ (y l)))
    let R (y : Fin (p + 1) → ULift.{u} (Fin r))
        (σ : Equiv.Perm (Fin (p + 1)))
        (h : StrictMono (fun l ↦ (y (σ l)).down)) :
        F (fun l ↦ ⟨(y (σ l)).down⟩) ⟶ F y :=
      { app := fun B ↦ M.presheafModuleCat.map
          ((homOfLE (le_inf (le_iInf fun l ↦
            (prod.fst ≫ Pi.π (fun k ↦ W₀ (y k)) (σ l)).le) prod.snd.le)) ≫
            orderedCechTupleOpenMap W₀ B.unop (OrderEmbedding.ofStrictMono _ h)).op
        naturality := by
          intro B C i
          change M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _ =
            M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _
          rw [← M.presheafModuleCat.map_comp, ← M.presheafModuleCat.map_comp]
          congr 1 }
    let c : (D.X p).presheafModuleCat ⟶ ∏ᶜ F := Pi.lift fun y ↦ ∑ σ : Equiv.Perm (Fin (p + 1)),
      if h : StrictMono (fun l ↦ (y (σ l)).down) then
        (Equiv.Perm.sign σ : ℤ) •
          ((e p).hom ≫ Pi.π F (fun l ↦ ⟨(y (σ l)).down⟩) ≫ R y σ h)
      else 0
    let φ : (D.X p).presheafModuleCat ⟶ (D.X p).presheafModuleCat :=
      c ≫ (e p).inv
    have hφ (B : X'.Opens) (s : Γ(D.X p, B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)) :
        orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s) =
          orderedCechNaturalProjectionValue M W₀ D e p B y s := by
      change (((c ≫ (e p).inv) ≫ (e p).hom ≫ Pi.π F y).app (op B)) s = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, c, Pi.lift_comp_π]
      simp only [NatTrans.app_sum, orderedCechNaturalProjectionValue]
      simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs with h
      · simp only [NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply,
          NatTrans.comp_app, ConcreteCategory.comp_apply]
        change (Equiv.Perm.sign σ : ℤ) •
          M.presheaf.map (_ ≫ _).op _ = _
        rw [op_comp, M.presheaf.map_comp]
        rfl
      · rfl
    let ψ : (D.X p).presheaf ⟶ (D.X p).presheaf :=
      Functor.whiskerRight φ (forget₂ (ModuleCat Γ(X', ⊤)) AddCommGrpCat)
    have hψ : ∀ (B : X'.Opens) (a : Γ(X', B)) (s : Γ(D.X p, B)),
        ψ.app (op B) (a • s) = a • ψ.app (op B) s := by
      intro B a s
      have hinj (x z : Γ(D.X p, B))
          (hxz : ∀ y, orderedCechNaturalCoordinate M W₀ D e p B y x =
            orderedCechNaturalCoordinate M W₀ D e p B y z) : x = z := by
        apply (ConcreteCategory.bijective_of_isIso ((e p).hom.app (op B))).injective
        apply Concrete.isLimit_ext _
          (isLimitOfPreserves ((evaluation _ _).obj (op B))
            (limit.isLimit (Discrete.functor F)))
        intro y
        exact hxz y.as
      apply hinj
      intro y
      let z : Γ(D.X p, B) := ψ.app (op B) s
      change orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) (a • s)) =
        orderedCechNaturalCoordinate M W₀ D e p B y (a • z)
      rw [hφ]
      rw [show orderedCechNaturalCoordinate M W₀ D e p B y (a • z) =
          X'.presheaf.map prod.snd.op a •
            orderedCechNaturalCoordinate M W₀ D e p B y z from hlinear p y B a z]
      change orderedCechNaturalProjectionValue M W₀ D e p B y (a • s) =
        X'.presheaf.map prod.snd.op a •
          orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s)
      rw [hφ]
      unfold orderedCechNaturalProjectionValue
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs with h
      · rw [show orderedCechNaturalCoordinate M W₀ D e p B
            (fun l ↦ ⟨(y (σ l)).down⟩) (a • s) =
              X'.presheaf.map prod.snd.op a • orderedCechNaturalCoordinate
                M W₀ D e p B (fun l ↦ ⟨(y (σ l)).down⟩) s from
          hlinear p (fun l ↦ ⟨(y (σ l)).down⟩) B a s]
        rw [map_smul, map_smul, smul_comm]
        congr 1
        change (X'.presheaf.map prod.snd.op ≫
          X'.presheaf.map (orderedCechTupleOpenMap W₀ B
            (OrderEmbedding.ofStrictMono _ h)).op ≫
          X'.presheaf.map (homOfLE (le_inf (le_iInf fun l ↦
            (prod.fst ≫ Pi.π (fun k ↦ W₀ (y k)) (σ l)).le) prod.snd.le)).op) a = _
        rw [← X'.presheaf.map_comp, ← X'.presheaf.map_comp]
        congr 2
      · exact (smul_zero _).symm
    refine ⟨⟨PresheafOfModules.homMk ψ (fun B ↦ hψ B.unop)⟩, ?_⟩
    exact hφ
  choose Q hQ using construction
  exact ⟨Q, hQ⟩

end AlgebraicGeometry.Scheme.Modules
