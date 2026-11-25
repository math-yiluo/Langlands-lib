/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechDegreewiseProjection
public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Locally linear second-sorting maps

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.2.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The first-repeat sum before pushforward and extension.
Source: Stacks 01FM, equation 20.23.6.2.
(blueprint: lem-pc-ordered-cech-second-sorting-degreewise). -/
noncomputable def orderedCechSecondSortingValue {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (p : ℕ) (B : X'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
    (s : Γ(D.X (p + 1), B)) : Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
    if cechStableSort (fun l ↦ (y l).down) σ ∧
        cechFirstRepeat (fun l ↦ (y (σ l)).down) a then
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ a.val) •
        M.presheaf.map (prod.map
          (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (cechJunction σ σ a l)) (𝟙 _)).op
          (orderedCechNaturalCoordinate M W₀ D e (p + 1) B
            (y ∘ cechJunction σ σ a) s)
    else 0

set_option backward.isDefEq.respectTransparency false in
/-- The explicit second-sorting formula lifts to locally linear module-sheaf maps.
Source: Stacks 01FM, equation 20.23.6.2.
(blueprint: lem-pc-ordered-cech-second-sorting-degreewise).

Proof: Project through e in degree p+1 to every duplicated sorted tuple, restrict
along its product map, multiply by the permutation sign and the first-repeat sign,
and sum. Assemble the tuple outputs by the product universal property, then compose
with e inverse in degree p. Naturality follows from functoriality of restriction
and uniqueness of maps between opens. For local linearity, apply e and each tuple
projection. Use hlinear on the input coordinates and semilinearity of restriction;
the two scalar restrictions agree because the category of opens is thin. Integer
multiples commute with local scalars and finite sums preserve linearity. Coordinate
injectivity proves local linearity of the assembled natural transformation, which
PresheafOfModules.homMk lifts to module sheaves. No differential hypothesis is used.
An empty index family has no tuples, and degree zero has no first-repeat term;
the same construction is the zero map in these cases. -/
theorem orderedCech_secondSorting_degreewise_exists {X' : Scheme.{u}}
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
    : ∃ Q : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p,
      ∀ (p : ℕ) (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y ((Q p).app B s) =
          orderedCechSecondSortingValue M W₀ D e p B y s := by
  classical
  have construction (p : ℕ) : ∃ q : D.X (p + 1) ⟶ D.X p,
      ∀ (B : X'.Opens) (s : Γ(D.X (p + 1), B)) (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y (q.app B s) =
          orderedCechSecondSortingValue M W₀ D e p B y s := by
    let F (n : ℕ) := fun y : Fin (n + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W₀ (y l)))
    let R (y : Fin (p + 1) → ULift.{u} (Fin r))
        (σ : Equiv.Perm (Fin (p + 1))) (a : Fin (p + 1)) :
        F (p + 1) (y ∘ cechJunction σ σ a) ⟶ F p y :=
      { app := fun B ↦ M.presheafModuleCat.map
          (prod.map (Pi.lift fun l ↦
            Pi.π (fun k ↦ W₀ (y k)) (cechJunction σ σ a l)) (𝟙 B.unop)).op
        naturality := by
          intro B C i
          change M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _ =
            M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _
          rw [← M.presheafModuleCat.map_comp, ← M.presheafModuleCat.map_comp]
          congr 1 }
    let c : (D.X (p + 1)).presheafModuleCat ⟶ ∏ᶜ F p :=
      Pi.lift fun y ↦ ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
        if cechStableSort (fun l ↦ (y l).down) σ ∧
            cechFirstRepeat (fun l ↦ (y (σ l)).down) a then
          ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ a.val) •
            ((e (p + 1)).hom ≫ Pi.π (F (p + 1)) (y ∘ cechJunction σ σ a) ≫ R y σ a)
        else 0
    let φ : (D.X (p + 1)).presheafModuleCat ⟶ (D.X p).presheafModuleCat :=
      c ≫ (e p).inv
    have hφ (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)) :
        orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s) =
          orderedCechSecondSortingValue M W₀ D e p B y s := by
      change (((c ≫ (e p).inv) ≫ (e p).hom ≫ Pi.π (F p) y).app (op B)) s = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, c, Pi.lift_comp_π]
      simp only [NatTrans.app_sum, orderedCechSecondSortingValue]
      simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro a _
      split_ifs
      · simp only [NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply,
          NatTrans.comp_app, ConcreteCategory.comp_apply]
        rfl
      · rfl
    let ψ : (D.X (p + 1)).presheaf ⟶ (D.X p).presheaf :=
      Functor.whiskerRight φ (forget₂ (ModuleCat Γ(X', ⊤)) AddCommGrpCat)
    have hψ : ∀ (B : X'.Opens) (a : Γ(X', B)) (s : Γ(D.X (p + 1), B)),
        ψ.app (op B) (a • s) = a • ψ.app (op B) s := by
      intro B a s
      have hinj (x z : Γ(D.X p, B))
          (hxz : ∀ y, orderedCechNaturalCoordinate M W₀ D e p B y x =
            orderedCechNaturalCoordinate M W₀ D e p B y z) : x = z := by
        apply (ConcreteCategory.bijective_of_isIso ((e p).hom.app (op B))).injective
        apply Concrete.isLimit_ext _
          (isLimitOfPreserves ((evaluation _ _).obj (op B))
            (limit.isLimit (Discrete.functor (F p))))
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
      change orderedCechSecondSortingValue M W₀ D e p B y (a • s) =
        X'.presheaf.map prod.snd.op a •
          orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s)
      rw [hφ]
      unfold orderedCechSecondSortingValue
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs
      · rw [show orderedCechNaturalCoordinate M W₀ D e (p + 1) B
            (y ∘ cechJunction σ σ b) (a • s) =
              X'.presheaf.map prod.snd.op a • orderedCechNaturalCoordinate
                M W₀ D e (p + 1) B (y ∘ cechJunction σ σ b) s from
          hlinear (p + 1) (y ∘ cechJunction σ σ b) B a s]
        rw [map_smul, smul_comm]
        congr 1
        change (X'.presheaf.map prod.snd.op ≫
          X'.presheaf.map (prod.map (Pi.lift fun l ↦
            Pi.π (fun k ↦ W₀ (y k)) (cechJunction σ σ b l)) (𝟙 B)).op) a = _
        rw [← X'.presheaf.map_comp]
        congr 2
      · exact (smul_zero _).symm
    refine ⟨⟨PresheafOfModules.homMk ψ (fun B ↦ hψ B.unop)⟩, ?_⟩
    exact hφ
  choose Q hQ using construction
  exact ⟨Q, hQ⟩

end AlgebraicGeometry.Scheme.Modules
