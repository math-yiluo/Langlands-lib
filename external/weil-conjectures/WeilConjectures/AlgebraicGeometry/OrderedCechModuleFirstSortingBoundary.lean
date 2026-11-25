/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrderedCechModuleProjectionLift
public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import WeilConjectures.AlgebraicGeometry.OrderedCechDegreewiseProjection
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # The first sorting boundary for module Čech cochains

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def firstSortingValue {X' : Scheme.{u}}
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
    ∑ τ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort (fun l ↦ (y l).down) σ ∧ cechPartialSort σ τ a then
        ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
          M.presheaf.map (prod.map
            (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (cechJunction σ τ a l)) (𝟙 _)).op
              (orderedCechNaturalCoordinate M W₀ D e (p + 1) B
                (y ∘ cechJunction σ τ a) s)
      else 0

set_option backward.isDefEq.respectTransparency false in
private theorem firstSorting_exists {X' : Scheme.{u}}
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
          firstSortingValue M W₀ D e p B y s := by
  classical
  have construction (p : ℕ) : ∃ q : D.X (p + 1) ⟶ D.X p,
      ∀ (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y (q.app B s) =
          firstSortingValue M W₀ D e p B y s := by
    let F (n : ℕ) := fun y : Fin (n + 1) → ULift.{u} (Fin r) ↦
      ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat).obj
          (op (∏ᶜ fun l ↦ W₀ (y l)))
    let R (y : Fin (p + 1) → ULift.{u} (Fin r))
        (σ τ : Equiv.Perm (Fin (p + 1))) (a : Fin (p + 1)) :
        F (p + 1) (y ∘ cechJunction σ τ a) ⟶ F p y :=
      { app := fun B ↦ M.presheafModuleCat.map (prod.map
          (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (cechJunction σ τ a l)) (𝟙 B.unop)).op
        naturality := by
          intro B C i
          change M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _ =
            M.presheafModuleCat.map _ ≫ M.presheafModuleCat.map _
          rw [← M.presheafModuleCat.map_comp, ← M.presheafModuleCat.map_comp]
          congr 1 }
    let c : (D.X (p + 1)).presheafModuleCat ⟶ ∏ᶜ F p := Pi.lift fun y ↦
      ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
        ∑ τ : Equiv.Perm (Fin (p + 1)),
          if cechStableSort (fun l ↦ (y l).down) σ ∧ cechPartialSort σ τ a then
            ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
              ((e (p + 1)).hom ≫ Pi.π (F (p + 1)) (y ∘ cechJunction σ τ a) ≫ R y σ τ a)
          else 0
    let φ : (D.X (p + 1)).presheafModuleCat ⟶ (D.X p).presheafModuleCat :=
      c ≫ (e p).inv
    have hφ (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)) :
        orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s) =
          firstSortingValue M W₀ D e p B y s := by
      change (((c ≫ (e p).inv) ≫ (e p).hom ≫ Pi.π (F p) y).app (op B)) s = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, c, Pi.lift_comp_π]
      simp only [NatTrans.app_sum, firstSortingValue]
      simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs
      · rfl
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
      change firstSortingValue M W₀ D e p B y (a • s) =
        X'.presheaf.map prod.snd.op a •
          orderedCechNaturalCoordinate M W₀ D e p B y (φ.app (op B) s)
      rw [hφ]
      unfold firstSortingValue
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs
      · rw [show orderedCechNaturalCoordinate M W₀ D e (p + 1) B
            (y ∘ cechJunction σ τ b) (a • s) =
              X'.presheaf.map prod.snd.op a • orderedCechNaturalCoordinate
                M W₀ D e (p + 1) B (y ∘ cechJunction σ τ b) s from
          hlinear (p + 1) (y ∘ cechJunction σ τ b) B a s]
        rw [map_smul, smul_comm]
        congr 1
        change (X'.presheaf.map prod.snd.op ≫ X'.presheaf.map _ ) a = _
        rw [← X'.presheaf.map_comp]
        congr 2
      · exact (smul_zero _).symm
    refine ⟨⟨PresheafOfModules.homMk ψ (fun B ↦ hψ B.unop)⟩, ?_⟩
    exact hφ
  choose Q hQ using construction
  exact ⟨Q, hQ⟩

/-- The intersection model on the base open B.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-degreewise-projection-differential). -/
private noncomputable def naturalCechSectionSite {X : Scheme.{u}} {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) :
    SiteCechComplex (fun i : Fin r ↦ W ⟨i⟩ ⊓ B)
      (fun i ↦ homOfLE (le_top : W ⟨i⟩ ⊓ B ≤ ⊤)) where
  W p t := ⨅ k : Fin (p + 1), W ⟨t k⟩ ⊓ B
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k; exact Subsingleton.elim _ _
    · intro b _; exact Subsingleton.elim _ _
  W_zero := by intro t; simp
  pr_zero := by intro t; exact Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

/-- Restriction from the chosen product to the intersection model.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-degreewise-projection-differential). -/
private noncomputable def naturalCechSectionMap {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    (naturalCechSectionSite W B).W p t ⟶ (∏ᶜ fun k ↦ W ⟨t k⟩) ⨯ B :=
  prod.lift (Pi.lift fun k ↦ homOfLE ((iInf_le _ k).trans inf_le_left))
    (homOfLE ((iInf_le _ 0).trans inf_le_right))

private theorem naturalCechSectionMap_isIso {X : Scheme.{u}} {r p : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (B : X.Opens) (t : Fin (p + 1) → Fin r) :
    IsIso (naturalCechSectionMap W B t) := by
  apply (PartialOrder.isIso_iff_eq _).mpr
  apply le_antisymm (naturalCechSectionMap W B t).le
  apply le_iInf
  intro k
  exact le_inf (prod.fst ≫ Pi.π (fun l ↦ W ⟨t l⟩) k).le prod.snd.le

/-- All tuple coordinates, transported by actual restriction maps.
Source: Stacks 01FJ. (blueprint: lem-pc-ordered-cech-degreewise-projection-differential). -/
private noncomputable def naturalCechSectionCochain {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    (naturalCechSectionSite W B).cochains M.presheaf p :=
  fun t ↦ M.presheaf.map (naturalCechSectionMap W B t).op
    (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t k⟩) s)

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate transport identifies the given differential with the alternating face sum.
Source: Stacks 01FJ, the Čech differential, and 01FK, restriction to ordered tuples.
(blueprint: lem-pc-ordered-cech-degreewise-projection-differential).

Proof: Compose hd with the projection to a full tuple and evaluate at B and s.
The Mathlib Čech differential is the sum of signed coface maps. Its j-th coface,
after projecting to t, first projects to t composed with j.succAbove and then
restricts along the map of chosen products dropping the j-th factor, times the
identity of B. Restrict further along naturalCechSectionMap. The resulting arrow
from the intersection for t to the chosen product for its j-th face equals the
composite through the face intersection, since the category of opens is thin.
Functoriality identifies the corresponding restrictions. Additivity of restriction
moves it through the finite sum and the integer coefficients. This gives exactly
the defining alternating sum for naturalCechSectionSite. For an empty index set
there are no tuples; no nonempty intersection or affine hypothesis is required. -/
private theorem naturalCechSectionCochain_differential {X : Scheme.{u}} (M : X.Modules) {r : ℕ}
    (W : ULift.{u} (Fin r) → X.Opens) (D : CochainComplex X.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).d p (p + 1))
    (p : ℕ) (B : X.Opens) (s : Γ(D.X p, B)) :
    naturalCechSectionCochain M W D e (p + 1) B ((D.d p (p + 1)).app B s) =
      (naturalCechSectionSite W B).differentialValue M.presheaf p
        (naturalCechSectionCochain M W D e p B s) := by
  classical
  funext t
  let F := (prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat
  have h := congrArg
    (fun f ↦ ((f ≫ TopCat.Presheaf.cechComplexFunctorπ W F (p + 1)
      (fun k ↦ ⟨t k⟩)).app (op B)) s) (hd p)
  simp only [Category.assoc] at h
  rw [TopCat.Presheaf.cechComplexFunctor_d_π W F] at h
  change orderedCechNaturalCoordinate M W D e (p + 1) B (fun k ↦ ⟨t k⟩)
    ((D.d p (p + 1)).app B s) = _ at h
  unfold naturalCechSectionCochain
  rw [h]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, NatTrans.app_sum, NatTrans.app_zsmul,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  unfold SiteCechComplex.differentialValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s) =
    (M.presheaf.map _ ≫ M.presheaf.map _)
      (orderedCechNaturalCoordinate M W D e p B (fun k ↦ ⟨t (j.succAbove k)⟩) s)
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private theorem firstSorting_cochain {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (Q : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (hQ : ∀ (p : ℕ) (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y ((Q p).app B s) =
          firstSortingValue M W₀ D e p B y s)
    (p : ℕ) (B : X'.Opens) (s : Γ(D.X (p + 1), B)) :
    naturalCechSectionCochain M W₀ D e p B ((Q p).app B s) =
      cechFirstSortingHom X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ B) M.presheaf
        (naturalCechSectionSite W₀ B) p
          (naturalCechSectionCochain M W₀ D e (p + 1) B s) := by
  classical
  funext t
  unfold naturalCechSectionCochain
  rw [hQ, firstSortingValue, map_sum]
  change _ = ∑ σ : Equiv.Perm (Fin (p + 1)), ∑ a : Fin (p + 1),
    ∑ τ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort t σ ∧ cechPartialSort σ τ a then
        ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
          M.presheaf.map ((naturalCechSectionSite W₀ B).indexMap t
            (cechJunction σ τ a)).op
              (M.presheaf.map (naturalCechSectionMap W₀ B (t ∘ cechJunction σ τ a)).op
                (orderedCechNaturalCoordinate M W₀ D e (p + 1) B
                  (fun k ↦ ⟨t (cechJunction σ τ a k)⟩) s)) else 0
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs
  · rw [map_zsmul]
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W₀ D e (p + 1) B
          (fun k ↦ ⟨t (cechJunction σ τ a k)⟩) s) =
      (M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W₀ D e (p + 1) B
          (fun k ↦ ⟨t (cechJunction σ τ a k)⟩) s)
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
    congr 2
  · exact map_zero _

private noncomputable def firstSortingFamily {X : Scheme.{u}}
    (D : CochainComplex X.Modules ℕ) (Q : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) : D.X i ⟶ D.X j :=
  eqToHom (congrArg D.X h.symm) ≫ Q j

-- Transport through the dependent sectionwise cochain model needs additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
private theorem firstSorting_boundary_cochain {X' : Scheme.{u}}
    (M : X'.Modules) {r : ℕ}
    (W₀ : ULift.{u} (Fin r) → X'.Opens) (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj M.presheafModuleCat)).d p (p + 1))
    (Q : ∀ p : ℕ, D.X (p + 1) ⟶ D.X p)
    (hQ : ∀ (p : ℕ) (B : X'.Opens) (s : Γ(D.X (p + 1), B))
        (y : Fin (p + 1) → ULift.{u} (Fin r)),
        orderedCechNaturalCoordinate M W₀ D e p B y ((Q p).app B s) =
          firstSortingValue M W₀ D e p B y s)
    (p : ℕ) (B : X'.Opens) (s : Γ(D.X p, B)) :
    naturalCechSectionCochain M W₀ D e p B
        (((Homotopy.nullHomotopicMap' (firstSortingFamily D Q)).f p).app B s) =
      naturalCechSectionCochain M W₀ D e p B s -
        cechStableSortingMap X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ B) M.presheaf
          (naturalCechSectionSite W₀ B) p
            (naturalCechSectionCochain M W₀ D e p B s) := by
  classical
  let S := naturalCechSectionSite W₀ B
  have hi := congrArg (fun k ↦ k (naturalCechSectionCochain M W₀ D e p B s))
    (cechFirstSortingIdentity X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ B) M.presheaf S p)
  change _ = naturalCechSectionCochain M W₀ D e p B s -
    cechStableSortingMap X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ B) M.presheaf S p
      (naturalCechSectionCochain M W₀ D e p B s) at hi
  rw [← hi]
  cases p with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 1) (by rfl)
      (by intro l; change ¬ l + 1 = 0; omega)]
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 1) (by rfl)
      (by intro l; change ¬ l + 1 = 0; omega)]
    change naturalCechSectionCochain M W₀ D e 0 B
      ((Q 0).app B ((D.d 0 1).app B s)) =
      cechFirstSortingHom X' _ M.presheaf S 0
        (S.differential M.presheaf 0 (naturalCechSectionCochain M W₀ D e 0 B s))
    rw [firstSorting_cochain M W₀ D e Q hQ,
      naturalCechSectionCochain_differential M W₀ D e hd]
    rfl
  | succ p =>
    rw [Homotopy.nullHomotopicMap'_f (k₂ := p) (k₀ := p + 1 + 1) (by rfl) (by rfl)]
    rw [Homotopy.nullHomotopicMap'_f (k₂ := p) (k₀ := p + 1 + 1) (by rfl) (by rfl)]
    change naturalCechSectionCochain M W₀ D e (p + 1) B
      ((Q (p + 1)).app B ((D.d (p + 1) (p + 1 + 1)).app B s) +
        (D.d p (p + 1)).app B ((Q p).app B s)) = _
    have hadd (x z : Γ(D.X (p + 1), B)) :
        naturalCechSectionCochain M W₀ D e (p + 1) B (x + z) =
          naturalCechSectionCochain M W₀ D e (p + 1) B x +
            naturalCechSectionCochain M W₀ D e (p + 1) B z := by
      funext t
      change M.presheaf.map (naturalCechSectionMap W₀ B t).op
        (orderedCechNaturalCoordinate M W₀ D e (p + 1) B (fun k ↦ ⟨t k⟩) (x + z)) =
        M.presheaf.map (naturalCechSectionMap W₀ B t).op
          (orderedCechNaturalCoordinate M W₀ D e (p + 1) B (fun k ↦ ⟨t k⟩) x) +
        M.presheaf.map (naturalCechSectionMap W₀ B t).op
          (orderedCechNaturalCoordinate M W₀ D e (p + 1) B (fun k ↦ ⟨t k⟩) z)
      simp only [orderedCechNaturalCoordinate, map_add]
    rw [hadd, firstSorting_cochain M W₀ D e Q hQ,
      naturalCechSectionCochain_differential M W₀ D e hd,
      naturalCechSectionCochain_differential M W₀ D e hd,
      firstSorting_cochain M W₀ D e Q hQ]
    simp only [cechFirstSortingFamily, SiteCechComplex.complex, CochainComplex.of_d,
      eqToHom_refl, Category.id_comp]
    rfl

open Classical in
/-- The first sorting operator assembles into module-sheaf maps.
Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-ordered-cech-module-first-sorting-boundary).

Proof: On an open B of X', identify the full cochains of D with sections on the
products of the W₀ using e. Apply the explicit junction sum cechFirstSortingHom:
sum over the stable permutation, the junction position, and the partial sorting permutation, with
coefficient (-1)^a sign(tau).
The intersection arrows are the unique arrows of opens with the prescribed tuple
projections. Transport the output back through e inverse. Every summand is additive.
Naturality of e and functoriality of restriction show naturality in B. For local
linearity, apply hlinear to each input coordinate; the two paths restricting a
scalar to the output intersection agree in the poset of opens. Since e is bijective,
the output coordinates determine a locally linear section map. These maps define
morphisms of module sheaves in adjacent natural degrees. Push them forward along f'
and conjugate by extendXIso in nonnegative degrees; put zero in all other degrees.
Apply cechFirstSortingIdentity on each open, using hd for the transported
differential. The categorical products of opens identify with the intersections in
SiteCechComplex, by their universal properties. The stable-sorting term is exactly
the displayed permutation sum, with prod.map giving the same unique restriction.
The resulting boundary is identity minus stable sorting.
In degree zero the incoming term vanishes in both natural and extended complexes.
For r=0 the products of section groups indexed by tuples are empty, hence zero;
no nonempty or covering assumption is used. Repeated tuples are retained by stable sorting,
including in degrees above r;
the junction formula still applies. -/
theorem orderedCech_module_firstSorting_boundary {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s) :
    let L := ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
      ComplexShape.embeddingUpNat)
    ∃ H : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel j i → (L.X i ⟶ L.X j),
      ∀ (p : ℕ) (B : T'.Opens) (y : Fin (p + 1) → ULift.{u} (Fin r))
        (s : Γ(L.X (p : ℤ), B)),
        orderedCechFullCoordinate f' M W₀ D e p B y
          (((Homotopy.nullHomotopicMap' H).f (p : ℤ)).app B s) =
          orderedCechFullCoordinate f' M W₀ D e p B y s -
          (∑ σ : Equiv.Perm (Fin (p + 1)),
        if cechStableSort (fun l ↦ (y l).down) σ then
          (Equiv.Perm.sign σ : ℤ) •
            M.presheaf.map (prod.map
              (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
                (orderedCechFullCoordinate f' M W₀ D e p B (y ∘ σ) s)
        else 0) := by
  classical
  obtain ⟨Q, hQ⟩ := firstSorting_exists M W₀ D e hlinear
  let q := Homotopy.nullHomotopicMap' (firstSortingFamily D Q)
  let G := Modules.pushforward f'
  let v := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map q
  let h := (G.mapHomotopy (Homotopy.nullHomotopy' (firstSortingFamily D Q))).extend
    ComplexShape.embeddingUpNat
  let H := fun i j (_ : (ComplexShape.up ℤ).Rel j i) ↦ h.hom i j
  have hh : Homotopy.nullHomotopicMap' H =
      HomologicalComplex.extendMap v ComplexShape.embeddingUpNat := by
    apply HomologicalComplex.Hom.ext
    funext i
    have hc := h.comm i
    simp only [Functor.map_zero, HomologicalComplex.extendMap_zero,
      HomologicalComplex.zero_f_apply, add_zero] at hc
    rw [hc]
    have he : (fun i j ↦ @dite _ ((ComplexShape.up ℤ).Rel j i)
        (Classical.propDecidable _) (H i j) fun _ ↦ 0) =
        h.hom := by
      funext i j
      split_ifs with hij
      · rfl
      · exact (h.zero i j hij).symm
    change dNext i _ + prevD i _ = _
    exact congrArg (fun z ↦ dNext i z + prevD i z) he
  refine ⟨H, ?_⟩
  intro p B y s
  rw [hh]
  let E := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extendXIso
    ComplexShape.embeddingUpNat (i := p) rfl
  have hv : E.hom.app B
      (((HomologicalComplex.extendMap v ComplexShape.embeddingUpNat).f (p : ℤ)).app B s) =
      (q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s) := by
    rw [HomologicalComplex.extendMap_f v ComplexShape.embeddingUpNat
      (i := p) (i' := (p : ℤ)) rfl]
    change E.hom.app B (E.inv.app B ((q.f p).app (f' ⁻¹ᵁ B) (E.hom.app B s))) = _
    have hi := congrArg (fun k ↦ (k.app B) ((q.f p).app (f' ⁻¹ᵁ B)
      (E.hom.app B s))) E.inv_hom_id
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
      CategoryTheory.id_apply] using hi
  change orderedCechNaturalCoordinate M W₀ D e p (f' ⁻¹ᵁ B) y
    (E.hom.app B _) = _
  rw [hv]
  let t : Fin (p + 1) → Fin r := fun k ↦ (y k).down
  let A := f' ⁻¹ᵁ B
  have hb := congrFun
    (firstSorting_boundary_cochain M W₀ D e hd Q hQ p A (E.hom.app B s)) t
  have hm : IsIso (naturalCechSectionMap W₀ A t) := naturalCechSectionMap_isIso W₀ A t
  apply (ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (naturalCechSectionMap W₀ A t).op)).injective
  change M.presheaf.map (naturalCechSectionMap W₀ A t).op
      (orderedCechNaturalCoordinate M W₀ D e p A y ((q.f p).app A (E.hom.app B s))) = _
  change M.presheaf.map (naturalCechSectionMap W₀ A t).op
      (orderedCechNaturalCoordinate M W₀ D e p A y ((q.f p).app A (E.hom.app B s))) =
    M.presheaf.map (naturalCechSectionMap W₀ A t).op
      (orderedCechNaturalCoordinate M W₀ D e p A y (E.hom.app B s) -
        ∑ σ : Equiv.Perm (Fin (p + 1)),
          if cechStableSort t σ then
            (Equiv.Perm.sign σ : ℤ) • M.presheaf.map (prod.map
              (Pi.lift fun l ↦ Pi.π (fun k ↦ W₀ (y k)) (σ l)) (𝟙 _)).op
                (orderedCechNaturalCoordinate M W₀ D e p A (y ∘ σ) (E.hom.app B s))
          else 0)
  rw [map_sub, map_sum]
  change naturalCechSectionCochain M W₀ D e p A (q.f p |>.app A <| E.hom.app B s) t = _
  rw [hb]
  change naturalCechSectionCochain M W₀ D e p A (E.hom.app B s) t -
    (cechStableSortingMap X' (fun i : Fin r ↦ W₀ ⟨i⟩ ⊓ A) M.presheaf
      (naturalCechSectionSite W₀ A) p (naturalCechSectionCochain M W₀ D e p A
        (E.hom.app B s))) t = _
  congr 1
  change (∑ σ : Equiv.Perm (Fin (p + 1)),
    if cechStableSort t σ then
      (Equiv.Perm.sign σ : ℤ) • M.presheaf.map
        ((naturalCechSectionSite W₀ A).indexMap t σ).op
          (naturalCechSectionCochain M W₀ D e p A (E.hom.app B s) (t ∘ σ))
    else 0) = _
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs
  · rw [map_zsmul]
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W₀ D e p A (y ∘ σ) (E.hom.app B s)) =
      (M.presheaf.map _ ≫ M.presheaf.map _)
        (orderedCechNaturalCoordinate M W₀ D e p A (y ∘ σ) (E.hom.app B s))
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
    congr 2
  · exact (map_zero _).symm

end AlgebraicGeometry.Scheme.Modules
