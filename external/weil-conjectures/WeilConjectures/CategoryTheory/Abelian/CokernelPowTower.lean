/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# The tower of reductions of an object modulo the powers of an integer

Let `C` be a preadditive category with cokernels, `A : C` and `ℓ : ℕ`. This file defines the
inverse system `n ↦ A/ℓⁿ = coker(ℓⁿ : A ⟶ A)` (`CategoryTheory.Limits.cokernelPowTower`), with the
reductions `A/ℓⁿ⁺¹ ⟶ A/ℓⁿ` as transition maps, and the cone of projections `A ⟶ A/ℓⁿ`
(`CategoryTheory.Limits.cokernelPowTowerCone`). The object `A` is `ℓ`-adically complete and
separated when this cone is a limit cone.

A cone `c` over a tower whose legs `c.pt ⟶ Fₙ` are cokernels of `ℓⁿ` is isomorphic to
`cokernelPowTowerCone c.pt ℓ` (`CategoryTheory.Limits.cokernelPowTowerConeIsoOfIsColimit`), so
`c` is a limit cone if and only if `c.pt` is `ℓ`-adically complete and separated
(`CategoryTheory.Limits.isLimitCokernelPowTowerConeOfIsColimit`,
`CategoryTheory.Limits.isLimitOfIsColimitCokernelCofork`). In particular, `ℓ`-adic completeness
is invariant under isomorphisms (`CategoryTheory.Limits.isLimitCokernelPowTowerConeOfIso`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (A : C) (ℓ : ℕ)

lemma pow_succ_smul_comp_cokernel_π (n : ℕ) :
    (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 A) ≫ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) = 0 := by
  rw [pow_succ', Nat.cast_mul, mul_smul, Preadditive.zsmul_comp, cokernel.condition, smul_zero]

/-- The reduction `A/ℓⁿ⁺¹ ⟶ A/ℓⁿ`. -/
noncomputable def cokernelPowTransition (n : ℕ) :
    cokernel (((ℓ ^ (n + 1) : ℕ) : ℤ) • 𝟙 A) ⟶ cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  cokernel.desc _ (cokernel.π _) (pow_succ_smul_comp_cokernel_π A ℓ n)

@[reassoc (attr := simp)]
lemma cokernel_π_cokernelPowTransition (n : ℕ) :
    cokernel.π _ ≫ cokernelPowTransition A ℓ n = cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  cokernel.π_desc _ _ _

/-- The inverse system `n ↦ A/ℓⁿ` of the reductions of `A` modulo the powers of `ℓ`. -/
noncomputable def cokernelPowTower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A)) (cokernelPowTransition A ℓ)

lemma cokernelPowTower_obj (n : ℕ) :
    (cokernelPowTower A ℓ).obj (Opposite.op n) = cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  rfl


@[simp]
lemma cokernelPowTower_map_succ (n : ℕ) :
    (cokernelPowTower A ℓ).map (homOfLE (n.le_add_right 1)).op = cokernelPowTransition A ℓ n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone of the projections `A ⟶ A/ℓⁿ`. -/
noncomputable def cokernelPowTowerCone : Cone (cokernelPowTower A ℓ) where
  pt := A
  π := NatTrans.ofOpSequence (fun n ↦ cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A)) (fun n ↦ by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      cokernelPowTower_map_succ]
    exact (cokernel_π_cokernelPowTransition A ℓ n).symm)

@[simp]
lemma cokernelPowTowerCone_π_app (n : ℕ) :
    (cokernelPowTowerCone A ℓ).π.app (Opposite.op n) = cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 A) :=
  rfl

section IsLimit

variable {A ℓ} {F : ℕᵒᵖ ⥤ C} (c : Cone F)
  (w : ∀ n : ℕ, (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt) ≫ c.π.app (Opposite.op n) = 0)
  (hc : ∀ n : ℕ, IsColimit (CokernelCofork.ofπ _ (w n)))

/-- The identification `c.pt/ℓⁿ ≅ Fₙ` for a cone `c` whose `n`-th leg is a cokernel of `ℓⁿ`. -/
noncomputable def cokernelPowIsoOfIsColimit (n : ℕ) :
    cokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt) ≅ F.obj (Opposite.op n) :=
  (cokernelIsCokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt)).coconePointUniqueUpToIso (hc n)

@[reassoc (attr := simp)]
lemma cokernel_π_cokernelPowIsoOfIsColimit_hom (n : ℕ) :
    cokernel.π (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt) ≫ (cokernelPowIsoOfIsColimit c w hc n).hom =
      c.π.app (Opposite.op n) :=
  (cokernelIsCokernel (((ℓ ^ n : ℕ) : ℤ) • 𝟙 c.pt)).comp_coconePointUniqueUpToIso_hom (hc n)
    WalkingParallelPair.one

/-- The identification of the tower `n ↦ c.pt/ℓⁿ` with the diagram of a cone `c` whose legs
`c.pt ⟶ Fₙ` are cokernels of `ℓⁿ`. -/
noncomputable def cokernelPowTowerIsoOfIsColimit : cokernelPowTower c.pt ℓ ≅ F :=
  NatIso.ofComponents (fun n ↦ cokernelPowIsoOfIsColimit c w hc n.unop) (fun {X Y} f ↦ by
    induction X with | op m => ?_
    induction Y with | op n => ?_
    have h := (cokernelPowTowerCone c.pt ℓ).w f
    rw [cokernelPowTowerCone_π_app, cokernelPowTowerCone_π_app] at h
    rw [← cancel_epi (cokernel.π (((ℓ ^ m : ℕ) : ℤ) • 𝟙 c.pt)), reassoc_of% h,
      cokernel_π_cokernelPowIsoOfIsColimit_hom, cokernel_π_cokernelPowIsoOfIsColimit_hom_assoc,
      c.w f])

@[simp]
lemma cokernelPowTowerIsoOfIsColimit_hom_app (n : ℕ) :
    (cokernelPowTowerIsoOfIsColimit c w hc).hom.app (Opposite.op n) =
      (cokernelPowIsoOfIsColimit c w hc n).hom :=
  rfl

/-- A cone `c` whose legs `c.pt ⟶ Fₙ` are cokernels of `ℓⁿ` is isomorphic to the cone
`cokernelPowTowerCone c.pt ℓ`, transported along `cokernelPowTowerIsoOfIsColimit`. -/
noncomputable def cokernelPowTowerConeIsoOfIsColimit :
    (Cone.postcompose (cokernelPowTowerIsoOfIsColimit c w hc).hom).obj
      (cokernelPowTowerCone c.pt ℓ) ≅ c :=
  Cone.ext (Iso.refl _) (fun n ↦ by
    induction n with
    | op n =>
      rw [Iso.refl_hom, Category.id_comp, Cone.postcompose_obj_π, NatTrans.comp_app,
        cokernelPowTowerCone_π_app, cokernelPowTowerIsoOfIsColimit_hom_app,
        cokernel_π_cokernelPowIsoOfIsColimit_hom])

/-- A limit cone whose legs `c.pt ⟶ Fₙ` are cokernels of `ℓⁿ` exhibits `c.pt` as `ℓ`-adically
complete and separated. -/
noncomputable def isLimitCokernelPowTowerConeOfIsColimit (h : IsLimit c) :
    IsLimit (cokernelPowTowerCone c.pt ℓ) :=
  (IsLimit.postcomposeHomEquiv (cokernelPowTowerIsoOfIsColimit c w hc) _)
    (h.ofIsoLimit (cokernelPowTowerConeIsoOfIsColimit c w hc).symm)

/-- If `c.pt` is `ℓ`-adically complete and separated, a cone `c` whose legs `c.pt ⟶ Fₙ` are
cokernels of `ℓⁿ` is a limit cone. -/
noncomputable def isLimitOfIsColimitCokernelCofork (h : IsLimit (cokernelPowTowerCone c.pt ℓ)) :
    IsLimit c :=
  ((IsLimit.postcomposeHomEquiv (cokernelPowTowerIsoOfIsColimit c w hc) _).symm h).ofIsoLimit
    (cokernelPowTowerConeIsoOfIsColimit c w hc)

end IsLimit

/-- Cokernels are invariant under conjugation by an isomorphism: if `p` is a cokernel of
`g : Y ⟶ Y` and `e : X ≅ Y` intertwines `f : X ⟶ X` with `g`, then `e.hom ≫ p` is a cokernel
of `f`. -/
noncomputable def isColimitCokernelCoforkOfIsoHomComp {X Y Q : C} (e : X ≅ Y) {f : X ⟶ X}
    {g : Y ⟶ Y} (hfg : f ≫ e.hom = e.hom ≫ g) {p : Y ⟶ Q} (hp : g ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p hp)) :
    IsColimit (CokernelCofork.ofπ (f := f) (e.hom ≫ p)
      (by rw [← Category.assoc, hfg, Category.assoc, hp, Limits.comp_zero])) :=
  have hd {Z : C} (x : X ⟶ Z) (hx : f ≫ x = 0) : g ≫ e.inv ≫ x = 0 := by
    have hgf : g ≫ e.inv = e.inv ≫ f := by
      rw [Iso.comp_inv_eq, Category.assoc, hfg, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hgf, Category.assoc, hx, Limits.comp_zero]
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx ↦ (CokernelCofork.IsColimit.desc' h (e.inv ≫ x) (hd x hx)).1)
    (fun x hx ↦ (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·)
      (CokernelCofork.IsColimit.desc' h (e.inv ≫ x) (hd x hx)).2).trans
        (Iso.hom_inv_id_assoc e x)))
    (fun x hx m hm ↦ Cofork.IsColimit.hom_ext h ((Iso.inv_hom_id_assoc e _).symm.trans
      ((congrArg (e.inv ≫ ·) ((Category.assoc _ _ _).symm.trans hm)).trans
        (CokernelCofork.IsColimit.desc' h (e.inv ≫ x) (hd x hx)).2.symm)))

variable {A ℓ} in
/-- **`ℓ`-adic completeness is invariant under isomorphisms**: if `A ≅ B` and `A` is
`ℓ`-adically complete and separated, then so is `B`. -/
noncomputable def isLimitCokernelPowTowerConeOfIso {B : C} (e : A ≅ B)
    (h : IsLimit (cokernelPowTowerCone A ℓ)) : IsLimit (cokernelPowTowerCone B ℓ) :=
  IsLimit.ofExtendIso e.hom (isLimitOfIsColimitCokernelCofork
    ((cokernelPowTowerCone B ℓ).extend e.hom) _
    (fun n ↦ isColimitCokernelCoforkOfIsoHomComp e
      (by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul])
      (cokernel.condition _) (cokernelIsCokernel _)) h)

end CategoryTheory.Limits
