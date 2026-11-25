/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange

/-! Cohomology of a homotopy limit of an eventually constant tower. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

private theorem roos_epi
    {C : Type*} [Category C] [Preadditive C]
    (M : ℕ → C) (f : ∀ n : ℕ, M (n + 1) ⟶ M n)
    (P : Fan M) (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n, t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫ f n)
    (hf : ∀ n, IsIso (f n)) : Epi t := by
  let : ∀ n, IsIso (f n) := hf
  let x : ∀ n, P.pt ⟶ M n := fun n ↦
    Nat.rec (motive := fun n ↦ P.pt ⟶ M n) 0
      (fun n a ↦ (a - P.proj n) ≫ inv (f n)) n
  let s : P.pt ⟶ P.pt := Fan.IsLimit.lift hP x
  have hs : s ≫ t = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext hP
    intro n
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc,
      Fan.IsLimit.fac, Fan.IsLimit.fac]
    change x n - ((x n - P.proj n) ≫ inv (f n)) ≫ f n = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    abel
  exact ⟨fun {Z} g h he ↦ by
    simpa only [← Category.assoc, hs, Category.id_comp] using congrArg (fun a ↦ s ≫ a) he⟩

private theorem roos_zero_leg
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : ℕᵒᵖ ⥤ DerivedCategory C) (c : Cone F) (hc : IsHomotopyLimit c)
    (hprod : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j)) (q : ℤ)
    (ht : ∀ n : ℕ,
      IsIso ((DerivedCategory.homologyFunctor C q).map
        (F.map (homOfLE n.le_succ).op)) ∧
      IsIso ((DerivedCategory.homologyFunctor C (q - 1)).map
        (F.map (homOfLE n.le_succ).op))) :
    IsIso ((DerivedCategory.homologyFunctor C q).map (c.π.app (op 0))) := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let H := DerivedCategory.homologyFunctor C q
  let H' := DerivedCategory.homologyFunctor C (q - 1)
  let := hprod q
  let := hprod (q - 1)
  let HP : Fan (fun n : ℕ ↦ H.obj (F.obj (op n))) :=
    Fan.mk (H.obj P.pt) (fun n ↦ H.map (P.proj n))
  let hHP : IsLimit HP := isLimitFanMkObjOfIsLimit H _ _ hP
  have hepi : Epi (H'.map (𝟙 P.pt - towerShift hP)) := by
    apply roos_epi (fun n ↦ H'.obj (F.obj (op n)))
      (fun n ↦ H'.map (F.map (homOfLE n.le_succ).op))
      (Fan.mk (H'.obj P.pt) (fun n ↦ H'.map (P.proj n)))
      (isLimitFanMkObjOfIsLimit H' _ _ hP)
    · intro n
      change H'.map (𝟙 P.pt - towerShift hP) ≫ H'.map (P.proj n) = _
      rw [← H'.map_comp]
      have hh : (𝟙 P.pt - towerShift hP) ≫ P.proj n =
          P.proj n - P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
        rw [Preadditive.sub_comp, Category.id_comp, towerShift_proj]
      rw [hh, H'.map_sub, H'.map_comp]
      rfl
    · exact fun n ↦ (ht n).2
  let T := Triangle.mk (Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)))
    (𝟙 P.pt - towerShift hP) δ
  have hδ : DerivedCategory.HomologySequence.δ T (q - 1) q (by omega) = 0 :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT
      (q - 1) q (by omega)).1 hepi
  have hmono : Mono (H.map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT
      (q - 1) q (by omega)).2 hδ
  let M : ℕ → C := fun n ↦ H.obj (F.obj (op n))
  let f : ∀ n, M (n + 1) ⟶ M n := fun n ↦ H.map (F.map (homOfLE n.le_succ).op)
  let : ∀ n, IsIso (f n) := fun n ↦ (ht n).1
  let e : ∀ n, M 0 ≅ M n := fun n ↦
    Nat.rec (motive := fun n ↦ M 0 ≅ M n) (Iso.refl _)
      (fun n en ↦ en ≪≫ (asIso (f n)).symm) n
  let a : M 0 ⟶ H.obj P.pt := Fan.IsLimit.lift hHP (fun n ↦ (e n).hom)
  have ha (n : ℕ) : a ≫ H.map (P.proj n) = (e n).hom := Fan.IsLimit.fac hHP _ n
  have haz : a ≫ H.map T.mor₂ = 0 := by
    apply Fan.IsLimit.hom_ext hHP
    intro n
    dsimp only [HP, T, Triangle.mk_mor₂, fan_mk_proj]
    rw [Limits.zero_comp]
    change (a ≫ H.map (𝟙 P.pt - towerShift hP)) ≫ H.map (P.proj n) = 0
    rw [Category.assoc, ← H.map_comp, Preadditive.sub_comp, Category.id_comp,
      towerShift_proj, H.map_sub, H.map_comp, Preadditive.comp_sub,
      ← Category.assoc, ha, ha]
    change (e n).hom - ((e n).hom ≫ inv (f n)) ≫ f n = 0
    simp
  obtain ⟨b, hb⟩ := (DerivedCategory.HomologySequence.exact₂ T hT q).lift' a haz
  change b ≫ H.map T.mor₁ = a at hb
  have hleg (n : ℕ) : H.map T.mor₁ ≫ H.map (P.proj n) = H.map (c.π.app (op n)) := by
    rw [← H.map_comp]
    exact congrArg H.map (Fan.IsLimit.fac hP _ n)
  have hbf : b ≫ H.map (c.π.app (op 0)) = 𝟙 _ := by
    rw [← hleg, ← Category.assoc, hb, ha]
    rfl
  have hfb : H.map (c.π.app (op 0)) ≫ b = 𝟙 _ := by
    apply (cancel_mono (H.map T.mor₁)).1
    rw [Category.assoc, hb, Category.id_comp]
    apply Fan.IsLimit.hom_ext hHP
    intro n
    change (H.map (c.π.app (op 0)) ≫ a) ≫ H.map (P.proj n) =
      H.map T.mor₁ ≫ H.map (P.proj n)
    rw [Category.assoc, ha, hleg]
    induction n with
    | zero => exact Category.comp_id _
    | succ n ih =>
      have hw := congrArg H.map (c.w (homOfLE n.le_succ).op)
      simp only [H.map_comp] at hw
      change H.map (c.π.app (op 0)) ≫ (e n).hom ≫ inv (f n) = _
      rw [← Category.assoc, ih]
      apply (cancel_mono (f n)).1
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hw.symm
  exact ⟨⟨b, hfb, hbf⟩⟩

/-- Eventual constancy in two adjacent degrees makes every sufficiently late cone leg
invertible on cohomology.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-arbitrary.proof.md,
Milnor paragraph (blueprint: lem-roos-eventually-constant-projection).

Proof: discard the finite initial segment by homotopy-limit tail invariance. Apply
cohomology to its Milnor triangle. The degree q-1 difference map has a section, obtained
recursively by x_0=0 and x_(i+1)=t_i^(-1)(x_i-y_i). Thus the degree q first arrow is monic
and is a kernel of its difference map. The compatible inverse transition isomorphisms
from the zeroth term give an inverse to the zeroth cone leg through that kernel. -/
theorem DerivedCategory.isIso_homology_map_cone_leg_of_eventually_isIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasCountableProducts (DerivedCategory C)]
    (F : ℕᵒᵖ ⥤ DerivedCategory C) (c : Cone F)
    (hc : IsHomotopyLimit c)
    (hprod : ∀ j : ℤ, PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C j))
    (q : ℤ) (N : ℕ)
    (ht : ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor C q).map
        (F.map (homOfLE n.le_succ).op)) ∧
      IsIso ((DerivedCategory.homologyFunctor C (q - 1)).map
        (F.map (homOfLE n.le_succ).op)))
    (n : ℕ) (hn : N ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C q).map (c.π.app (op n))) := by
  have hsucc (a b : ℕ) (hab : a ≤ b) (hb : b = a + 1) (ha : N ≤ a) :
      IsIso ((homologyFunctor C q).map (F.map (homOfLE hab).op)) ∧
      IsIso ((homologyFunctor C (q - 1)).map (F.map (homOfLE hab).op)) := by
    subst b
    exact ht a ha
  let G := addOpFunctor n ⋙ F
  have htail (i : ℕ) :
      IsIso ((homologyFunctor C q).map (G.map (homOfLE i.le_succ).op)) ∧
      IsIso ((homologyFunctor C (q - 1)).map (G.map (homOfLE i.le_succ).op)) := by
    exact hsucc (i + n) (i + 1 + n) (by omega) (by omega) (by omega)
  have h := roos_zero_leg G (c.whisker (addOpFunctor n))
    (hc.whiskerAdd n) hprod q htail
  have hleg (a b : ℕ) (he : a = b)
      (hi : IsIso ((homologyFunctor C q).map (c.π.app (op a)))) :
      IsIso ((homologyFunctor C q).map (c.π.app (op b))) := by
    subst b
    exact hi
  exact hleg (0 + n) n (Nat.zero_add n) h
