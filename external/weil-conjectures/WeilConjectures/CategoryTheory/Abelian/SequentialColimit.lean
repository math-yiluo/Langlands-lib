/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.DerivedCategory.Telescope

/-!
# Sequential colimits as cokernels of `1 - shift`

Let `F : ℕ ⥤ C` be a sequence `F₀ ⟶ F₁ ⟶ ⋯` in a preadditive category, with a coproduct
`∐ₙ Fₙ` and the shift `t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` (`CategoryTheory.Limits.Cofan.telescopeShift`). Then:

* the colimit of `F` is the cokernel of `1 - t`
  (`CategoryTheory.Limits.isColimitCokernelCoforkSubTelescopeShift`);
* if `C` is abelian and colimits of shape `ℕ` are exact (for instance if `C` satisfies AB5), then
  `1 - t` is a monomorphism (`CategoryTheory.Limits.mono_id_sub_telescopeShift`), so that
  `0 ⟶ ∐ₙ Fₙ ⟶ ∐ₙ Fₙ ⟶ colim F ⟶ 0` is a short exact sequence
  (`CategoryTheory.Limits.shortExact_telescopeShortComplex_of_isColimit`).

The injectivity of `1 - t` is reduced to the finite stages: `∐ₙ Fₙ` is the colimit of the finite
biproducts `⨁_{i ≤ N} Fᵢ`, and `1 - t` is the colimit of the maps
`⨁_{i ≤ N} Fᵢ ⟶ ⨁_{i ≤ N + 1} Fᵢ` induced by `1 - t`, which are monomorphisms (they are
unitriangular).
-/

@[expose] public section

namespace CategoryTheory.Limits

open Category

variable {C : Type*} [Category* C]

section Cokernel

variable [Preadditive C] {F : ℕ ⥤ C} {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

/-- The cocone over a sequence `F` given by a morphism out of `∐ₙ Fₙ` which is killed by
`1 - t`. -/
@[simps pt]
noncomputable def coconeOfSubTelescopeShift {T : C} (h : P.pt ⟶ T)
    (hh : (𝟙 _ - Cofan.telescopeShift hP) ≫ h = 0) : Cocone F where
  pt := T
  ι := NatTrans.ofSequence (fun n ↦ P.inj n ≫ h) (fun n ↦ by
    have : P.inj n ≫ (𝟙 _ - Cofan.telescopeShift hP) ≫ h = 0 := by rw [hh, comp_zero]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, id_comp, Cofan.inj_telescopeShift_assoc,
      sub_eq_zero] at this
    simp [← this])

@[simp]
lemma coconeOfSubTelescopeShift_ι_app {T : C} (h : P.pt ⟶ T)
    (hh : (𝟙 _ - Cofan.telescopeShift hP) ≫ h = 0) (n : ℕ) :
    (coconeOfSubTelescopeShift hP h hh).ι.app n = P.inj n ≫ h := rfl

variable {c : Cocone F} (hc : IsColimit c)

lemma id_sub_telescopeShift_comp_desc :
    (𝟙 P.pt - Cofan.telescopeShift hP) ≫ Cofan.IsColimit.desc hP (fun n ↦ c.ι.app n) = 0 :=
  Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
    simp [Preadditive.comp_sub, Preadditive.sub_comp, Cofan.IsColimit.fac, c.w]

/-- The colimit of a sequence `F` is the cokernel of `1 - t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ`. -/
noncomputable def isColimitCokernelCoforkSubTelescopeShift :
    IsColimit (CokernelCofork.ofπ (Cofan.IsColimit.desc hP (fun n ↦ c.ι.app n))
      (id_sub_telescopeShift_comp_desc hP)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun h hh ↦ hc.desc (coconeOfSubTelescopeShift hP h hh))
    (fun h hh ↦ Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
      simp only [Cofan.IsColimit.fac_assoc, IsColimit.fac, coconeOfSubTelescopeShift_ι_app])
    (fun h hh m hm ↦ hc.hom_ext fun n ↦ by
      simp only [IsColimit.fac, coconeOfSubTelescopeShift_ι_app, ← hm,
        Cofan.IsColimit.fac_assoc])

end Cokernel

section PartialSum

variable [Preadditive C] [HasFiniteBiproducts C] (F : ℕ ⥤ C)

/-- The family `(Fᵢ)_{i ≤ m}`. -/
abbrev partialFamily (m : ℕ) : Fin (m + 1) → C := fun i ↦ F.obj i

/-- The finite biproduct `⨁_{i ≤ N + k} Fᵢ`. -/
noncomputable abbrev partialSum (k N : ℕ) : C := ⨁ partialFamily F (N + k)

/-- The inclusion `⨁_{i ≤ N + k} Fᵢ ⟶ ⨁_{i ≤ N + 1 + k} Fᵢ`. -/
noncomputable def partialSumStep (k N : ℕ) : partialSum F k N ⟶ partialSum F k (N + 1) :=
  biproduct.desc fun i ↦ biproduct.ι (partialFamily F (N + 1 + k)) ⟨i, by omega⟩

/-- The sequence `N ↦ ⨁_{i ≤ N + k} Fᵢ` of finite partial sums. -/
noncomputable def partialSumFunctor (k : ℕ) : ℕ ⥤ C :=
  Functor.ofSequence (partialSumStep F k)

@[reassoc]
lemma ι_partialSumFunctor_map (k : ℕ) {N M : ℕ} (h : N ≤ M) (i : ℕ) (hi : i < N + k + 1) :
    biproduct.ι (partialFamily F (N + k)) ⟨i, hi⟩ ≫
        (partialSumFunctor F k).map (homOfLE h) =
      biproduct.ι (partialFamily F (M + k)) ⟨i, by omega⟩ := by
  induction M, h using Nat.le_induction with
  | base =>
    have : homOfLE (le_refl N) = 𝟙 N := rfl
    rw [this, Functor.map_id]
    exact Category.comp_id _
  | succ M hNM ih =>
    have : homOfLE (hNM.trans M.le_succ) = homOfLE hNM ≫ homOfLE M.le_succ := rfl
    rw [this, Functor.map_comp, reassoc_of% ih]
    simp [partialSumFunctor, partialSumStep]

variable {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

/-- The map `⨁_{i ≤ m} Fᵢ ⟶ ∐ₙ Fₙ`. -/
noncomputable abbrev partialSumToCoproduct (m : ℕ) : (⨁ partialFamily F m) ⟶ P.pt :=
  biproduct.desc fun i ↦ P.inj (i : ℕ)

/-- The cocone of the finite partial sums `⨁_{i ≤ N + k} Fᵢ` with point `∐ₙ Fₙ`. -/
@[simps pt]
noncomputable def partialSumCocone (k : ℕ) : Cocone (partialSumFunctor F k) where
  pt := P.pt
  ι := NatTrans.ofSequence (fun N ↦ partialSumToCoproduct F (P := P) (N + k)) (fun N ↦ by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp [partialSumFunctor, partialSumStep])

@[simp]
lemma partialSumCocone_ι_app (k N : ℕ) :
    (partialSumCocone F k (P := P)).ι.app N = partialSumToCoproduct F (P := P) (N + k) := rfl

/-- `∐ₙ Fₙ` is the colimit of the finite partial sums `⨁_{i ≤ N + k} Fᵢ`. -/
noncomputable def isColimitPartialSumCocone (k : ℕ) :
    IsColimit (partialSumCocone F k (P := P)) where
  desc s := Cofan.IsColimit.desc hP fun n ↦
    biproduct.ι (partialFamily F (n + k)) ⟨n, by omega⟩ ≫ s.ι.app n
  fac s N := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    obtain ⟨i, hi⟩ := i
    have h₁ := s.w (homOfLE (le_max_left i N))
    have h₂ := s.w (homOfLE (le_max_right i N))
    rw [partialSumCocone_ι_app, biproduct.ι_desc_assoc, Cofan.IsColimit.fac, ← h₁, ← h₂,
      ι_partialSumFunctor_map_assoc, ι_partialSumFunctor_map_assoc]
  uniq s m hm := Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
    rw [Cofan.IsColimit.fac, ← hm, partialSumCocone_ι_app, biproduct.ι_desc_assoc]

/-- The map `⨁_{i ≤ N} Fᵢ ⟶ ⨁_{i ≤ N + 1} Fᵢ` induced by `1 - t`. -/
noncomputable def partialSumSubShift (N : ℕ) :
    (⨁ partialFamily F (N + 0)) ⟶ (⨁ partialFamily F (N + 1)) :=
  biproduct.desc fun i ↦
    biproduct.ι (partialFamily F (N + 1)) ⟨i, by omega⟩ -
      F.map (homOfLE (i : ℕ).le_succ) ≫ biproduct.ι (partialFamily F (N + 1)) ⟨i + 1, by omega⟩

/-- The natural transformation `(⨁_{i ≤ N} Fᵢ)_N ⟶ (⨁_{i ≤ N + 1} Fᵢ)_N` induced by `1 - t`. -/
noncomputable def partialSumSubShiftNatTrans : partialSumFunctor F 0 ⟶ partialSumFunctor F 1 :=
  NatTrans.ofSequence (partialSumSubShift F) (fun N ↦ by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    simp [partialSumFunctor, partialSumStep, partialSumSubShift, Preadditive.sub_comp])

lemma partialSumSubShift_π_zero (N : ℕ) :
    partialSumSubShift F N ≫ biproduct.π (partialFamily F (N + 1)) ⟨0, by omega⟩ =
      biproduct.π (partialFamily F (N + 0)) ⟨0, by omega⟩ := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · simp [partialSumSubShift, Preadditive.sub_comp]
    rfl
  · simp [partialSumSubShift, Preadditive.sub_comp]

lemma partialSumSubShift_π_succ (N j : ℕ) (hj : j + 1 < N + 0 + 1) :
    partialSumSubShift F N ≫ biproduct.π (partialFamily F (N + 1)) ⟨j + 1, by omega⟩ =
      biproduct.π (partialFamily F (N + 0)) ⟨j + 1, hj⟩ -
        biproduct.π (partialFamily F (N + 0)) ⟨j, by omega⟩ ≫ F.map (homOfLE j.le_succ) := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  obtain ⟨i, hi⟩ := i
  by_cases h₁ : i = j + 1
  · subst h₁
    simp [partialSumSubShift, Preadditive.sub_comp]
  · by_cases h₂ : i = j
    · subst h₂
      simp [partialSumSubShift, Preadditive.sub_comp]
    · simp [partialSumSubShift, Preadditive.sub_comp, h₁, h₂]

instance mono_partialSumSubShift (N : ℕ) : Mono (partialSumSubShift F N) where
  right_cancellation {T} g₁ g₂ hg := by
    rw [← sub_eq_zero, ← Preadditive.sub_comp] at hg
    rw [← sub_eq_zero]
    set g := g₁ - g₂
    have key : ∀ (j : ℕ) (hj : j < N + 0 + 1),
        g ≫ biproduct.π (partialFamily F (N + 0)) ⟨j, hj⟩ = 0 := by
      intro j
      induction j with
      | zero =>
        intro hj
        rw [← partialSumSubShift_π_zero, reassoc_of% hg, zero_comp]
      | succ j ih =>
        intro hj
        have := hg =≫ biproduct.π (partialFamily F (N + 1)) ⟨j + 1, by omega⟩
        rw [Category.assoc, partialSumSubShift_π_succ F N j hj, Preadditive.comp_sub,
          reassoc_of% (ih (by omega)), zero_comp, sub_zero, zero_comp] at this
        exact this
    exact biproduct.hom_ext _ _ fun j ↦ by
      obtain ⟨j, hj⟩ := j
      rw [key j hj, zero_comp]

end PartialSum

section Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

variable [Abelian C] (F : ℕ ⥤ C) {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)

set_option linter.flexible false in
/-- In an abelian category with exact colimits of shape `ℕ`, the map
`1 - t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` is a monomorphism. -/
lemma mono_id_sub_telescopeShift [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C] :
    Mono (𝟙 P.pt - Cofan.telescopeShift hP) := by
  have : Mono (partialSumSubShiftNatTrans F) := by
    have (N : ℕ) : Mono ((partialSumSubShiftNatTrans F).app N) :=
      mono_partialSumSubShift F N
    exact NatTrans.mono_of_mono_app _
  refine colim.map_mono' (partialSumSubShiftNatTrans F) (isColimitPartialSumCocone F hP 0)
    (isColimitPartialSumCocone F hP 1) _ fun N ↦ ?_
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  simp [partialSumSubShiftNatTrans, partialSumSubShift, Preadditive.comp_sub,
    Preadditive.sub_comp]
  exact Category.comp_id _

variable {c : Cocone F} (hc : IsColimit c)

include hc in
/-- In an abelian category with exact colimits of shape `ℕ`, a sequence `F` gives a short exact
sequence `0 ⟶ ∐ₙ Fₙ ──1 - t──▶ ∐ₙ Fₙ ⟶ colim F ⟶ 0`. -/
lemma shortExact_telescopeShortComplex_of_isColimit [HasColimitsOfShape ℕ C]
    [HasExactColimitsOfShape ℕ C] : (Cofan.telescopeShortComplex hP c).ShortExact :=
  have : Mono (Cofan.telescopeShortComplex hP c).f := mono_id_sub_telescopeShift F hP
  have : Epi (Cofan.telescopeShortComplex hP c).g :=
    Cofork.IsColimit.epi (isColimitCokernelCoforkSubTelescopeShift hP hc)
  { exact := ShortComplex.exact_of_g_is_cokernel _
      (isColimitCokernelCoforkSubTelescopeShift hP hc) }

end Abelian

end CategoryTheory.Limits
