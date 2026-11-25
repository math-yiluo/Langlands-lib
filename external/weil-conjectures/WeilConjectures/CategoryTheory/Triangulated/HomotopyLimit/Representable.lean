/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Homotopy limits of partially representing objects

Let `Φ : C ⥤ D` be a functor and `P` a property of objects of `C`. A morphism
`ε : Φ.obj T ⟶ M` *represents* `Hom(Φ -, M)` on `P` (`CategoryTheory.Functor.RepresentsOn`) if
`f ↦ Φ.map f ≫ ε` is a bijection `Hom(A, T) ≃ Hom(Φ A, M)` for every `A` satisfying `P`: `T` is
a value of a "partial right adjoint" of `Φ` at `M`.

This file contains the formal core of the construction of right adjoints as derived limits of
partial right adjoints: if `M` is the homotopy limit of a tower `Mₙ` and each `Mₙ` is represented
on `P` by some `Tₙ`, then the `Tₙ` form a tower and its homotopy limit represents `M` on `P`.

## Main definitions

- `CategoryTheory.Functor.RepresentsOn`: `ε : Φ.obj T ⟶ M` represents `Hom(Φ -, M)` on `P`.
- `CategoryTheory.Functor.RepresentsOn.tower`: the tower formed by objects representing the terms
  of a tower `M`, and `CategoryTheory.Functor.RepresentsOn.towerπ` the natural transformation
  to `M`.

## Main statements

- `CategoryTheory.Functor.RepresentsOn.of_isLimit_fan`: products of representing maps represent.
- `CategoryTheory.Functor.RepresentsOn.of_distTriang`: a five lemma; in a morphism from the image
  of a distinguished triangle to a distinguished triangle, if the second and third components
  represent on a shift-stable `P`, so does the first.
- `CategoryTheory.Functor.RepresentsOn.exists_of_isHomotopyLimit`: the homotopy limit of a tower
  of representing objects represents the homotopy limit.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite Pretriangulated

variable {C D : Type*} [Category C] [Category D]

namespace Functor

/-- `ε : Φ.obj T ⟶ M` *represents* `Hom(Φ -, M)` on the objects satisfying `P` if, for every
`A` with `P A`, the map `Hom(A, T) → Hom(Φ A, M)`, `f ↦ Φ.map f ≫ ε`, is bijective. -/
def RepresentsOn (Φ : C ⥤ D) (P : ObjectProperty C) {T : C} {M : D} (ε : Φ.obj T ⟶ M) :
    Prop :=
  ∀ A : C, P A → Function.Bijective fun f : A ⟶ T ↦ Φ.map f ≫ ε

namespace RepresentsOn

variable {Φ : C ⥤ D} {P : ObjectProperty C}

/-- A product of representing maps represents: if `εᵢ : Φ.obj Xᵢ ⟶ Yᵢ` represent on `P` and
`ψ : Φ(∏ Xᵢ) ⟶ ∏ Yᵢ` has components `Φ(∏ Xᵢ) ⟶ Φ Xᵢ ⟶ Yᵢ`, then `ψ` represents on `P`. -/
lemma of_isLimit_fan {ι : Type*} {X : ι → C} {c : Fan X} (hc : IsLimit c) {Y : ι → D}
    {d : Fan Y} (hd : IsLimit d) {ε : ∀ i, Φ.obj (X i) ⟶ Y i}
    (hε : ∀ i, Φ.RepresentsOn P (ε i)) (ψ : Φ.obj c.pt ⟶ d.pt)
    (hψ : ∀ i, ψ ≫ d.proj i = Φ.map (c.proj i) ≫ ε i) : Φ.RepresentsOn P ψ := by
  intro A hA
  refine ⟨fun f g hfg ↦ Fan.IsLimit.hom_ext hc _ _ fun i ↦ (hε i A hA).1 ?_, fun w ↦ ?_⟩
  · simpa [hψ] using congrArg (· ≫ d.proj i) hfg
  · choose g hg using fun i ↦ (hε i A hA).2 (w ≫ d.proj i)
    refine ⟨Fan.IsLimit.lift hc g, Fan.IsLimit.hom_ext hd _ _ fun i ↦ ?_⟩
    simp only [assoc, hψ, ← Φ.map_comp_assoc, Fan.IsLimit.fac]
    exact hg i

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Φ.CommShift ℤ] [Φ.Additive]
  [P.IsStableUnderShift ℤ]

/-- The five lemma for representing maps: let `T₁` be a distinguished triangle in `C`, `T₂` a
distinguished triangle in `D`, and `(a, b, c)` a morphism from the image of `T₁` under `Φ` to
`T₂`. If `b` and `c` represent on a shift-stable property `P`, then so does `a`. -/
lemma of_distTriang {T₁ : Triangle C} (hT₁ : T₁ ∈ distTriang C) {T₂ : Triangle D}
    (hT₂ : T₂ ∈ distTriang D) (a : Φ.obj T₁.obj₁ ⟶ T₂.obj₁) (b : Φ.obj T₁.obj₂ ⟶ T₂.obj₂)
    (c : Φ.obj T₁.obj₃ ⟶ T₂.obj₃) (comm₁ : Φ.map T₁.mor₁ ≫ b = a ≫ T₂.mor₁)
    (comm₂ : Φ.map T₁.mor₂ ≫ c = b ≫ T₂.mor₂)
    (comm₃ : Φ.map T₁.mor₃ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app T₁.obj₁ ≫ a⟦(1 : ℤ)⟧' =
      c ≫ T₂.mor₃)
    (hb : Φ.RepresentsOn P b) (hc : Φ.RepresentsOn P c) : Φ.RepresentsOn P a := by
  intro A hA
  have hA₁ : P (A⟦(1 : ℤ)⟧) := P.le_shift (1 : ℤ) A hA
  have inj (f : A ⟶ T₁.obj₁) (hf : Φ.map f ≫ a = 0) : f = 0 := by
    have h₁ : f ≫ T₁.mor₁ = 0 := (hb A hA).1 (by
      simp only [Φ.map_comp, assoc, comm₁, reassoc_of% hf, Φ.map_zero, zero_comp])
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₁ T₁ hT₁ (f⟦(1 : ℤ)⟧')
      (by rw [← Functor.map_comp, h₁, Functor.map_zero])
    have h₂ : (Φ.map u ≫ c) ≫ T₂.mor₃ = 0 := by
      rw [assoc, ← comm₃, ← Φ.map_comp_assoc, ← hu, Φ.commShiftIso_hom_naturality_assoc,
        ← Functor.map_comp, hf, Functor.map_zero, comp_zero]
    obtain ⟨w, hw⟩ := Triangle.coyoneda_exact₃ T₂ hT₂ _ h₂
    obtain ⟨v, hv⟩ := (hb _ hA₁).2 w
    have hv' : Φ.map v ≫ b = w := hv
    have h₃ : u = v ≫ T₁.mor₂ := (hc _ hA₁).1 (by
      simp only [hw, ← hv', Φ.map_comp, assoc, comm₂])
    have h₄ : f⟦(1 : ℤ)⟧' = 0 := by
      rw [hu, h₃, assoc, comp_distTriang_mor_zero₂₃ _ hT₁, comp_zero]
    exact (shiftFunctor C (1 : ℤ)).map_eq_zero_iff.mp h₄
  refine ⟨fun f g hfg ↦ sub_eq_zero.mp (inj _ ?_), fun g ↦ ?_⟩
  · have hfg' : Φ.map f ≫ a = Φ.map g ≫ a := hfg
    rw [Φ.map_sub, Preadditive.sub_comp, hfg', sub_self]
  obtain ⟨x, hx⟩ := (hb A hA).2 (g ≫ T₂.mor₁)
  have hx' : Φ.map x ≫ b = g ≫ T₂.mor₁ := hx
  have h₁ : x ≫ T₁.mor₂ = 0 := (hc A hA).1 (by
    simp only [Φ.map_comp, assoc, comm₂, reassoc_of% hx', comp_distTriang_mor_zero₁₂ _ hT₂,
      comp_zero, Φ.map_zero, zero_comp])
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T₁ hT₁ x h₁
  have h₂ : (g - Φ.map y ≫ a) ≫ T₂.mor₁ = 0 := by
    rw [Preadditive.sub_comp, assoc, ← comm₁, ← hx', hy, Φ.map_comp, assoc, sub_self]
  obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ T₂ hT₂ ((g - Φ.map y ≫ a)⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, h₂, Functor.map_zero])
  obtain ⟨s, hs⟩ := (hc _ hA₁).2 ((Φ.commShiftIso (1 : ℤ)).hom.app A ≫ z)
  have hs' : Φ.map s ≫ c = (Φ.commShiftIso (1 : ℤ)).hom.app A ≫ z := hs
  let t : A ⟶ T₁.obj₁ := (shiftFunctor C (1 : ℤ)).preimage (s ≫ T₁.mor₃)
  have ht : Φ.map t ≫ a = g - Φ.map y ≫ a := by
    refine (shiftFunctor D (1 : ℤ)).map_injective ?_
    rw [← cancel_epi ((Φ.commShiftIso (1 : ℤ)).hom.app A),
      (shiftFunctor D (1 : ℤ)).map_comp (Φ.map t) a, ← Φ.commShiftIso_hom_naturality_assoc,
      Functor.map_preimage, Φ.map_comp, assoc, comm₃, reassoc_of% hs', hz]
  refine ⟨t + y, ?_⟩
  simp only [Φ.map_add, Preadditive.add_comp, ht, sub_add_cancel]

end Triangulated

section Tower

variable {T : ℕ → C} (hT : ∀ n, P (T n)) {M : ℕᵒᵖ ⥤ D} {ε : ∀ n, Φ.obj (T n) ⟶ M.obj (op n)}
  (hε : ∀ n, Φ.RepresentsOn P (ε n))

/-- The transition map `Tₙ₊₁ ⟶ Tₙ` of the tower of representing objects: the unique map `f`
with `Φ.map f ≫ εₙ = εₙ₊₁ ≫ M.map _` (`RepresentsOn.map_towerMap_comp`). -/
noncomputable def towerMap (n : ℕ) : T (n + 1) ⟶ T n :=
  ((hε n) _ (hT (n + 1))).2 (ε (n + 1) ≫ M.map (homOfLE (n.le_add_right 1)).op) |>.choose

@[reassoc]
lemma map_towerMap_comp (n : ℕ) :
    Φ.map (towerMap hT hε n) ≫ ε n = ε (n + 1) ≫ M.map (homOfLE (n.le_add_right 1)).op :=
  ((hε n) _ (hT (n + 1))).2 (ε (n + 1) ≫ M.map (homOfLE (n.le_add_right 1)).op) |>.choose_spec

/-- The tower `⋯ ⟶ T₂ ⟶ T₁ ⟶ T₀` formed by objects `Tₙ` representing the terms `Mₙ` of a tower
`M` on `P`, provided each `Tₙ` satisfies `P`. -/
noncomputable def tower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (towerMap hT hε)

@[simp]
lemma tower_obj (n : ℕ) : (tower hT hε).obj (op n) = T n :=
  rfl

/-- The natural transformation `Φ(Tₙ) ⟶ Mₙ` from the image of the tower of representing
objects to `M`, with components the representing maps `εₙ`. -/
noncomputable def towerπ : tower hT hε ⋙ Φ ⟶ M :=
  NatTrans.ofOpSequence (F := tower hT hε ⋙ Φ) (G := M) ε fun n ↦ by
    simpa [tower] using map_towerMap_comp hT hε n

@[simp]
lemma towerπ_app (n : ℕ) : (towerπ hT hε).app (op n) = ε n :=
  rfl

end Tower

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [Φ.CommShift ℤ] [Φ.IsTriangulated]
  [Φ.Additive] [P.IsStableUnderShift ℤ]

/-- The homotopy limit of representing objects represents the homotopy limit: let
`ε : T ⋙ Φ ⟶ M` be a morphism of towers whose components represent `Hom(Φ -, Mₙ)` on a
shift-stable property `P`. Given homotopy limit cones `cT` over `T` and `cM` over `M`, there
is a map `e : Φ(R lim T) ⟶ R lim M` compatible with the legs and `ε`, which represents
`Hom(Φ -, R lim M)` on `P`. It is the first component of a morphism of Milnor triangles, and
represents by the five lemma `RepresentsOn.of_distTriang`. -/
theorem exists_of_isHomotopyLimit {T : ℕᵒᵖ ⥤ C} {M : ℕᵒᵖ ⥤ D} (ε : T ⋙ Φ ⟶ M)
    (hε : ∀ n : ℕ, Φ.RepresentsOn P (ε.app (op n))) {cT : Cone T} (hcT : IsHomotopyLimit cT)
    {cM : Cone M} (hcM : IsHomotopyLimit cM) :
    ∃ e : Φ.obj cT.pt ⟶ cM.pt,
      (∀ n : ℕ, e ≫ cM.π.app (op n) = Φ.map (cT.π.app (op n)) ≫ ε.app (op n)) ∧
        Φ.RepresentsOn P e := by
  obtain ⟨PT, hPT, δT, hT⟩ := hcT
  obtain ⟨PM, hPM, δM, hM⟩ := hcM
  let ψ : Φ.obj PT.pt ⟶ PM.pt := Fan.IsLimit.lift hPM fun n ↦ Φ.map (PT.proj n) ≫ ε.app (op n)
  have hψ (n : ℕ) : ψ ≫ PM.proj n = Φ.map (PT.proj n) ≫ ε.app (op n) := Fan.IsLimit.fac hPM _ n
  have hψP : Φ.RepresentsOn P ψ := of_isLimit_fan hPT hPM hε ψ hψ
  have hcomm : Φ.map (𝟙 PT.pt - towerShift hPT) ≫ ψ = ψ ≫ (𝟙 PM.pt - towerShift hPM) :=
    Fan.IsLimit.hom_ext hPM _ _ fun n ↦ by
      have hnat := ε.naturality (homOfLE (n.le_add_right 1)).op
      simp only [Functor.comp_map] at hnat
      simp only [Φ.map_sub, Φ.map_id, Preadditive.sub_comp, Preadditive.comp_sub, id_comp,
        comp_id, assoc, hψ, towerShift_proj, ← Φ.map_comp_assoc, Φ.map_comp, hnat]
      rw [reassoc_of% hψ (n + 1)]
  obtain ⟨e, he₁, he₃⟩ :=
    complete_distinguished_triangle_morphism₁ _ _ (Φ.map_distinguished _ hT) hM ψ ψ hcomm
  have h₁ : Φ.map (Fan.IsLimit.lift hPT fun n ↦ cT.π.app (op n)) ≫ ψ =
      e ≫ Fan.IsLimit.lift hPM fun n ↦ cM.π.app (op n) := he₁
  have h₃ : Φ.map δT ≫ (Φ.commShiftIso (1 : ℤ)).hom.app cT.pt ≫ e⟦(1 : ℤ)⟧' = ψ ≫ δM := by
    rw [← assoc]
    exact he₃
  refine ⟨e, fun n ↦ ?_, of_distTriang hT hM e ψ ψ h₁ hcomm h₃ hψP hψP⟩
  have h := h₁ =≫ PM.proj n
  simp only [assoc, hψ, Fan.IsLimit.fac, ← Φ.map_comp_assoc] at h
  exact h.symm

end RepresentsOn

end Functor

end CategoryTheory
