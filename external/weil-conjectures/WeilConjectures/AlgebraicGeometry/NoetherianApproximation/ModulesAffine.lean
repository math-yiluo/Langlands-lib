/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.PresentationSections

/-!
# Modules of finite presentation on a cofiltered limit of affine schemes

Let `{Eⱼ}` be a cofiltered system of affine schemes with limit `X = lim Eⱼ`. Then the category of
modules of finite presentation on `X` is the colimit of the categories of modules of finite
presentation on the `Eⱼ` (Stacks, Tag 01ZR, affine case; EGA IV₃, 8.5.2):

- every module of finite presentation on `X` is the pullback of one on some `Eⱼ`
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_of_isLimit_of_isAffine`);
- two morphisms between modules of finite presentation on `Eⱼ` which agree after pullback to `X`
  agree after pullback to some later stage
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_eq_of_isLimit_of_isAffine`);
- every morphism between the pullbacks to `X` of modules of finite presentation on `Eⱼ` is the
  pullback of a morphism defined over some later stage
  (`AlgebraicGeometry.Scheme.Modules.exists_pullback_map_eq_of_isLimit_of_isAffine'`).

## Proof

On an affine scheme a quasi-coherent module is determined by its global sections, and morphisms
out of it are determined by, and can be built from, the images of generators of the global
sections satisfying the relations (`Modules/PresentationSections.lean`). A presentation of the
global sections pulls back to a presentation with the coefficients pulled back. The global
sections of `X` are the colimit of those of the `Eⱼ`
(`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit`,
`AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`), so the finitely many
coefficients of the relations, of the images of generators, and of the identities between them
descend to a finite stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

section Helpers

variable {X Y : Scheme.{u}}

/-- The pullback of a finite linear combination of global sections is the linear combination of
the pullbacks, with coefficients pulled back along `g.appTop`. -/
lemma pullbackΓ_sum_smul (g : Y ⟶ X) (M : X.Modules) {ι : Type*} (s : Finset ι)
    (a : ι → Γ(X, ⊤)) (m : ι → Γ(M, ⊤)) :
    pullbackΓ g M (∑ i ∈ s, a i • m i) = ∑ i ∈ s, g.appTop (a i) • pullbackΓ g M (m i) := by
  rw [map_sum]
  simp [pullbackΓ_smul_appTop]

/-- A morphism of modules commutes with finite linear combinations of sections. -/
lemma Hom.app_sum_smul {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) {ι : Type*} (s : Finset ι)
    (a : ι → Γ(X, U)) (m : ι → Γ(M, U)) :
    φ.app U (∑ i ∈ s, a i • m i) = ∑ i ∈ s, a i • φ.app U (m i) := by
  simp [map_sum]

end Helpers

/-- Finite linear combinations over a finite type are finite sums. -/
lemma _root_.Finsupp.linearCombination_eq_sum_fintype {A M G : Type*} [Fintype G] [Semiring A]
    [AddCommMonoid M] [Module A M] (v : G → M) (f : G →₀ A) :
    Finsupp.linearCombination A v f = ∑ g, f g • v g := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  simp

section Colimit

/-!
### Schemes whose global functions are the colimit of those of a cofiltered system

Throughout, `p j : X ⟶ E.obj j` is a compatible family of morphisms from an affine scheme `X` to
a cofiltered system of affine schemes such that `Γ(X, ⊤)` is the colimit of the `Γ(E.obj j, ⊤)`:
every global function on `X` comes from some stage (`hsurj`), and a global function on a stage
vanishing on `X` vanishes on some later stage (`hinj`). This is the case for the limit cone
(`AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit`,
`AlgebraicGeometry.exists_appTop_map_eq_zero_of_isAffine_of_isLimit`). Working with `X` rather
than with the cone point avoids the objects `((Functor.const J).obj c.pt).obj j`.
-/

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}}
  [∀ j, IsAffine (E.obj j)] {X : Scheme.{u}}

omit [IsCofiltered J] [∀ j, IsAffine (E.obj j)] in
/-- Pulling back global functions along `E.map (f ≫ g)` is pulling back along `E.map g`, then
along `E.map f`. -/
lemma appTop_map_comp_apply {k k' j : J} (f : k ⟶ k') (g : k' ⟶ j) (x : Γ(E.obj j, ⊤)) :
    (E.map (f ≫ g)).appTop x = (E.map f).appTop ((E.map g).appTop x) := by
  rw [E.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

omit [IsCofiltered J] [∀ j, IsAffine (E.obj j)] in
/-- Global functions on a stage, pulled back to a later stage and then along a compatible family
of morphisms, are the functions pulled back directly. -/
lemma appTop_map_apply_of_comp_eq (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j) {k j : J} (f : k ⟶ j)
    (x : Γ(E.obj j, ⊤)) :
    (p k).appTop ((E.map f).appTop x) = (p j).appTop x := by
  rw [← hp f, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

omit [∀ j, IsAffine (E.obj j)] in
/-- Finitely many global functions on a stage which vanish on `X` vanish on some later stage. -/
lemma exists_appTop_map_eq_zero_finset (p : ∀ j, X ⟶ E.obj j)
    (hinj : ∀ (j : J) (s : Γ(E.obj j, ⊤)), (p j).appTop s = 0 →
      ∃ (k : J) (f : k ⟶ j), (E.map f).appTop s = 0)
    {j : J} {ι : Type*} (s : Finset ι) (a : ι → Γ(E.obj j, ⊤))
    (ha : ∀ i ∈ s, (p j).appTop (a i) = 0) :
    ∃ (k : J) (t : k ⟶ j), ∀ i ∈ s, (E.map t).appTop (a i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert i s hi ih =>
    obtain ⟨k₁, t₁, h₁⟩ := ih fun l hl ↦ ha l (Finset.mem_insert_of_mem hl)
    obtain ⟨k₂, t₂, h₂⟩ := hinj j (a i) (ha i (Finset.mem_insert_self i s))
    obtain ⟨k, u₁, u₂, hu⟩ := IsCofiltered.cospan t₁ t₂
    refine ⟨k, u₁ ≫ t₁, fun l hl ↦ ?_⟩
    obtain rfl | hl := Finset.mem_insert.mp hl
    · rw [hu, appTop_map_comp_apply, h₂, map_zero]
    · rw [appTop_map_comp_apply, h₁ l hl, map_zero]

omit [∀ j, IsAffine (E.obj j)] in
/-- Finitely many global functions on `X` come from global functions on a common stage, which can
be chosen below any given stage. -/
lemma exists_appTop_eq_finset (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j)
    (hsurj : ∀ s : Γ(X, ⊤), ∃ (j : J) (t : Γ(E.obj j, ⊤)), (p j).appTop t = s)
    (j : J) {ι : Type*} (s : Finset ι) (y : ι → Γ(X, ⊤)) :
    ∃ (k : J) (_ : k ⟶ j) (a : ι → Γ(E.obj k, ⊤)), ∀ i ∈ s, (p k).appTop (a i) = y i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨k₁, t₁, a, ha⟩ := ih
    obtain ⟨k₂, b, hb⟩ := hsurj (y i)
    refine ⟨IsCofiltered.min k₁ k₂, IsCofiltered.minToLeft k₁ k₂ ≫ t₁,
      fun l ↦ if l = i then (E.map (IsCofiltered.minToRight k₁ k₂)).appTop b
        else (E.map (IsCofiltered.minToLeft k₁ k₂)).appTop (a l), fun l hl ↦ ?_⟩
    obtain rfl | hl' := Finset.mem_insert.mp hl
    · simp [appTop_map_apply_of_comp_eq p hp, hb]
    · have hli : l ≠ i := by
        rintro rfl
        exact hi hl'
      simp [hli, appTop_map_apply_of_comp_eq p hp, ha l hl']

/-- **Vanishing of sections descends to a finite stage, affine case.** Finitely many global
sections of a module of finite presentation on a stage which vanish after pullback to `X` vanish
after pullback to some later stage. -/
theorem exists_pullbackΓ_eq_zero_of_colimit_appTop [IsAffine X] (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j)
    (hsurj : ∀ s : Γ(X, ⊤), ∃ (j : J) (t : Γ(E.obj j, ⊤)), (p j).appTop t = s)
    (hinj : ∀ (j : J) (s : Γ(E.obj j, ⊤)), (p j).appTop s = 0 →
      ∃ (k : J) (f : k ⟶ j), (E.map f).appTop s = 0)
    {j : J} (Q : (E.obj j).Modules) [Q.IsFinitePresentation] {ι : Type*} [Finite ι]
    (x : ι → Γ(Q, ⊤)) (hx : ∀ i, pullbackΓ (p j) Q (x i) = 0) :
    ∃ (k : J) (t : k ⟶ j), ∀ i, pullbackΓ (E.map t) Q (x i) = 0 := by
  classical
  obtain ⟨P, _, _⟩ := (Module.finitePresentation_iff_exists_presentation.{u, u}).mp
    (finitePresentation_sections_of_isFinitePresentation Q (isAffineOpen_top (E.obj j)))
  have := Fintype.ofFinite P.G
  have := Fintype.ofFinite P.R
  have := Fintype.ofFinite ι
  have hspan (m : Γ(Q, ⊤)) : m ∈ Submodule.span Γ(E.obj j, ⊤) (Set.range P.var) := by
    rw [← P.range_π, LinearMap.range_eq_top.mpr P.surjective_π]
    exact Submodule.mem_top
  choose a ha using fun i ↦ (Submodule.mem_span_range_iff_exists_fun _).mp (hspan (x i))
  have hrel (r : P.R) : ∑ g, P.relation r g • P.var g = 0 := by
    rw [← Finsupp.linearCombination_eq_sum_fintype]
    exact P.linearCombination_var_relation r
  obtain ⟨t, ht, htv⟩ := exists_isPresentation_pullbackΓ (p j) Q P.toIsPresentation
  have hker (i : ι) : Finsupp.equivFunOnFinite.symm (fun g ↦ (p j).appTop (a i g)) ∈
      Submodule.span Γ(X, ⊤) (Set.range (P.baseChange (p j).appTop.hom).relation) := by
    rw [← ht.ker_π, LinearMap.mem_ker, Module.Relations.Solution.π,
      Finsupp.linearCombination_eq_sum_fintype]
    simp only [Finsupp.coe_equivFunOnFinite_symm, htv]
    rw [← pullbackΓ_sum_smul, ha, hx]
  choose b hb using fun i ↦ (Submodule.mem_span_range_iff_exists_fun _).mp (hker i)
  have hb' (i : ι) (g : P.G) :
      ∑ r, b i r * (p j).appTop (P.relation r g) = (p j).appTop (a i g) := by
    have := congr($(hb i) g)
    simpa [Finsupp.finsetSum_apply] using this
  obtain ⟨k₁, t₁, b', hb''⟩ := exists_appTop_eq_finset p hp hsurj j
    (Finset.univ : Finset (ι × P.R)) fun x ↦ b x.1 x.2
  obtain ⟨k, t₂, hk⟩ := exists_appTop_map_eq_zero_finset p hinj
    (Finset.univ : Finset (ι × P.G)) (fun x ↦ (E.map t₁).appTop (a x.1 x.2) -
      ∑ r, b' (x.1, r) * (E.map t₁).appTop (P.relation r x.2)) (fun x _ ↦ by
        simp only [map_sub, map_sum, map_mul, appTop_map_apply_of_comp_eq p hp,
          hb'' _ (Finset.mem_univ _), hb', sub_self])
  refine ⟨k, t₂ ≫ t₁, fun i ↦ ?_⟩
  have hcoeff (g : P.G) : (E.map (t₂ ≫ t₁)).appTop (a i g) =
      ∑ r, (E.map t₂).appTop (b' (i, r)) * (E.map (t₂ ≫ t₁)).appTop (P.relation r g) := by
    have := hk (i, g) (Finset.mem_univ _)
    simp only [map_sub, map_sum, map_mul, sub_eq_zero] at this
    simp only [appTop_map_comp_apply, this]
  rw [← ha i, pullbackΓ_sum_smul]
  simp only [hcoeff, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, ← pullbackΓ_sum_smul, hrel, map_zero, smul_zero,
    Finset.sum_const_zero]

/-- Modules of finite presentation on `X` descend to a finite stage. -/
theorem exists_pullback_iso_of_colimit_appTop [IsAffine X] (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j)
    (hsurj : ∀ s : Γ(X, ⊤), ∃ (j : J) (t : Γ(E.obj j, ⊤)), (p j).appTop t = s) (M : X.Modules)
    [M.IsFinitePresentation] :
    ∃ (j : J) (N : (E.obj j).Modules), N.IsFinitePresentation ∧
      Nonempty ((Modules.pullback (p j)).obj N ≅ M) := by
  obtain ⟨P, _, _⟩ := (Module.finitePresentation_iff_exists_presentation.{u, u}).mp
    (finitePresentation_sections_of_isFinitePresentation M (isAffineOpen_top X))
  have := Fintype.ofFinite P.G
  have := Fintype.ofFinite P.R
  obtain ⟨k, -, a, ha⟩ := exists_appTop_eq_finset p hp hsurj (IsCofiltered.nonempty (C := J)).some
    (Finset.univ : Finset (P.R × P.G)) fun x ↦ P.relation x.1 x.2
  let ρ : Module.Relations.{u, u} Γ(E.obj k, ⊤) :=
    { G := P.G
      R := P.R
      relation := fun r ↦ Finsupp.equivFunOnFinite.symm fun g ↦ a (r, g) }
  have : Finite ρ.G := ‹Finite P.G›
  have : Finite ρ.R := ‹Finite P.R›
  obtain ⟨N, s, _, hs⟩ := exists_isFinitePresentation_isPresentation ρ
  obtain ⟨t, ht, -⟩ := exists_isPresentation_pullbackΓ (p k) N hs
  have hrel (r : P.R) : (ρ.baseChange (p k).appTop.hom).relation r = P.relation r := by
    ext g
    exact ha (r, g) (Finset.mem_univ _)
  obtain ⟨e, -⟩ := exists_iso_of_isPresentation (ht.ofRelationEq hrel) P.toIsPresentation
  exact ⟨k, N, inferInstance, ⟨e⟩⟩

/-- Equalities of morphisms between modules of finite presentation descend to a finite stage. -/
theorem exists_pullback_map_eq_of_colimit_appTop [IsAffine X] (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j)
    (hsurj : ∀ s : Γ(X, ⊤), ∃ (j : J) (t : Γ(E.obj j, ⊤)), (p j).appTop t = s)
    (hinj : ∀ (j : J) (s : Γ(E.obj j, ⊤)), (p j).appTop s = 0 →
      ∃ (k : J) (f : k ⟶ j), (E.map f).appTop s = 0)
    {j : J} {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (ψ₁ ψ₂ : N₁ ⟶ N₂) (h : (Modules.pullback (p j)).map ψ₁ = (Modules.pullback (p j)).map ψ₂) :
    ∃ (k : J) (t : k ⟶ j),
      (Modules.pullback (E.map t)).map ψ₁ = (Modules.pullback (E.map t)).map ψ₂ := by
  obtain ⟨P, _, _⟩ := (Module.finitePresentation_iff_exists_presentation.{u, u}).mp
    (finitePresentation_sections_of_isFinitePresentation N₁ (isAffineOpen_top (E.obj j)))
  have hx (g : P.G) :
      pullbackΓ (p j) N₂ (ψ₁.app ⊤ (P.var g) - ψ₂.app ⊤ (P.var g)) = 0 := by
    rw [map_sub, ← pullbackΓ_naturality, ← pullbackΓ_naturality, h, sub_self]
  obtain ⟨k, t, hk⟩ := exists_pullbackΓ_eq_zero_of_colimit_appTop p hp hsurj hinj N₂ _ hx
  obtain ⟨s, hs, hsv⟩ := exists_isPresentation_pullbackΓ (E.map t) N₁ P.toIsPresentation
  refine ⟨k, t, hom_ext_of_isPresentation hs fun g ↦ ?_⟩
  rw [hsv, pullbackΓ_naturality, pullbackΓ_naturality, ← sub_eq_zero, ← map_sub, hk]

/-- Morphisms between the pullbacks to `X` of modules of finite presentation descend to a finite
stage. -/
theorem exists_pullback_map_eq_of_colimit_appTop' [IsAffine X] (p : ∀ j, X ⟶ E.obj j)
    (hp : ∀ {k j : J} (f : k ⟶ j), p k ≫ E.map f = p j)
    (hsurj : ∀ s : Γ(X, ⊤), ∃ (j : J) (t : Γ(E.obj j, ⊤)), (p j).appTop t = s)
    (hinj : ∀ (j : J) (s : Γ(E.obj j, ⊤)), (p j).appTop s = 0 →
      ∃ (k : J) (f : k ⟶ j), (E.map f).appTop s = 0)
    {j : J} {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (φ : (Modules.pullback (p j)).obj N₁ ⟶ (Modules.pullback (p j)).obj N₂) :
    ∃ (k : J) (t : k ⟶ j)
      (ψ : (Modules.pullback (E.map t)).obj N₁ ⟶ (Modules.pullback (E.map t)).obj N₂),
      (pullbackCompOfEq (p k) (E.map t) (p j) (hp t) N₁).inv ≫
        (Modules.pullback (p k)).map ψ ≫
          (pullbackCompOfEq (p k) (E.map t) (p j) (hp t) N₂).hom = φ := by
  classical
  obtain ⟨P₁, _, _⟩ := (Module.finitePresentation_iff_exists_presentation.{u, u}).mp
    (finitePresentation_sections_of_isFinitePresentation N₁ (isAffineOpen_top (E.obj j)))
  obtain ⟨P₂, _, _⟩ := (Module.finitePresentation_iff_exists_presentation.{u, u}).mp
    (finitePresentation_sections_of_isFinitePresentation N₂ (isAffineOpen_top (E.obj j)))
  have := Fintype.ofFinite P₁.G
  have := Fintype.ofFinite P₁.R
  have := Fintype.ofFinite P₂.G
  have hrel (r : P₁.R) : ∑ g, P₁.relation r g • P₁.var g = 0 := by
    rw [← Finsupp.linearCombination_eq_sum_fintype]
    exact P₁.linearCombination_var_relation r
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_isPresentation_pullbackΓ (p j) N₁ P₁.toIsPresentation
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_isPresentation_pullbackΓ (p j) N₂ P₂.toIsPresentation
  have hspan (m : Γ((Modules.pullback (p j)).obj N₂, ⊤)) :
      m ∈ Submodule.span Γ(X, ⊤) (Set.range t₂.var) := by
    rw [← t₂.range_π, LinearMap.range_eq_top.mpr ht₂.surjective_π]
    exact Submodule.mem_top
  choose y hy using fun g ↦
    (Submodule.mem_span_range_iff_exists_fun _).mp (hspan (φ.app ⊤ (t₁.var g)))
  obtain ⟨k₁, u₁, a, ha⟩ := exists_appTop_eq_finset p hp hsurj j
    (Finset.univ : Finset (P₁.G × P₂.G)) fun x ↦ y x.1 x.2
  replace ha (g : P₁.G) (g' : P₂.G) : (p k₁).appTop (a (g, g')) = y g g' :=
    ha (g, g') (Finset.mem_univ _)
  let z (g : P₁.G) : Γ((Modules.pullback (E.map u₁)).obj N₂, ⊤) :=
    ∑ g', a (g, g') • pullbackΓ (E.map u₁) N₂ (P₂.var g')
  let w (r : P₁.R) : Γ((Modules.pullback (E.map u₁)).obj N₂, ⊤) :=
    ∑ g, (E.map u₁).appTop (P₁.relation r g) • z g
  have hw (r : P₁.R) : pullbackΓ (p k₁) _ (w r) = 0 := by
    have key : (pullbackCompOfEq (p k₁) (E.map u₁) (p j) (hp u₁) N₂).hom.app ⊤
        (pullbackΓ (p k₁) _ (w r)) = 0 := by
      simp only [w, z, pullbackΓ_sum_smul, Hom.app_sum_smul, pullbackCompOfEq_hom_app_pullbackΓ,
        appTop_map_apply_of_comp_eq p hp, ha]
      simp only [← ht₂v, hy]
      rw [← Hom.app_sum_smul]
      simp only [ht₁v, ← pullbackΓ_sum_smul, hrel, map_zero]
    rw [← iso_hom_app_inv_app (pullbackCompOfEq (p k₁) (E.map u₁) (p j) (hp u₁) N₂).symm ⊤
      (pullbackΓ (p k₁) _ (w r)), Iso.symm_inv, key, map_zero]
  obtain ⟨k, u₂, hk⟩ := exists_pullbackΓ_eq_zero_of_colimit_appTop p hp hsurj hinj _ w hw
  obtain ⟨s₁, hs₁, hs₁v⟩ := exists_isPresentation_pullbackΓ (E.map (u₂ ≫ u₁)) N₁
    P₁.toIsPresentation
  let sol : (P₁.baseChange (E.map (u₂ ≫ u₁)).appTop.hom).Solution
      Γ((Modules.pullback (E.map (u₂ ≫ u₁))).obj N₂, ⊤) :=
    { var g := (pullbackCompOfEq (E.map u₂) (E.map u₁) (E.map (u₂ ≫ u₁))
        (E.map_comp _ _).symm N₂).hom.app ⊤ (pullbackΓ (E.map u₂) _ (z g))
      linearCombination_var_relation r := by
        rw [Finsupp.linearCombination_eq_sum_fintype]
        refine Eq.trans ?_ (congrArg ((pullbackCompOfEq (E.map u₂) (E.map u₁) (E.map (u₂ ≫ u₁))
          (E.map_comp _ _).symm N₂).hom.app ⊤) (hk r) |>.trans (map_zero _))
        simp only [w, pullbackΓ_sum_smul, Hom.app_sum_smul, Finsupp.mapRange_apply,
          appTop_map_comp_apply] }
  obtain ⟨ψ, hψ⟩ := exists_hom_of_isPresentation hs₁ sol
  refine ⟨k, u₂ ≫ u₁, ψ, hom_ext_of_isPresentation ht₁ fun g ↦ ?_⟩
  rw [← hy g, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ht₁v, pullbackCompOfEq_inv_app_pullbackΓ, pullbackΓ_naturality,
    ← hs₁v, hψ]
  simp only [sol, z, pullbackΓ_sum_smul, Hom.app_sum_smul, pullbackCompOfEq_hom_app_pullbackΓ,
    appTop_map_apply_of_comp_eq p hp, ha, ht₂v]

end Colimit

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

/-- **Modules of finite presentation descend to a finite stage, affine case** (Stacks, Tag 01ZR).
Every module of finite presentation on the limit of a cofiltered system of affine schemes is
isomorphic to the pullback of a module of finite presentation on some stage. -/
theorem exists_pullback_iso_of_isLimit_of_isAffine (hc : IsLimit c) (M : c.pt.Modules)
    [M.IsFinitePresentation] :
    ∃ (j : J) (N : (E.obj j).Modules), N.IsFinitePresentation ∧
      Nonempty ((Modules.pullback (c.π.app j)).obj N ≅ M) :=
  have := Scheme.isAffine_of_isLimit c hc
  exists_pullback_iso_of_colimit_appTop (X := c.pt) c.π.app c.w
    (exists_appTop_π_eq_of_isAffine_of_isLimit E c hc) M

/-- **Equalities of morphisms of modules descend to a finite stage, affine case**
(Stacks, Tag 01ZR). Two morphisms between modules of finite presentation on a stage of a
cofiltered system of affine schemes which agree after pullback to the limit agree after pullback
to some later stage. -/
theorem exists_pullback_map_eq_of_isLimit_of_isAffine (hc : IsLimit c) {j : J}
    {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (ψ₁ ψ₂ : N₁ ⟶ N₂)
    (h : (Modules.pullback (c.π.app j)).map ψ₁ = (Modules.pullback (c.π.app j)).map ψ₂) :
    ∃ (k : J) (t : k ⟶ j),
      (Modules.pullback (E.map t)).map ψ₁ = (Modules.pullback (E.map t)).map ψ₂ :=
  have := Scheme.isAffine_of_isLimit c hc
  exists_pullback_map_eq_of_colimit_appTop (X := c.pt) c.π.app c.w
    (exists_appTop_π_eq_of_isAffine_of_isLimit E c hc)
    (exists_appTop_map_eq_zero_of_isAffine_of_isLimit E c hc) ψ₁ ψ₂ h

/-- **Morphisms of modules descend to a finite stage, affine case** (Stacks, Tag 01ZR). Every
morphism between the pullbacks to the limit of two modules of finite presentation on a stage of a
cofiltered system of affine schemes is the pullback of a morphism defined over some later
stage. -/
theorem exists_pullback_map_eq_of_isLimit_of_isAffine' (hc : IsLimit c) {j : J}
    {N₁ N₂ : (E.obj j).Modules} [N₁.IsFinitePresentation] [N₂.IsFinitePresentation]
    (φ : (Modules.pullback (c.π.app j)).obj N₁ ⟶ (Modules.pullback (c.π.app j)).obj N₂) :
    ∃ (k : J) (t : k ⟶ j)
      (ψ : (Modules.pullback (E.map t)).obj N₁ ⟶ (Modules.pullback (E.map t)).obj N₂),
      (pullbackCompOfEq (c.π.app k) (E.map t) (c.π.app j) (c.w t) N₁).inv ≫
        (Modules.pullback (c.π.app k)).map ψ ≫
          (pullbackCompOfEq (c.π.app k) (E.map t) (c.π.app j) (c.w t) N₂).hom = φ :=
  have := Scheme.isAffine_of_isLimit c hc
  exists_pullback_map_eq_of_colimit_appTop' (X := c.pt) c.π.app c.w
    (exists_appTop_π_eq_of_isAffine_of_isLimit E c hc)
    (exists_appTop_map_eq_zero_of_isAffine_of_isLimit E c hc) φ

end AlgebraicGeometry.Scheme.Modules
