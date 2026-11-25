/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Clearing denominators for a section of an invertible module

Let `X` be a quasi-compact scheme, separated over an affine scheme, `ℒ` an invertible
`𝒪_X`-module and `s` a global section of `ℒ`, i.e. a morphism `s: 𝒪_X ⟶ ℒ`. Let `X_s` be the
complement of the zero scheme `Z(s)`. Every section `t` of a quasi-coherent module `ℱ` over
`X_s` becomes, after multiplication by a power of `s`, the restriction of a global section:
there are `m` and `u ∈ Γ(X, ℱ ⊗ ℒ^{⊗ m})` with `u|_{X_s} = t ⊗ s^m`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.tensorPowSection`: the power `s^{⊗ m}: 𝒪_X ⟶ ℒ^{⊗ m}` of
  a global section `s: 𝒪_X ⟶ ℒ`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict`: clearing denominators.
- `AlgebraicGeometry.Scheme.Modules.exists_hom_app_eq_of_tensorPowSection`: a section `t` such
  that `t ⊗ s^m` extends globally is in the image of a morphism from an inverse of `ℒ^{⊗ m}`.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_app_one_of_le`: `s(1)` is a free generator
  away from the zero scheme of `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The `m`-th power `s^{⊗ m} : 𝒪_X ⟶ ℒ^{⊗ m}` of a global section `s : 𝒪_X ⟶ ℒ`:
`s^{⊗ 0} = 𝟙` and `s^{⊗ (m + 1)} = s ⊗ s^{⊗ m}`, precomposed with `𝒪_X ≅ 𝒪_X ⊗ 𝒪_X`. -/
noncomputable def tensorPowSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) :
    (m : ℕ) → (𝟙_ X.Modules ⟶ L.tensorPow m)
  | 0 => 𝟙 _
  | m + 1 => (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ tensorPowSection s m)

@[simp]
lemma tensorPowSection_zero {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) :
    tensorPowSection s 0 = 𝟙 _ :=
  rfl

lemma tensorPowSection_succ {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ) :
    tensorPowSection s (m + 1) = (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ tensorPowSection s m) :=
  rfl

/-- The power `s^{⊗ m}` evaluated at the section `1` over `U`. -/
noncomputable abbrev tensorPowSectionOne {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ)
    (U : X.Opens) : Γ(L.tensorPow m, U) :=
  (tensorPowSection s m).app U (unitSectionsEquiv U 1)

/-- `s^{⊗ 0}(1) = 1`. -/
lemma tensorPowSectionOne_zero {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (U : X.Opens) :
    tensorPowSectionOne s 0 U = unitSectionsEquiv U 1 :=
  rfl

/-- `s^{⊗ (m + 1)}(1) = s(1) ⊗ s^{⊗ m}(1)`. -/
lemma tensorPowSectionOne_succ {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ) (U : X.Opens) :
    tensorPowSectionOne s (m + 1) U =
      tmulSection (s.app U (unitSectionsEquiv U 1)) (tensorPowSectionOne s m U) := by
  rw [tensorPowSectionOne, tensorPowSection_succ, Hom.comp_app, ConcreteCategory.comp_apply,
    leftUnitor_inv_app]
  exact tensorHom_app_tmulSection _ _ _ _

/-- `s^{⊗ m}(1)` is compatible with restriction. -/
lemma presheaf_map_tensorPowSectionOne {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ)
    {U V : X.Opens} (i : V ⟶ U) :
    (L.tensorPow m).presheaf.map i.op (tensorPowSectionOne s m U) = tensorPowSectionOne s m V := by
  rw [tensorPowSectionOne, ← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one]

/-- If `s(1) = f • e` on `U`, then `s^{⊗ m}(1) = f ^ m • e^{⊗ m}` on `U`, for some section
`e^{⊗ m}` which is a free generator if `e` is. -/
lemma exists_tensorPowSectionOne_eq_pow_smul {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)
    {U : X.Opens} {e : Γ(L, U)} (he : IsFreeGenerator e) {f : Γ(X, U)}
    (hf : s.app U (unitSectionsEquiv U 1) = f • e) (m : ℕ) :
    ∃ E : Γ(L.tensorPow m, U), IsFreeGenerator E ∧ tensorPowSectionOne s m U = f ^ m • E := by
  induction m with
  | zero => exact ⟨_, isFreeGenerator_one U, by rw [pow_zero, one_smul]; rfl⟩
  | succ m ih =>
    obtain ⟨E, hE, hE'⟩ := ih
    refine ⟨tmulSection e E, he.tmulSection hE, ?_⟩
    rw [tensorPowSectionOne_succ, hf, hE', smul_tmulSection, tmulSection_smul, smul_smul, pow_succ']

/-- If `s(1)` is a free generator on `U`, so is `s^{⊗ m}(1)`. -/
lemma isFreeGenerator_tensorPowSectionOne {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)
    {U : X.Opens} (hs : IsFreeGenerator (s.app U (unitSectionsEquiv U 1))) (m : ℕ) :
    IsFreeGenerator (tensorPowSectionOne s m U) := by
  induction m with
  | zero => exact isFreeGenerator_one U
  | succ m ih =>
    rw [tensorPowSectionOne_succ]
    exact hs.tmulSection ih

/-- Transport of `s^{⊗ m}(1)` along an equality of exponents. -/
lemma eqToHom_app_tensorPowSectionOne {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) {m n : ℕ}
    (h : m = n) (U : X.Opens) :
    (eqToHom (congrArg L.tensorPow h)).app U (tensorPowSectionOne s m U) =
      tensorPowSectionOne s n U := by
  subst h
  rfl

/-- `s^{⊗ (a + b)}(1)` corresponds to `s^{⊗ a}(1) ⊗ s^{⊗ b}(1)` under `ℒ^{⊗ (a + b)} ≅
ℒ^{⊗ a} ⊗ ℒ^{⊗ b}`. -/
lemma tensorPowAddIso_inv_app_tmulSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (a b : ℕ)
    (U : X.Opens) :
    (L.tensorPowAddIso a b).inv.app U
        (tmulSection (tensorPowSectionOne s a U) (tensorPowSectionOne s b U)) =
      tensorPowSectionOne s (a + b) U := by
  induction a with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection _ _).trans (one_smul _ _))).trans
      (eqToHom_app_tensorPowSectionOne s (Nat.zero_add b).symm U)
  | succ a ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      tensorPowSectionOne_succ]
    have h2 : (Iso.refl L ⊗ᵢ L.tensorPowAddIso a b).inv.app U
        (tmulSection (s.app U (unitSectionsEquiv U 1))
          (tmulSection (tensorPowSectionOne s a U) (tensorPowSectionOne s b U))) =
        tmulSection (s.app U (unitSectionsEquiv U 1)) (tensorPowSectionOne s (a + b) U) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    exact (congrArg _ ((congrArg _ (associator_hom_app_tmulSection _ _ _)).trans h2)).trans
      ((congrArg _ (tensorPowSectionOne_succ s (a + b) U).symm).trans
        (eqToHom_app_tensorPowSectionOne s (Nat.succ_add a b).symm U))

/-- The section `t ⊗ s^m` of `F ⊗ ℒ^{⊗ m}`. -/
lemma rightUnitor_inv_comp_whiskerLeft_app {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ)
    (F : X.Modules) (U : X.Opens) (t : Γ(F, U)) :
    ((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app U t =
      tmulSection t (tensorPowSectionOne s m U) := by
  rw [Hom.comp_app, ConcreteCategory.comp_apply, rightUnitor_inv_app,
    whiskerLeft_app_tmulSection]

/-- Multiplication by `s^{⊗ b}`, as a morphism `F ⊗ ℒ^{⊗ a} ⟶ F ⊗ ℒ^{⊗ (a + b)}`. -/
noncomputable def mulTensorPowSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules)
    (a b : ℕ) : F ⊗ L.tensorPow a ⟶ F ⊗ L.tensorPow (a + b) :=
  (ρ_ _).inv ≫ (F ⊗ L.tensorPow a) ◁ tensorPowSection s b ≫ (α_ _ _ _).hom ≫
    F ◁ (L.tensorPowAddIso a b).inv

/-- Multiplication by `s^{⊗ b}` on sections. -/
lemma mulTensorPowSection_app {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules)
    (a b : ℕ) (U : X.Opens) (y : Γ(F ⊗ L.tensorPow a, U)) :
    (mulTensorPowSection s F a b).app U y = (F ◁ (L.tensorPowAddIso a b).inv).app U
      ((α_ F (L.tensorPow a) (L.tensorPow b)).hom.app U
        (tmulSection y (tensorPowSectionOne s b U))) := by
  rw [mulTensorPowSection, Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, rightUnitor_inv_app,
    whiskerLeft_app_tmulSection]

/-- Multiplication by `s^{⊗ b}` sends `x ⊗ s^{⊗ a}` to `x ⊗ s^{⊗ (a + b)}`. -/
lemma mulTensorPowSection_app_tmulSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)
    (F : X.Modules) (a b : ℕ) (U : X.Opens) (x : Γ(F, U)) :
    (mulTensorPowSection s F a b).app U (tmulSection x (tensorPowSectionOne s a U)) =
      tmulSection x (tensorPowSectionOne s (a + b) U) := by
  rw [mulTensorPowSection_app, associator_hom_app_tmulSection, whiskerLeft_app_tmulSection,
    tensorPowAddIso_inv_app_tmulSection]

/-- Multiplication by `s^{⊗ b}` kills sections killed by `g` if `s^{⊗ b}(1)` is a multiple
of `g`. -/
lemma mulTensorPowSection_app_eq_zero {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules)
    (a b : ℕ) {U : X.Opens} {g : Γ(X, U)} {E : Γ(L.tensorPow b, U)}
    (hE : tensorPowSectionOne s b U = g • E) {y : Γ(F ⊗ L.tensorPow a, U)} (hy : g • y = 0) :
    (mulTensorPowSection s F a b).app U y = 0 := by
  rw [mulTensorPowSection_app, hE, tmulSection_smul, ← smul_tmulSection, hy, zero_tmulSection,
    map_zero, map_zero]

/-- On an affine open `V` on which `ℒ` has a free generator `e`, with `s(1) = f • e`, the
non-vanishing locus `X_s` of `s` meets `V` in `D(f)`. -/
lemma basicOpen_coeff_eq {L : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : 𝟙_ X.Modules ⟶ L) (V : X.affineOpens) {e : Γ(L, V.1)} (he : IsFreeGenerator e) :
    X.basicOpen (he.coeff (s.app V.1 (unitSectionsEquiv _ 1))) =
      V.1 ⊓ (Hom.zeroLocus s).support.compl := by
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  ext x
  have key (hx : x ∈ V.1) : x ∈ (Hom.zeroLocus s).support ↔
      x ∉ X.basicOpen (he.coeff (s.app V.1 (unitSectionsEquiv _ 1))) := by
    rw [IdealSheafData.mem_support_iff_of_mem hx,
      Hom.ideal_zeroLocus s V (isFreeGenerator_one _) he
        (he.coeff_smul _).symm, zeroLocus_span, mem_zeroLocus_iff]
    simp
    rfl
  constructor
  · intro hx
    have hxV : x ∈ V.1 := X.basicOpen_le _ hx
    exact ⟨hxV, fun hs ↦ (key hxV).1 hs hx⟩
  · rintro ⟨hxV, hxs⟩
    by_contra h
    exact hxs ((key hxV).2 h)

/-- **A section is a free generator where it does not vanish.** If `U` does not meet the zero
scheme of `s : 𝒪_X ⟶ ℒ`, then `s(1)` is a free generator of `ℒ` on `U`. -/
lemma isFreeGenerator_app_one_of_le {L : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : 𝟙_ X.Modules ⟶ L) {U : X.Opens} (hU : U ≤ (Hom.zeroLocus s).support.compl) :
    IsFreeGenerator (s.app U (unitSectionsEquiv U 1)) := by
  let S : Sieve U := {
    arrows V' _ := ∃ (V : X.affineOpens) (e : Γ(L, V.1)), IsFreeGenerator e ∧ V' ≤ V.1
    downward_closed := fun ⟨V, e, he, h⟩ g ↦ ⟨V, e, he, (leOfHom g).trans h⟩ }
  refine isFreeGenerator_of_mem _ (S := S) (fun x hx ↦ ?_) fun V' i ⟨V, e, he, hV'V⟩ ↦ ?_
  · obtain ⟨V, hxV, hVU, e, he⟩ := exists_isFreeGenerator L hx
    exact ⟨V.1, homOfLE hVU, ⟨V, e, he, le_rfl⟩, hxV⟩
  · set c := he.coeff (s.app V.1 (unitSectionsEquiv _ 1))
    have hV'D : V' ≤ X.basicOpen c := by
      rw [basicOpen_coeff_eq s V he]
      exact le_inf hV'V ((leOfHom i).trans hU)
    have hc : IsUnit (X.presheaf.map (homOfLE hV'V).op c) := by
      have h2 : X.presheaf.map (homOfLE hV'D).op
          (X.presheaf.map (homOfLE (X.basicOpen_le c)).op c) =
          X.presheaf.map (homOfLE hV'V).op c :=
        Scheme.presheaf_map_map_apply _ _ _
      rw [← h2]
      exact (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map (homOfLE hV'D).op).hom
    rw [← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one,
      ← map_one (X.presheaf.map (homOfLE hV'V).op).hom, ← presheaf_map_unitSectionsEquiv,
      Hom.app_presheaf_map, ← he.coeff_smul (s.app V.1 (unitSectionsEquiv _ 1)), map_smul]
    obtain ⟨g, hg⟩ := hc
    rw [← hg]
    exact (he.map hV'V).units_smul g

/-- **Clearing denominators for a section of an invertible module.** Let `X` be a quasi-compact
scheme, separated over an affine scheme `S`, let `ℒ` be an invertible `𝒪_X`-module and
`s: 𝒪_X ⟶ ℒ` a global section of `ℒ`, and let `X_s` be the complement of the zero scheme
`Z(s)`. For every quasi-coherent `𝒪_X`-module `ℱ` and every `t ∈ Γ(X_s, ℱ)` there are `m ≥ 0`
and `u ∈ Γ(X, ℱ ⊗ ℒ^{⊗ m})` with `u|_{X_s} = t ⊗ s^m`.

Here `t ⊗ s^m` is the image of `t` under `ℱ ≅ ℱ ⊗ 𝒪_X ⟶ ℱ ⊗ ℒ^{⊗ m}`, the second map being
`ℱ ◁ s^{⊗ m}`. -/
@[stacks 01PW]
theorem exists_tensorPowSection_eq_restrict {S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsAffine S] [CompactSpace X] (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    (t : Γ(F, (Hom.zeroLocus s).support.compl)) :
    ∃ (m : ℕ) (u : Γ(F ⊗ L.tensorPow m, ⊤)),
      (F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u =
        ((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app _ t := by
  classical
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  generalize hXs : (Hom.zeroLocus s).support.compl = Xs at t ⊢
  have hcov (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧ ∃ e : Γ(L, V.1), IsFreeGenerator e := by
    obtain ⟨V, hx, -, he⟩ := exists_isFreeGenerator L (x := x) (W := ⊤) trivial
    exact ⟨V, hx, he⟩
  choose V hxV e he using hcov
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((V x).1 : Set X))
    (fun x ↦ (V x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let ι := {x // x ∈ T}
  let W : ι → X.Opens := fun j ↦ (V j.1).1
  have hW (j : ι) : IsAffineOpen (W j) := (V j.1).2
  have hcover : ⊤ ≤ iSup W := by
    intro x _
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  let fc : ∀ j : ι, Γ(X, W j) := fun j ↦ (he j.1).coeff (s.app (W j) (unitSectionsEquiv _ 1))
  have hfc (j : ι) : s.app (W j) (unitSectionsEquiv _ 1) = fc j • e j.1 :=
    ((he j.1).coeff_smul _).symm
  have hD (j : ι) : X.basicOpen (fc j) = W j ⊓ Xs := by
    rw [← hXs]
    exact basicOpen_coeff_eq s (V j.1) (he j.1)
  have hDle (j : ι) : X.basicOpen (fc j) ≤ Xs := (hD j).le.trans inf_le_right
  -- Step 1: lift `t` on each `D(f_j)` to `W j` after multiplying by a power of `f_j`.
  have hlift (j : ι) := exists_map_eq_pow_smul_of_isAffineOpen F (hW j) (fc j)
    (F.presheaf.map (homOfLE (hDle j)).op t)
  choose n t₀ ht₀ using hlift
  let a := Finset.univ.sup n
  have hna (j : ι) : n j ≤ a := Finset.le_sup (Finset.mem_univ j)
  let t₁ : ∀ j : ι, Γ(F, W j) := fun j ↦ fc j ^ (a - n j) • t₀ j
  have ht₁ (j : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (fc j))).op (t₁ j) =
      X.presheaf.map (homOfLE (X.basicOpen_le (fc j))).op (fc j) ^ a •
        F.presheaf.map (homOfLE (hDle j)).op t := by
    rw [map_smul, ht₀, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel (hna j)]
  choose E hE hE' using fun (j : ι) (m : ℕ) ↦
    exists_tensorPowSectionOne_eq_pow_smul s (he j.1) (hfc j) m
  let u₁ : ∀ j : ι, Γ(F ⊗ L.tensorPow a, W j) := fun j ↦ tmulSection (t₁ j) (E j a)
  have hu₁ (j : ι) {P : X.Opens} (hP : P ≤ X.basicOpen (fc j)) :
      (F ⊗ L.tensorPow a).presheaf.map (homOfLE (hP.trans (X.basicOpen_le _))).op (u₁ j) =
        tmulSection (F.presheaf.map (homOfLE (hP.trans (hDle j))).op t)
          (tensorPowSectionOne s a P) := by
    rw [tmulSection_map, ← presheaf_map_homOfLE_map_homOfLE (X.basicOpen_le (fc j)) hP (t₁ j), ht₁,
      map_smul, map_pow, presheaf_map_homOfLE_map_homOfLE,
      ← presheaf_map_tensorPowSectionOne s a (homOfLE (hP.trans (X.basicOpen_le _))), hE',
      map_smul, map_pow, tmulSection_smul, smul_tmulSection, Scheme.presheaf_map_map_apply]
    rfl
  -- Step 2: on overlaps, the `u₁ j` agree after multiplication by a power of `f_j`.
  have hover (j k : ι) : ∃ b : ℕ,
      X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j) ^ b •
        ((F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
          (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)) = 0 := by
    set g := X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j)
    set d := (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
      (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)
    have hg : X.basicOpen g = (W j ⊓ W k) ⊓ X.basicOpen (fc j) := X.basicOpen_res _ _
    have hPj : X.basicOpen g ≤ X.basicOpen (fc j) := hg.le.trans inf_le_right
    have hPk : X.basicOpen g ≤ X.basicOpen (fc k) := by
      rw [hD k]
      refine le_inf ((X.basicOpen_le g).trans inf_le_right) (hPj.trans (hDle j))
    have hd0 : (F ⊗ L.tensorPow a).presheaf.map (homOfLE (X.basicOpen_le g)).op d = 0 := by
      rw [map_sub, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE, hu₁ j hPj,
        hu₁ k hPk]
      exact sub_self _
    obtain ⟨d', hd'⟩ := ((hE j a).bijective_tmulSection_right
      (inf_le_left : W j ⊓ W k ≤ W j)).2 d
    dsimp only at hd'
    have hd'0 : F.presheaf.map (homOfLE (X.basicOpen_le g)).op d' = 0 := by
      apply ((hE j a).bijective_tmulSection_right ((X.basicOpen_le g).trans inf_le_left)).1
      dsimp only
      rw [zero_tmulSection, ← presheaf_map_homOfLE_map_homOfLE inf_le_left (X.basicOpen_le g),
        ← tmulSection_map, hd', hd0]
    obtain ⟨b, hb⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F ((hW j).inf (hW k)) g d' hd'0
    refine ⟨b, ?_⟩
    rw [← hd', ← smul_tmulSection, hb, zero_tmulSection]
  choose b hb using hover
  -- Step 3: multiply by `s^{⊗ b}` and glue.
  let b' := Finset.univ.sup fun p : ι × ι ↦ b p.1 p.2
  have hbb (j k : ι) : b j k ≤ b' := Finset.le_sup (f := fun p : ι × ι ↦ b p.1 p.2)
    (Finset.mem_univ (j, k))
  let ν := mulTensorPowSection s F a b'
  let v : ∀ j : ι, Γ(F ⊗ L.tensorPow (a + b'), W j) := fun j ↦ ν.app (W j) (u₁ j)
  let 𝓕 : TopCat.Sheaf Ab X :=
    ⟨(F ⊗ L.tensorPow (a + b')).presheaf, (F ⊗ L.tensorPow (a + b')).isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible 𝓕.1 W v := by
    intro j k
    rw [← sub_eq_zero]
    have key : ν.app (W j ⊓ W k)
        ((F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_left).op (u₁ j) -
          (F ⊗ L.tensorPow a).presheaf.map (homOfLE inf_le_right).op (u₁ k)) = 0 := by
      refine mulTensorPowSection_app_eq_zero s F a b'
        (g := X.presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op (fc j) ^ b')
        (E := (L.tensorPow b').presheaf.map (homOfLE (inf_le_left : W j ⊓ W k ≤ W j)).op
          (E j b')) ?_ ?_
      · rw [← presheaf_map_tensorPowSectionOne s b' (homOfLE inf_le_left), hE', map_smul,
          map_pow]
      · rw [← Nat.sub_add_cancel (hbb j k), pow_add, mul_smul, hb, smul_zero]
    rw [map_sub, Hom.app_presheaf_map, Hom.app_presheaf_map] at key
    exact key
  obtain ⟨u, hu, -⟩ := 𝓕.existsUnique_gluing' W ⊤ (fun j ↦ homOfLE le_top) hcover v hcompat
  refine ⟨a + b', u, ?_⟩
  rw [rightUnitor_inv_comp_whiskerLeft_app]
  refine 𝓕.eq_of_locally_eq' (fun j ↦ W j ⊓ Xs) Xs (fun j ↦ homOfLE inf_le_right) ?_ _ _
    fun j ↦ ?_
  · intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcover (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj, hx⟩
  · have hu' : (F ⊗ L.tensorPow (a + b')).presheaf.map (homOfLE (le_top : W j ≤ ⊤)).op u =
        v j := hu j
    refine (presheaf_map_homOfLE_map_homOfLE _ _ _).trans
      ((presheaf_map_homOfLE_map_homOfLE le_top inf_le_left u).symm.trans ?_)
    rw [hu', ← Hom.app_presheaf_map, hu₁ j (hD j).ge, mulTensorPowSection_app_tmulSection,
      tmulSection_map, presheaf_map_tensorPowSectionOne]

/-- Let `s` be a section of `ℒ` which generates `ℒ` on `U`, and let `ℒ^{⊗ m} ⊗ D ≅ 𝒪_X`. If a
section `t` of `F` over `U` is such that `t ⊗ s^m` extends to a global section `u` of
`F ⊗ ℒ^{⊗ m}`, then `t` is in the image of a morphism `D ⟶ F` on sections over `U`: namely of
`D ≅ 𝒪_X ⊗ D ⟶ (F ⊗ ℒ^{⊗ m}) ⊗ D ≅ F ⊗ (ℒ^{⊗ m} ⊗ D) ≅ F`, the middle map being `u`. -/
theorem exists_hom_app_eq_of_tensorPowSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L)
    {U : X.Opens} (hs : IsFreeGenerator (s.app U (unitSectionsEquiv U 1))) (m : ℕ)
    {D F : X.Modules} (c : L.tensorPow m ⊗ D ≅ 𝟙_ X.Modules) (t : Γ(F, U))
    (u : Γ(F ⊗ L.tensorPow m, ⊤))
    (hu : (F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u =
      ((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app U t) :
    ∃ (φ : D ⟶ F) (w : Γ(D, U)), φ.app U w = t := by
  obtain ⟨w, hw⟩ := ((bijective_app_of_iso c U).comp
    ((isFreeGenerator_tensorPowSectionOne s hs m).bijective_tmulSection_left (N := D) le_rfl)).2
      (unitSectionsEquiv U 1)
  rw [Function.comp_apply, presheaf_map_id_apply] at hw
  -- `homOfGlobalSection` has source `Modules.unit X`, which is `𝟙_ X.Modules` only up to
  -- unfolding the monoidal structure, so we evaluate its whiskering by hand.
  have h₁ : (homOfGlobalSection _ u ▷ D).app U (tmulSection (unitSectionsEquiv U 1) w) =
      tmulSection ((F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u) w :=
    (whiskerRight_app_tmulSection _ _ _).trans
      (congrArg (tmulSection · w) (homOfGlobalSection_app_one _ u U))
  refine ⟨(λ_ D).inv ≫ homOfGlobalSection _ u ▷ D ≫ (α_ F (L.tensorPow m) D).hom ≫
    F ◁ c.hom ≫ (ρ_ F).hom, w, ?_⟩
  rw [Hom.comp_app, Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    leftUnitor_inv_app]
  refine (congrArg (fun z ↦ (ρ_ F).hom.app U ((F ◁ c.hom).app U
    ((α_ F (L.tensorPow m) D).hom.app U z))) h₁).trans ?_
  rw [hu, rightUnitor_inv_comp_whiskerLeft_app, associator_hom_app_tmulSection,
    whiskerLeft_app_tmulSection, hw, rightUnitor_hom_app_tmulSection',
    LinearEquiv.symm_apply_apply, one_smul]

end AlgebraicGeometry.Scheme.Modules
