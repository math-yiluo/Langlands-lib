/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections

/-!
# Morphisms to projective space given by linear combinations of sections

Let `ψ : Z ⟶ ℙ(m; S)` and `χ : Z ⟶ ℙ(n; S)` be morphisms over `S` given by families of global
sections `u` and `v` of one module `L` on `Z`, i.e. `ψ^* 𝒪(1) ≅ L` sends `ψ^* T_q` to `u q`, and
similarly for `χ` and `v`. If every `v l` is a linear combination of the `u q` with coefficients
from `Γ(S)`, then `χ` is, on the image of `ψ`, the composite of `ψ` with a linear projection
`ℙ(m; S) ⇢ ℙ(n; S)`. We do not construct the projection; we only prove the consequence that if
`χ` is a monomorphism, then so is `ψ`.

On the chart `ψ⁻¹ D₊(T_q)` the section `v l` is `ψ^* A_{ql} • u q` for the function
`A_{ql} = ∑_r c_{lr} T_r / T_q` on `D₊(T_q)`, so `v l` generates `L` exactly on
`ψ⁻¹ D(A_{ql})`, which is therefore contained in `χ⁻¹ D₊(T_l)`; there `χ` pulls `T_r / T_l` back
to `ψ^*(A_{qr} / A_{ql})`. Hence two morphisms `a, b : T ⟶ Z` with `a ≫ ψ = b ≫ ψ` satisfy
`a ≫ χ = b ≫ χ` on each of the opens `(a ≫ ψ)⁻¹ D(A_{ql})`, which cover `T`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.generatingLocus_eq_preimage_standardOpen`: if
  `φ^* 𝒪(1) ≅ M` sends `φ^* Tᵢ` to `s i`, then `s i` generates `M` exactly on `φ⁻¹ D₊(Tᵢ)`.
- `AlgebraicGeometry.ProjectiveSpace.hom_ext_of_preimage_standardOpen_eq_top`: over an affine
  base, morphisms into the chart `D₊(Tᵢ)` are determined by the ratios `Tⱼ / Tᵢ`.
- `AlgebraicGeometry.ProjectiveSpace.mono_of_eq_sum_smul`: the monomorphism criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

section Sections

variable {X S : Scheme.{u}} {n : Type u} {M : X.Modules} {s : n → Γ(M, ⊤)}
  {φ : X ⟶ ℙ(n; S)} (ε : twistRestrict φ 1 ⟶ M) [IsIso ε]
  (hε : ∀ j, ε.app _ (pullbackSection φ (twistOneSection n S j)) =
    M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j))
include hε

/-- If `φ^* 𝒪(1) ≅ M` sends `φ^* Tᵢ` to `s i`, then `s i` generates `M` exactly on the preimage
of the standard open `D₊(Tᵢ)`. -/
lemma generatingLocus_eq_preimage_standardOpen (i : n) :
    generatingLocus (s i) = φ ⁻¹ᵁ standardOpen n S i := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦
    ⟨_, hx, isFreeGenerator_of_twistRestrict_iso ε hε i⟩
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((iSup_standardOpen n S).ge (Set.mem_univ (φ x)))
  have hx' := mem_basicOpen_of_generatesAt (isFreeGenerator_of_twistRestrict_iso ε hε j)
    (map_eq_coordRatio_smul_of_twistRestrict_iso ε hε j i) hj hx
  rw [← Scheme.preimage_basicOpen] at hx'
  exact basicOpen_coordRatio_le S j i hx'

end Sections

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- **Morphisms into a standard chart are determined by the ratios.** Over an affine base `S`,
two morphisms `W ⟶ ℙ(n; S)` landing in the standard open `D₊(Tᵢ)`, with the same composite to
`S` and pulling back every ratio `Tⱼ / Tᵢ` to the same function, are equal. -/
lemma hom_ext_of_preimage_standardOpen_eq_top {S : Scheme.{u}} [IsAffine S] {n : Type u}
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ ℙ(n; S)} (i : n)
    (h₁ : f₁ ⁻¹ᵁ standardOpen n S i = ⊤) (h₂ : f₂ ⁻¹ᵁ standardOpen n S i = ⊤)
    (hS : f₁ ≫ ℙ(n; S) ↘ S = f₂ ≫ ℙ(n; S) ↘ S)
    (hr : ∀ j, f₁.appLE (standardOpen n S i) ⊤ h₁.ge (coordRatio n S i j) =
      f₂.appLE (standardOpen n S i) ⊤ h₂.ge (coordRatio n S i j)) : f₁ = f₂ := by
  have : IsAffine (standardOpen n S i).toScheme := isAffineOpen_standardOpen n S i
  have key : f₁.appLE (standardOpen n S i) ⊤ h₁.ge = f₂.appLE (standardOpen n S i) ⊤ h₂.ge := by
    ext1
    refine RingHom.eq_of_eqOn_set_dense (closure_range_appLE_union_range_coordRatio S i) ?_
    rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
    · change ((ℙ(n; S) ↘ S).appLE ⊤ _ le_top ≫ f₁.appLE _ ⊤ h₁.ge) c =
        ((ℙ(n; S) ↘ S).appLE ⊤ _ le_top ≫ f₂.appLE _ ⊤ h₂.ge) c
      erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      rw [appLE_eq_of_eq hS]
    · exact hr j
  have hres : f₁.resLE (standardOpen n S i) ⊤ h₁.ge = f₂.resLE (standardOpen n S i) ⊤ h₂.ge :=
    ext_of_isAffine (by
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
        Scheme.Hom.resLE_app_top, key])
  rw [← cancel_epi W.topIso.hom, Scheme.topIso_hom, ← Scheme.Hom.resLE_comp_ι f₁ h₁.ge,
    ← Scheme.Hom.resLE_comp_ι f₂ h₂.ge, hres]

private lemma appLE_eq_map_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    f.appLE U V e x = X.presheaf.map (homOfLE e).op (f.app U x) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

section Mono

variable {S Z : Scheme.{u}} {g : Z ⟶ S} {L : Z.Modules} {m n : Type u} [Fintype m]
  {u : m → Γ(L, ⊤)} {v : n → Γ(L, ⊤)} (c : n → m → Γ(S, ⊤))
  {ψ : Z ⟶ ℙ(m; S)} {χ : Z ⟶ ℙ(n; S)}
  (εψ : twistRestrict ψ 1 ⟶ L) [IsIso εψ]
  (hεψ : ∀ q, εψ.app _ (pullbackSection ψ (twistOneSection m S q)) =
    L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op (u q))
  (εχ : twistRestrict χ 1 ⟶ L) [IsIso εχ]
  (hεχ : ∀ l, εχ.app _ (pullbackSection χ (twistOneSection n S l)) =
    L.presheaf.map (homOfLE (le_top : χ ⁻¹ᵁ ⊤ ≤ ⊤)).op (v l))

/-- The linear form `∑_r c_{lr} T_r`, divided by `T_q`, as a function on `D₊(T_q)`. -/
def linearRatio (q : m) (l : n) : Γ(ℙ(m; S), standardOpen m S q) :=
  ∑ r, (ℙ(m; S) ↘ S).appLE ⊤ (standardOpen m S q) le_top (c l r) * coordRatio m S q r

omit [IsIso εψ] in
include hεψ in
/-- On `ψ⁻¹ D₊(T_q)`, a linear combination `v l = ∑_r c_{lr} u r` is `ψ^* A_{ql} • u q`. -/
lemma map_eq_linearRatio_smul (hψ : ψ ≫ ℙ(m; S) ↘ S = g)
    (hv : ∀ l, v l = ∑ r, g.appTop (c l r) • u r) (q : m) (l : n) :
    L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ standardOpen m S q ≤ ⊤)).op (v l) =
      ψ.app (standardOpen m S q) (linearRatio c q l) •
        L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ standardOpen m S q ≤ ⊤)).op (u q) := by
  rw [hv, map_sum, linearRatio, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Scheme.Modules.map_smul, map_eq_coordRatio_smul_of_twistRestrict_iso εψ hεψ q r, smul_smul,
    map_mul]
  congr 2
  conv_rhs => rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]; erw [
    Scheme.Hom.appLE_comp_appLE]; rw [appLE_eq_of_eq hψ]
  exact (appLE_eq_map_app g ⊤ _ _ _).symm

variable {c} (hψ : ψ ≫ ℙ(m; S) ↘ S = g) (hv : ∀ l, v l = ∑ r, g.appTop (c l r) • u r)
include hεψ hεχ hψ hv

/-- The opens `ψ⁻¹ D(A_{ql})` cover `Z`. -/
lemma exists_mem_preimage_basicOpen_linearRatio (x : Z) :
    ∃ q l, x ∈ ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l) := by
  obtain ⟨q, hq⟩ := Opens.mem_iSup.mp ((iSup_standardOpen m S).ge (Set.mem_univ (ψ x)))
  obtain ⟨l, hl⟩ := Opens.mem_iSup.mp ((iSup_standardOpen n S).ge (Set.mem_univ (χ x)))
  have hgen : GeneratesAt (v l) x := by
    rw [← mem_generatingLocus, generatingLocus_eq_preimage_standardOpen εχ hεχ l]
    exact hl
  refine ⟨q, l, ?_⟩
  rw [Scheme.preimage_basicOpen]
  exact mem_basicOpen_of_generatesAt (isFreeGenerator_of_twistRestrict_iso εψ hεψ q)
    (map_eq_linearRatio_smul c εψ hεψ hψ hv q l) hq hgen

/-- `χ` maps `ψ⁻¹ D(A_{ql})` into `D₊(T_l)`. -/
lemma preimage_basicOpen_linearRatio_le (q : m) (l : n) :
    ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l) ≤ χ ⁻¹ᵁ standardOpen n S l := by
  intro x hx
  rw [Scheme.preimage_basicOpen] at hx
  have h := generatesAt_of_mem_basicOpen (isFreeGenerator_of_twistRestrict_iso εψ hεψ q)
    (map_eq_linearRatio_smul c εψ hεψ hψ hv q l) hx
  rw [← mem_generatingLocus, generatingLocus_eq_preimage_standardOpen εχ hεχ l] at h
  exact h

/-- On `ψ⁻¹ D(A_{ql})`, the morphism `χ` pulls `T_r / T_l` back to `ψ^*(A_{qr} / A_{ql})`. -/
lemma appLE_coordRatio_mul_appLE_linearRatio (q : m) (l : n) (r : n) :
    χ.appLE (standardOpen n S l) (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l))
        (preimage_basicOpen_linearRatio_le εψ hεψ εχ hεχ hψ hv q l) (coordRatio n S l r) *
      ψ.appLE (standardOpen m S q) (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l))
        (ψ.preimage_mono (ℙ(m; S).basicOpen_le _)) (linearRatio c q l) =
      ψ.appLE (standardOpen m S q) (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l))
        (ψ.preimage_mono (ℙ(m; S).basicOpen_le _)) (linearRatio c q r) := by
  have hYq : ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l) ≤ ψ ⁻¹ᵁ standardOpen m S q :=
    ψ.preimage_mono (ℙ(m; S).basicOpen_le _)
  have hYl := preimage_basicOpen_linearRatio_le εψ hεψ εχ hεχ hψ hv q l
  refine ((isFreeGenerator_of_twistRestrict_iso εψ hεψ q).map hYq).smul_left_injective ?_
  dsimp only
  rw [mul_smul, appLE_eq_map_app ψ, appLE_eq_map_app ψ, appLE_eq_map_app χ,
    ← Scheme.Modules.map_smul, ← map_eq_linearRatio_smul c εψ hεψ hψ hv q l,
    ← Scheme.Modules.map_smul, ← map_eq_linearRatio_smul c εψ hεψ hψ hv q r,
    presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE,
    ← presheaf_map_homOfLE_map_homOfLE (le_top : χ ⁻¹ᵁ standardOpen n S l ≤ ⊤) hYl,
    ← presheaf_map_homOfLE_map_homOfLE (le_top : χ ⁻¹ᵁ standardOpen n S l ≤ ⊤) hYl (v r),
    map_eq_coordRatio_smul_of_twistRestrict_iso εχ hεχ l r, Scheme.Modules.map_smul]

/-- **The monomorphism criterion.** Let `ψ : Z ⟶ ℙ(m; S)` and `χ : Z ⟶ ℙ(n; S)` be morphisms
over an affine scheme `S`, given by global sections `u` and `v` of a module `L`, i.e.
`ψ^* 𝒪(1) ≅ L` sends `ψ^* T_q` to `u q`, and `χ^* 𝒪(1) ≅ L` sends `χ^* T_l` to `v l`. If every
`v l = ∑_r c_{lr} • u r` is a linear combination of the `u r` with coefficients from `Γ(S)`
and `χ` is a monomorphism, then so is `ψ`: on the opens `ψ⁻¹ D(A_{ql})` covering `Z`, the
morphism `χ` is determined by `ψ`. -/
theorem mono_of_eq_sum_smul [IsAffine S] (hχ : χ ≫ ℙ(n; S) ↘ S = g) [Mono χ] : Mono ψ := by
  refine ⟨fun {T} a b hab ↦ ?_⟩
  rw [← cancel_mono χ]
  let O (p : m × n) : T.Opens := (a ≫ ψ) ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c p.1 p.2)
  have hO : ⨆ p, O p = ⊤ := eq_top_iff.mpr fun t _ ↦ by
    obtain ⟨q, l, h⟩ := exists_mem_preimage_basicOpen_linearRatio εψ hεψ εχ hεχ hψ hv (a t)
    exact Opens.mem_iSup.mpr ⟨(q, l), h⟩
  refine Scheme.Opens.hom_ext_of_iSup_eq_top O hO _ _ fun ⟨q, l⟩ ↦ ?_
  have hYl := preimage_basicOpen_linearRatio_le εψ hεψ εχ hεχ hψ hv q l
  have hYq : ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l) ≤ ψ ⁻¹ᵁ standardOpen m S q :=
    ψ.preimage_mono (ℙ(m; S).basicOpen_le _)
  rw [← Category.assoc, ← Category.assoc]
  set a' := (O (q, l)).ι ≫ a
  set b' := (O (q, l)).ι ≫ b
  have hab' : a' ≫ ψ = b' ≫ ψ := by simp only [a', b', Category.assoc, hab]
  have haY : ⊤ ≤ a' ⁻¹ᵁ (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l)) := fun t _ ↦ t.2
  have hbY : ⊤ ≤ b' ⁻¹ᵁ (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l)) := by
    rw [← Scheme.Hom.comp_preimage, ← hab', Scheme.Hom.comp_preimage]
    exact haY
  have h₁ : (a' ≫ χ) ⁻¹ᵁ standardOpen n S l = ⊤ := eq_top_iff.mpr fun t ht ↦ hYl (haY ht)
  have h₂ : (b' ≫ χ) ⁻¹ᵁ standardOpen n S l = ⊤ := eq_top_iff.mpr fun t ht ↦ hYl (hbY ht)
  refine hom_ext_of_preimage_standardOpen_eq_top l h₁ h₂ (by
    simp only [a', b', Category.assoc, hχ, ← hψ, reassoc_of% hab])
    fun r ↦ ?_
  -- the relation `χ^*(T_r / T_l) * ψ^* A_{ql} = ψ^* A_{qr}`, pulled back along `a'` and `b'`
  have key (f : (O (q, l)).toScheme ⟶ Z) (hf : ⊤ ≤ f ⁻¹ᵁ
      (ψ ⁻¹ᵁ ℙ(m; S).basicOpen (linearRatio c q l))) (r' : n) :
      (f ≫ χ).appLE (standardOpen n S l) ⊤ (hf.trans (f.preimage_mono hYl))
          (coordRatio n S l r) *
        (f ≫ ψ).appLE (standardOpen m S q) ⊤ (hf.trans (f.preimage_mono hYq))
          (linearRatio c q l) =
        (f ≫ ψ).appLE (standardOpen m S q) ⊤ (hf.trans (f.preimage_mono hYq))
          (linearRatio c q r) := by
    have h := congrArg (f.appLE _ ⊤ hf)
      (appLE_coordRatio_mul_appLE_linearRatio εψ hεψ εχ hεχ hψ hv q l r)
    rw [map_mul] at h
    simpa only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] using h
  have hunit : IsUnit ((a' ≫ ψ).appLE (standardOpen m S q) ⊤ (haY.trans (a'.preimage_mono hYq))
      (linearRatio c q l)) := by
    have hle : ⊤ ≤ (O (q, l)).toScheme.basicOpen
        ((a' ≫ ψ).app (standardOpen m S q) (linearRatio c q l)) := by
      rw [← Scheme.preimage_basicOpen]
      exact haY
    rw [appLE_eq_map_app]
    have e : (O (q, l)).toScheme.presheaf.map (homOfLE (haY.trans (a'.preimage_mono hYq) :
          ⊤ ≤ (a' ≫ ψ) ⁻¹ᵁ standardOpen m S q)).op =
        (O (q, l)).toScheme.presheaf.map (homOfLE ((O (q, l)).toScheme.basicOpen_le _)).op ≫
          (O (q, l)).toScheme.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]
      rfl
    rw [e, CommRingCat.comp_apply]
    exact ((O (q, l)).toScheme.toRingedSpace.isUnit_res_basicOpen _).map _
  have ha := key a' haY r
  have hb := key b' hbY r
  rw [appLE_eq_of_eq hab'.symm] at hb
  exact hunit.mul_right_cancel (ha.trans hb.symm)

end Mono

section BaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S S' W X : Scheme.{u}} {m : Type u} (gS : S' ⟶ S) (φ : W ⟶ X) {M : X.Modules}
  {u : m → Γ(M, ⊤)} {j : X ⟶ ℙ(m; S)} (εj : twistRestrict j 1 ⟶ M) [IsIso εj]
  (hεj : ∀ q, εj.app _ (pullbackSection j (twistOneSection m S q)) =
    M.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ ⊤ ≤ ⊤)).op (u q))
  {ψ : W ⟶ ℙ(m; S')} (εψ : twistRestrict ψ 1 ⟶ (Scheme.Modules.pullback φ).obj M) [IsIso εψ]
  (hεψ : ∀ q, εψ.app _ (pullbackSection ψ (twistOneSection m S' q)) =
    ((Scheme.Modules.pullback φ).obj M).presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op
      (pullbackTopSection φ (u q)))
include hεj hεψ

/-- **Base change of a morphism given by sections.** Let `j : X ⟶ ℙ(m; S)` be given by global
sections `u` of a module `M`, and `ψ : W ⟶ ℙ(m; S')` by their pullbacks along `φ : W ⟶ X`. If
`ψ` and `φ ≫ j` agree over `S`, for a morphism `S' ⟶ S` to an affine scheme, then `ψ` is a
lift of `φ ≫ j` along the base change morphism `ℙ(m; S') ⟶ ℙ(m; S)`. -/
theorem map_comp_eq_of_pullbackTopSection [IsAffine S]
    (h : ψ ≫ ℙ(m; S') ↘ S' ≫ gS = φ ≫ j ≫ ℙ(m; S) ↘ S) : ψ ≫ map m gS = φ ≫ j := by
  let O (q : m) : W.Opens := φ ⁻¹ᵁ (j ⁻¹ᵁ standardOpen m S q)
  have hO : ⨆ q, O q = ⊤ := eq_top_iff.mpr fun x _ ↦ by
    obtain ⟨q, hq⟩ := Opens.mem_iSup.mp ((iSup_standardOpen m S).ge (Set.mem_univ (j (φ x))))
    exact Opens.mem_iSup.mpr ⟨q, hq⟩
  refine Scheme.Opens.hom_ext_of_iSup_eq_top O hO _ _ fun q ↦ ?_
  have hOψ : O q ≤ ψ ⁻¹ᵁ standardOpen m S' q := by
    rw [← generatingLocus_eq_preimage_standardOpen εψ hεψ q]
    refine le_trans (le_of_eq ?_) (preimage_generatingLocus_le φ (u q))
    rw [generatingLocus_eq_preimage_standardOpen εj hεj q]
  have hpre : map m gS ⁻¹ᵁ standardOpen m S q = standardOpen m S' q := by
    have := Scheme.Hom.comp_preimage (map m gS) (toProjInt m S)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule m (ULift.{u} ℤ)) (MvPolynomial.X q))
    rw [map_toProjInt] at this
    exact this.symm
  have hOι : ⊤ ≤ (O q).ι ⁻¹ᵁ O q := fun x _ ↦ x.2
  -- the ratios `Tᵣ / T_q` pulled back to `O q` along both morphisms agree
  have key (r : m) : ψ.appLE (standardOpen m S' q) (O q) hOψ (coordRatio m S' q r) =
      φ.appLE (j ⁻¹ᵁ standardOpen m S q) (O q) le_rfl
        (j.app (standardOpen m S q) (coordRatio m S q r)) := by
    refine ((isFreeGenerator_of_twistRestrict_iso εψ hεψ q).map hOψ).smul_left_injective ?_
    dsimp only
    conv_lhs => rw [appLE_eq_map_app, ← Scheme.Modules.map_smul,
      ← map_eq_coordRatio_smul_of_twistRestrict_iso εψ hεψ q r, presheaf_map_homOfLE_map_homOfLE]
    rw [presheaf_map_homOfLE_map_homOfLE, ← Scheme.Hom.app_eq_appLE,
      pullbackTopSection_map (V := j ⁻¹ᵁ standardOpen m S q),
      pullbackTopSection_map (V := j ⁻¹ᵁ standardOpen m S q), ← pullbackSection_smul,
      ← map_eq_coordRatio_smul_of_twistRestrict_iso εj hεj q r]
  have hD : ⊤ ≤ ((O q).ι ≫ φ ≫ j) ⁻¹ᵁ standardOpen m S q := fun x _ ↦ x.2
  refine hom_ext_of_preimage_standardOpen_eq_top q ?_ (eq_top_iff.mpr hD) ?_ fun r ↦ ?_
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    change ψ x.1 ∈ map m gS ⁻¹ᵁ standardOpen m S q
    rw [hpre]
    exact hOψ x.2
  · simp only [Category.assoc, map_over]
    rw [h]
  · have e₁ (e) : ((O q).ι ≫ ψ ≫ map m gS).appLE (standardOpen m S q) ⊤ e
        (coordRatio m S q r) = (O q).ι.appLE (O q) ⊤ hOι
          (ψ.appLE (standardOpen m S' q) (O q) hOψ (coordRatio m S' q r)) := by
      rw [← map_appLE_coordRatio gS q r hpre.ge]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    have e₂ (e) : ((O q).ι ≫ φ ≫ j).appLE (standardOpen m S q) ⊤ e (coordRatio m S q r) =
        (O q).ι.appLE (O q) ⊤ hOι (φ.appLE (j ⁻¹ᵁ standardOpen m S q) (O q) le_rfl
          (j.app (standardOpen m S q) (coordRatio m S q r))) := by
      rw [Scheme.Hom.app_eq_appLE]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rw [e₁, e₂, key r]

end BaseChange

end AlgebraicGeometry.ProjectiveSpace
