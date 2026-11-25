/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Coordinate covers: line bundles with trivialising sections

A *coordinate cover* of a scheme `X`, indexed by `ι`, is an open cover `(Uᵢ)` of `X` together
with functions `tᵢⱼ ∈ Γ(X, Uᵢ)`, thought of as the ratios `Tⱼ / Tᵢ` of sections `Tᵢ` of an
invertible module `L` with `Uᵢ = X_{Tᵢ}`, subject to `tᵢᵢ = 1`, `D(tᵢⱼ) = Uᵢ ∩ Uⱼ` and the
cocycle condition `tᵢₗ = tᵢⱼ tⱼₗ` on `Uᵢ ∩ Uⱼ`. A morphism `X ⟶ ℙ(ι; S)` gives a coordinate cover
by pulling back the standard charts, and conversely a coordinate cover glues to a morphism
`X ⟶ ℙ(ι; S)`.

A *section of degree `n`* of a coordinate cover is a family `sᵢ ∈ Γ(X, Uᵢ)` with
`sᵢ = tᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`, i.e. a section `s = sᵢ Tᵢⁿ` of `L^{⊗ n}` written in the
trivialisations. Families of sections of the same degree that generate the unit ideal on every
`Uᵢ` define morphisms to projective space (`AlgebraicGeometry.Scheme.CoordinateCover.hom`).

The main technical result is the extension lemma
`AlgebraicGeometry.Scheme.CoordinateCover.exists_section`: on a coordinate cover by quasi-compact
quasi-separated opens, every function `h` on a chart `U_{i₀}` is, after multiplication by a power
of `T_{i₀}`, the restriction of a section, which can moreover be chosen to vanish outside `U_{i₀}`.
This is the standard fact (Stacks, Tag 01PW) that sections of powers of `L` over `X_s` extend
after multiplication by a power of `s`.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover`: a coordinate cover.
- `AlgebraicGeometry.Scheme.CoordinateCover.Section`: sections of degree `n`.
- `AlgebraicGeometry.Scheme.CoordinateCover.hom`: the morphism to projective space defined by a
  family of sections.
- `AlgebraicGeometry.Scheme.CoordinateCover.sigma`: coordinate covers of the members of a
  disjoint open cover glue.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.preimage_hom_standardOpen`: the preimage of the
  standard open `D₊(Tₐ)` under the morphism defined by sections `σ` is the locus `X_{σₐ}`.
- `AlgebraicGeometry.Scheme.CoordinateCover.exists_section`: the extension lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- A *coordinate cover* of a scheme `X` indexed by `ι`: an open cover `(Uᵢ)` with functions
`tᵢⱼ ∈ Γ(X, Uᵢ)` (the ratios `Tⱼ / Tᵢ` of trivialising sections of an invertible module) such
that `tᵢᵢ = 1`, `D(tᵢⱼ) = Uᵢ ∩ Uⱼ` and `tᵢₗ = tᵢⱼ tⱼₗ` on `Uᵢ ∩ Uⱼ`. -/
structure Scheme.CoordinateCover (X : Scheme.{u}) (ι : Type u) where
  /-- The charts. -/
  U : ι → X.Opens
  /-- The ratio `Tⱼ / Tᵢ`, a function on the chart `Uᵢ`. -/
  ratio (i j : ι) : Γ(X, U i)
  ratio_self (i : ι) : ratio i i = 1
  basicOpen_ratio (i j : ι) : X.basicOpen (ratio i j) = U i ⊓ U j
  ratio_mul (i j l : ι) :
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i l) =
      X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (ratio i j) *
        X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (ratio j l)
  iSup_U : ⨆ i, U i = ⊤

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}} {ι : Type u} (𝒟 : X.CoordinateCover ι)

lemma isUnit_ratio_map (i j : ι) :
    IsUnit (X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (𝒟.ratio i j)) :=
  X.isUnit_map_of_le_basicOpen _ (𝒟.basicOpen_ratio i j).ge

/-- A *section of degree `n`* of a coordinate cover: functions `sᵢ ∈ Γ(X, Uᵢ)` with
`sᵢ = tᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`, i.e. the section `sᵢ Tᵢⁿ` of the `n`-th power of the underlying
invertible module. -/
@[ext]
structure Section (n : ℕ) where
  /-- The section on the chart `Uᵢ`, written in the trivialisation `Tᵢⁿ`. -/
  s (i : ι) : Γ(X, 𝒟.U i)
  s_eq (i j : ι) :
    X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (s i) =
      X.presheaf.map (homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i)).op (𝒟.ratio i j) ^ n *
        X.presheaf.map (homOfLE (inf_le_right : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U j)).op (s j)

variable {𝒟}

namespace Section

/-- The product of sections of degrees `m` and `n`, a section of degree `m + n`. -/
def mul {m n : ℕ} (σ : 𝒟.Section m) (τ : 𝒟.Section n) : 𝒟.Section (m + n) where
  s i := σ.s i * τ.s i
  s_eq i j := by
    rw [map_mul, map_mul, σ.s_eq i j, τ.s_eq i j, pow_add]
    ring

@[simp]
lemma mul_s {m n : ℕ} (σ : 𝒟.Section m) (τ : 𝒟.Section n) (i : ι) :
    (σ.mul τ).s i = σ.s i * τ.s i := rfl

/-- The locus `X_σ` where a section does not vanish. -/
def nonvanishing {n : ℕ} (σ : 𝒟.Section n) : X.Opens :=
  ⨆ i, X.basicOpen (σ.s i)

lemma basicOpen_inf_le {n : ℕ} (σ : 𝒟.Section n) (i j : ι) :
    X.basicOpen (σ.s i) ⊓ 𝒟.U j ≤ X.basicOpen (σ.s j) := by
  have h := congrArg X.basicOpen (σ.s_eq i j)
  rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    X.basicOpen_of_isUnit ((𝒟.isUnit_ratio_map i j).pow n)] at h
  intro x ⟨hxi, hxj⟩
  have hx : x ∈ (𝒟.U i ⊓ 𝒟.U j) ⊓ X.basicOpen (σ.s i) := ⟨⟨X.basicOpen_le _ hxi, hxj⟩, hxi⟩
  rw [h] at hx
  exact hx.2.2

/-- On the chart `Uⱼ`, the locus where `σ` does not vanish is the basic open of `σⱼ`. -/
lemma nonvanishing_inf {n : ℕ} (σ : 𝒟.Section n) (j : ι) :
    σ.nonvanishing ⊓ 𝒟.U j = X.basicOpen (σ.s j) := by
  refine le_antisymm ?_ (le_inf (le_iSup (fun i ↦ X.basicOpen (σ.s i)) j) (X.basicOpen_le _))
  rw [nonvanishing, iSup_inf_eq]
  exact iSup_le fun i ↦ σ.basicOpen_inf_le i j

end Section

/-- The coordinate section `Tₗ`, of degree one. -/
def coord (l : ι) : 𝒟.Section 1 where
  s i := 𝒟.ratio i l
  s_eq i j := by rw [pow_one, 𝒟.ratio_mul]

@[simp]
lemma coord_s (l i : ι) : (𝒟.coord l).s i = 𝒟.ratio i l := rfl

/-- The `n`-th power `Tₗⁿ` of a coordinate section. -/
def coordPow (l : ι) : (n : ℕ) → 𝒟.Section n
  | 0 => ⟨fun _ ↦ 1, fun i j ↦ by simp⟩
  | n + 1 => (coordPow l n).mul (𝒟.coord l)

@[simp]
lemma coordPow_s (l : ι) (n : ℕ) (i : ι) : (𝒟.coordPow l n).s i = 𝒟.ratio i l ^ n := by
  induction n with
  | zero => simp [coordPow]
  | succ n ih => simp [coordPow, ih, pow_succ]

section Hom

variable {α : Type u} {N : ℕ} (σ : α → 𝒟.Section N)
  (hσ : ∀ i, Ideal.span (Set.range fun a ↦ (σ a).s i) = ⊤) {S : Scheme.{u}} (g : X ⟶ S)

include hσ in
lemma span_topIso_inv (i : ι) :
    Ideal.span (Set.range fun a ↦ (𝒟.U i).topIso.inv ((σ a).s i)) = ⊤ := by
  have := Ideal.map_span (𝒟.U i).topIso.inv.hom (Set.range fun a ↦ (σ a).s i)
  rw [hσ i, Ideal.map_top, ← Set.range_comp] at this
  exact this.symm

/-- The morphism on the chart `Uᵢ` defined by the sections `σ`. -/
def localHom (i : ι) : (𝒟.U i).toScheme ⟶ ℙ(α; S) :=
  ProjectiveSpace.homOfSections ((𝒟.U i).ι ≫ g) (fun a ↦ (𝒟.U i).topIso.inv ((σ a).s i))
    (span_topIso_inv σ hσ i)

lemma homOfLE_localHom {V : X.Opens} (i : ι) (h : V ≤ 𝒟.U i) :
    X.homOfLE h ≫ localHom σ hσ g i = ProjectiveSpace.homOfSections (V.ι ≫ g)
      (fun a ↦ V.topIso.inv (X.presheaf.map (homOfLE h).op ((σ a).s i)))
      (by
        have := ProjectiveSpace.span_range_appTop_eq_top (X.homOfLE h) (span_topIso_inv σ hσ i)
        simp only [Scheme.homOfLE_appTop_topIso_inv] at this
        exact this) := by
  rw [localHom, ProjectiveSpace.comp_homOfSections]
  congr 1
  · simp
  · funext a
    exact Scheme.homOfLE_appTop_topIso_inv _ _

lemma localHom_compat (i j : ι) :
    X.homOfLE (inf_le_left : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U i) ≫ localHom σ hσ g i =
      X.homOfLE (inf_le_right : 𝒟.U i ⊓ 𝒟.U j ≤ 𝒟.U j) ≫ localHom σ hσ g j := by
  rw [homOfLE_localHom, homOfLE_localHom]
  obtain ⟨u, hu⟩ := (𝒟.isUnit_ratio_map i j).pow N
  refine (ProjectiveSpace.homOfSections_eq_of_unit_mul _
    ((Units.map (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom.toMonoidHom u)⁻¹) _ _ fun a ↦ ?_)
  rw [Units.eq_inv_mul_iff_mul_eq, Units.coe_map]
  change (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _ * (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _ =
    (𝒟.U i ⊓ 𝒟.U j).topIso.inv.hom _
  rw [← map_mul, hu, ← (σ a).s_eq]

/-- **The morphism to projective space defined by sections.** A family `σ` of sections of the
same degree of a coordinate cover, generating the unit ideal on every chart, defines a morphism
`X ⟶ ℙ(α; S)` over `g`, given on the chart `Uᵢ` by the functions `σₐ,ᵢ`. -/
def hom : X ⟶ ℙ(α; S) :=
  Scheme.Opens.glueMorphismsOfTop 𝒟.U 𝒟.iSup_U (localHom σ hσ g) (localHom_compat σ hσ g)

@[reassoc (attr := simp)]
lemma ι_hom (i : ι) : (𝒟.U i).ι ≫ hom σ hσ g = localHom σ hσ g i :=
  Scheme.Opens.ι_glueMorphismsOfTop _ _ _ _ i

@[reassoc (attr := simp)]
lemma hom_over : hom σ hσ g ≫ ℙ(α; S) ↘ S = g :=
  Scheme.Opens.hom_ext_of_iSup_eq_top 𝒟.U 𝒟.iSup_U _ _ fun i ↦ by
    rw [ι_hom_assoc, localHom, ProjectiveSpace.homOfSections_over]

/-- The preimage of the standard open `D₊(Tₐ)` under the morphism defined by the sections `σ` is
the locus where `σₐ` does not vanish. -/
lemma preimage_hom_standardOpen (a : α) :
    hom σ hσ g ⁻¹ᵁ ProjectiveSpace.standardOpen α S a = (σ a).nonvanishing := by
  have key (i : ι) : (𝒟.U i).ι ''ᵁ ((𝒟.U i).ι ⁻¹ᵁ (hom σ hσ g ⁻¹ᵁ
      ProjectiveSpace.standardOpen α S a)) = X.basicOpen ((σ a).s i) := by
    rw [← Scheme.Hom.comp_preimage, ι_hom, localHom,
      ProjectiveSpace.homOfSections_preimage_standardOpen,
      Scheme.Opens.ι_image_basicOpen_topIso_inv]
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (𝒟.iSup_U.ge (Set.mem_univ x))
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [← key i]
    exact ⟨⟨x, hi⟩, hx, rfl⟩
  · refine iSup_le fun i ↦ ?_
    rw [← key i]
    exact Scheme.Hom.image_preimage_le _ _

end Hom

section Extension

variable (𝒟)

/-- Auxiliary pointwise data for the extension lemma: on each chart `Uₗ`, a function
`eₗ` restricting to `h tₗᵢ₀ᵐ` on `Uₗ ∩ U_{i₀}`, for a common exponent `m`. -/
lemma exists_extension_aux [Finite ι] (hU : ∀ i, IsCompact (𝒟.U i : Set X))
    (hU' : ∀ i, IsQuasiSeparated (𝒟.U i : Set X)) (i₀ : ι) (h : Γ(X, 𝒟.U i₀)) :
    ∃ (m : ℕ) (e : ∀ l, Γ(X, 𝒟.U l)), ∀ l,
      X.presheaf.map (homOfLE (X.basicOpen_le (𝒟.ratio l i₀))).op (e l) =
        X.presheaf.map (homOfLE ((𝒟.basicOpen_ratio l i₀).le.trans inf_le_right)).op h *
          X.presheaf.map (homOfLE (X.basicOpen_le (𝒟.ratio l i₀))).op (𝒟.ratio l i₀) ^ m := by
  have := Fintype.ofFinite ι
  have H (l : ι) := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (𝒟.U l) (hU l) (hU' l)
    (𝒟.ratio l i₀)
    (X.presheaf.map (homOfLE ((𝒟.basicOpen_ratio l i₀).le.trans inf_le_right)).op h)
  choose n y hy using H
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at hy
  refine ⟨Finset.univ.sup n, fun l ↦ y l * 𝒟.ratio l i₀ ^ (Finset.univ.sup n - n l),
    fun l ↦ ?_⟩
  rw [map_mul, hy, map_pow, mul_comm _ (X.presheaf.map _ h), mul_assoc, ← pow_add,
    Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ l))]

/-- **The extension lemma** (Stacks, Tag 01PW). Let `𝒟` be a coordinate cover by finitely many
quasi-compact quasi-separated charts. For every function `h` on a chart `U_{i₀}` there is `N₀`
such that for all `N ≥ N₀` there is a section `σ` of degree `N` with `σ_{i₀} = h` that vanishes
outside `U_{i₀}`. -/
theorem exists_section [Finite ι] (hU : ∀ i, IsCompact (𝒟.U i : Set X))
    (hU' : ∀ i, IsQuasiSeparated (𝒟.U i : Set X)) (i₀ : ι) (h : Γ(X, 𝒟.U i₀)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ σ : 𝒟.Section N, σ.s i₀ = h ∧ σ.nonvanishing ≤ 𝒟.U i₀ := by
  have := Fintype.ofFinite ι
  obtain ⟨m, e, he⟩ := 𝒟.exists_extension_aux hU hU' i₀ h
  -- the defect of compatibility on `Uₗ ∩ Uₗ'` vanishes on `Uₗ ∩ Uₗ' ∩ U_{i₀}`
  have hV (l l' : ι) : IsCompact ((𝒟.U l ⊓ 𝒟.U l' : X.Opens) : Set X) := by
    rw [← 𝒟.basicOpen_ratio l l']
    exact isCompact_basicOpen X (hU l) _
  have Hδ (l l' : ι) : ∃ p : ℕ,
      X.presheaf.map (homOfLE (inf_le_left : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l)).op (𝒟.ratio l i₀) ^ p *
        (X.presheaf.map (homOfLE (inf_le_left : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l)).op (e l) -
          X.presheaf.map (homOfLE (inf_le_left : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l)).op
            (𝒟.ratio l l') ^ m *
          X.presheaf.map (homOfLE (inf_le_right : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l')).op (e l')) =
        0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (hV l l') _ _ ?_
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    set W := X.basicOpen
      (X.presheaf.map (homOfLE (inf_le_left : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l)).op (𝒟.ratio l i₀))
    have hW : W = 𝒟.U l ⊓ 𝒟.U l' ⊓ 𝒟.U i₀ := by
      simp only [W, Scheme.basicOpen_res, 𝒟.basicOpen_ratio]
      rw [inf_comm (𝒟.U l), inf_assoc, inf_assoc, ← inf_assoc (𝒟.U l), inf_idem, inf_comm]
    have hWl : W ≤ X.basicOpen (𝒟.ratio l i₀) := by
      rw [hW, 𝒟.basicOpen_ratio]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hWl' : W ≤ X.basicOpen (𝒟.ratio l' i₀) := by
      rw [hW, 𝒟.basicOpen_ratio]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hel := congrArg (X.presheaf.map (homOfLE hWl).op) (he l)
    have hel' := congrArg (X.presheaf.map (homOfLE hWl').op) (he l')
    have hr := congrArg (X.presheaf.map (homOfLE (X.basicOpen_le _ :
      W ≤ 𝒟.U l ⊓ 𝒟.U l')).op) (𝒟.ratio_mul l l' i₀)
    simp only [map_mul, map_pow, Scheme.presheaf_map_map] at hel hel' hr
    simp only [map_sub, map_mul, map_pow, Scheme.presheaf_map_map]
    rw [hel, hel', hr]
    ring
  choose p hp using Hδ
  set P := Finset.univ.sup fun ll : ι × ι ↦ p ll.1 ll.2
  have hP (l l' : ι) := Finset.le_sup (f := fun ll : ι × ι ↦ p ll.1 ll.2)
    (Finset.mem_univ (l, l'))
  refine ⟨m + P + 1, fun N hN ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  let σ : 𝒟.Section (m + P + 1) :=
    { s := fun l ↦ e l * 𝒟.ratio l i₀ ^ (P + 1)
      s_eq := fun l l' ↦ by
        have hδ := hp l l'
        have hr := 𝒟.ratio_mul l l' i₀
        obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hP l l')
        simp only [map_mul, map_pow]
        rw [hr] at hδ ⊢
        rw [show P = p l l' + q from hq]
        linear_combination (X.presheaf.map (homOfLE (inf_le_left : 𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l)).op
          (𝒟.ratio l l') * X.presheaf.map (homOfLE (inf_le_right :
            𝒟.U l ⊓ 𝒟.U l' ≤ 𝒟.U l')).op (𝒟.ratio l' i₀)) ^ (q + 1) * hδ }
  have hσ : σ.nonvanishing ≤ 𝒟.U i₀ := iSup_le fun l ↦ by
    change X.basicOpen (e l * 𝒟.ratio l i₀ ^ (P + 1)) ≤ _
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ P.succ_pos, 𝒟.basicOpen_ratio]
    exact inf_le_right.trans inf_le_right
  have hσ₀ : σ.s i₀ = h := by
    change e i₀ * 𝒟.ratio i₀ i₀ ^ (P + 1) = h
    rw [𝒟.ratio_self, one_pow, mul_one]
    have e₀ : X.basicOpen (𝒟.ratio i₀ i₀) = 𝒟.U i₀ := by rw [𝒟.ratio_self, X.basicOpen_one]
    refine X.eq_of_map_eq_of_eq e₀ ?_
    have := he i₀
    simp only [𝒟.ratio_self, map_one, one_pow, mul_one] at this
    exact this
  refine ⟨σ.mul (𝒟.coordPow i₀ k), ?_, ?_⟩
  · simp [hσ₀, 𝒟.ratio_self]
  · refine iSup_le fun l ↦ ?_
    rw [Section.mul_s, Scheme.basicOpen_mul]
    exact inf_le_left.trans ((le_iSup (fun l ↦ X.basicOpen (σ.s l)) l).trans hσ)

end Extension

section OfSections

variable {α : Type u} {N : ℕ} (σ : α → 𝒟.Section N) (c : α → ι)
  (hc : ∀ a, (σ a).nonvanishing ≤ 𝒟.U (c a)) (hcov : ⨆ a, (σ a).nonvanishing = ⊤)

include hc in
lemma nonvanishing_eq_basicOpen (a : α) :
    (σ a).nonvanishing = X.basicOpen ((σ a).s (c a)) := by
  rw [← (σ a).nonvanishing_inf (c a), inf_eq_left.mpr (hc a)]

lemma isUnit_map_s (a : α) : IsUnit (X.presheaf.map (homOfLE (hc a)).op ((σ a).s (c a))) :=
  X.isUnit_map_of_le_basicOpen _ (nonvanishing_eq_basicOpen σ c hc a).le

/-- The coordinate cover by the non-vanishing loci `X_{σₐ}` of finitely many sections of the same
degree, each contained in a chart `U_{c a}`, with the ratios `σ_b / σₐ`. -/
def ofSections : X.CoordinateCover α where
  U a := (σ a).nonvanishing
  ratio a b := X.presheaf.map (homOfLE (hc a)).op ((σ b).s (c a)) * ↑(isUnit_map_s σ c hc a).unit⁻¹
  ratio_self a := IsUnit.mul_val_inv _
  basicOpen_ratio a b := by
    have key := ((σ b).nonvanishing_inf (c a)).symm
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _), Scheme.basicOpen_res]
    apply le_antisymm
    · rintro x ⟨⟨hxa, hxB⟩, -⟩
      exact ⟨hxa, (key.le hxB).1⟩
    · rintro x ⟨hxa, hxb⟩
      exact ⟨⟨hxa, key.ge ⟨hxb, hc a hxa⟩⟩, hxa⟩
  ratio_mul a b d := by
    set W := (σ a).nonvanishing ⊓ (σ b).nonvanishing
    have hWa : W ≤ 𝒟.U (c a) := inf_le_left.trans (hc a)
    have hWb : W ≤ 𝒟.U (c b) := inf_le_right.trans (hc b)
    have hWab : W ≤ 𝒟.U (c a) ⊓ 𝒟.U (c b) := le_inf hWa hWb
    have hs (τ : 𝒟.Section N) := congrArg (X.presheaf.map (homOfLE hWab).op) (τ.s_eq (c a) (c b))
    simp only [map_mul, map_pow, Scheme.presheaf_map_map] at hs
    have hva := congrArg (X.presheaf.map (homOfLE (inf_le_left :
      W ≤ (σ a).nonvanishing)).op) (isUnit_map_s σ c hc a).mul_val_inv
    have hvb := congrArg (X.presheaf.map (homOfLE (inf_le_right :
      W ≤ (σ b).nonvanishing)).op) (isUnit_map_s σ c hc b).mul_val_inv
    simp only [map_mul, map_one, Scheme.presheaf_map_map] at hva hvb ⊢
    rw [hs (σ d), hs (σ b)]
    linear_combination (-(X.presheaf.map (homOfLE (hWab.trans inf_le_left)).op
      (𝒟.ratio (c a) (c b)) ^ N * X.presheaf.map (homOfLE hWb).op ((σ d).s (c b)) *
      X.presheaf.map (homOfLE (inf_le_left : W ≤ (σ a).nonvanishing)).op
        ↑(isUnit_map_s σ c hc a).unit⁻¹)) * hvb
  iSup_U := hcov

@[simp]
lemma ofSections_U (a : α) : (ofSections σ c hc hcov).U a = (σ a).nonvanishing := rfl

end OfSections

section Sigma

variable {X : Scheme.{u}} {κ : Type u} (V : κ → X.Opens) {ι : κ → Type u}
  (𝒟 : ∀ c, (V c).toScheme.CoordinateCover (ι c))

lemma _root_.AlgebraicGeometry.Scheme.Opens.image_ι_inf (W : X.Opens) (A B : W.toScheme.Opens) :
    W.ι ''ᵁ (A ⊓ B) = W.ι ''ᵁ A ⊓ W.ι ''ᵁ B :=
  Opens.ext (Set.image_inter W.ι.isOpenEmbedding.injective)

/-- Sections over an open in the image of an open immersion are determined by their pullbacks. -/
lemma _root_.AlgebraicGeometry.Scheme.Opens.eq_of_ι_app_eq (W : X.Opens) {O : X.Opens}
    (hO : O ≤ W) {s t : Γ(X, O)} (h : W.ι.app O s = W.ι.app O t) : s = t := by
  have : IsIso (W.ι.app O) := W.ι.isIso_app O (by rwa [Scheme.Opens.opensRange_ι])
  exact (ConcreteCategory.bijective_of_isIso (W.ι.app O)).1 h

/-- The ratios of the glued coordinate cover: the ratios of `𝒟 c` within the chart `c`, and `0`
between charts of different members of the cover. -/
noncomputable def sigmaRatio :
    (a b : Σ c, ι c) → Γ(X, (V a.1).ι ''ᵁ (𝒟 a.1).U a.2)
  | ⟨c, i⟩, ⟨c', j⟩ =>
    open Classical in
    if h : c' = c then ((V c).ι.appIso _).inv ((𝒟 c).ratio i (h ▸ j)) else 0

lemma sigmaRatio_mk (c : κ) (i j : ι c) :
    sigmaRatio V 𝒟 ⟨c, i⟩ ⟨c, j⟩ = ((V c).ι.appIso _).inv ((𝒟 c).ratio i j) := by
  simp [sigmaRatio]

lemma sigmaRatio_of_ne {a b : Σ c, ι c} (h : b.1 ≠ a.1) : sigmaRatio V 𝒟 a b = 0 := by
  obtain ⟨c, i⟩ := a
  obtain ⟨c', j⟩ := b
  simp [sigmaRatio, h]

lemma basicOpen_appIso_inv (W : X.Opens) (A : W.toScheme.Opens) (r : Γ(W.toScheme, A)) :
    X.basicOpen ((W.ι.appIso A).inv r) = W.ι ''ᵁ (W.toScheme.basicOpen r) := by
  have h1 : X.basicOpen ((W.ι.appIso A).inv r) ≤ W.ι.opensRange :=
    (X.basicOpen_le _).trans (W.ι.image_le_image_iff A ⊤ |>.mpr le_top |>.trans
      (W.ι.image_top_eq_opensRange).le)
  calc X.basicOpen ((W.ι.appIso A).inv r)
      _ = W.ι ''ᵁ (W.ι ⁻¹ᵁ X.basicOpen ((W.ι.appIso A).inv r)) :=
        ((W.ι.image_preimage_eq_opensRange_inf _).trans (inf_eq_right.mpr h1)).symm
      _ = W.ι ''ᵁ (W.toScheme.basicOpen r) := by
        congr 1
        rw [Scheme.preimage_basicOpen, Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_res]
        simp [Scheme.basicOpen_le]


lemma ι_app_map_appIso_inv (W : X.Opens) {A : W.toScheme.Opens} {O : X.Opens}
    (g : O ⟶ W.ι ''ᵁ A) (r : Γ(W.toScheme, A)) :
    W.ι.app O (X.presheaf.map g.op ((W.ι.appIso A).inv r)) =
      W.toScheme.presheaf.map (homOfLE (by
        simpa [Scheme.Hom.preimage_image_eq] using W.ι.preimage_mono g.le)).op r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, ← CommRingCat.comp_apply,
    ← Category.assoc, Scheme.Hom.appIso_inv_app, ← Functor.map_comp]
  rfl
variable (hV : Pairwise (Function.onFun Disjoint V)) (hcov : ⨆ c, V c = ⊤)

include hV in
lemma inf_eq_bot_of_ne {a b : Σ c, ι c} (h : b.1 ≠ a.1) :
    (V a.1).ι ''ᵁ (𝒟 a.1).U a.2 ⊓ (V b.1).ι ''ᵁ (𝒟 b.1).U b.2 = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf (Scheme.Opens.ι_image_le _ _) (Scheme.Opens.ι_image_le _ _)).trans
    (hV (Ne.symm h)).le_bot)

/-- **Gluing coordinate covers over a disjoint open cover.** If `X` is the disjoint union of
opens `V c`, coordinate covers `𝒟 c` of the `V c` glue to a coordinate cover of `X`, whose
charts are the charts of the `𝒟 c`. -/
noncomputable def sigma : X.CoordinateCover (Σ c, ι c) where
  U a := (V a.1).ι ''ᵁ (𝒟 a.1).U a.2
  ratio := sigmaRatio V 𝒟
  ratio_self a := by
    obtain ⟨c, i⟩ := a
    rw [sigmaRatio_mk, ratio_self, map_one]
  basicOpen_ratio a b := by
    obtain ⟨c, i⟩ := a
    obtain ⟨c', j⟩ := b
    by_cases h : c' = c
    · subst h
      rw [sigmaRatio_mk, basicOpen_appIso_inv, basicOpen_ratio, Scheme.Opens.image_ι_inf]
    · rw [sigmaRatio_of_ne V 𝒟 h, Scheme.basicOpen_zero]
      exact (inf_eq_bot_of_ne V 𝒟 hV h).symm
  ratio_mul a b l := by
    by_cases hab : b.1 = a.1
    · obtain ⟨c, i⟩ := a
      obtain ⟨c', j⟩ := b
      have hab' : c' = c := hab
      subst c'
      by_cases hl : l.1 = c
      · obtain ⟨c'', k⟩ := l
        have hl' : c'' = c := hl
        subst c''
        rw [sigmaRatio_mk, sigmaRatio_mk, sigmaRatio_mk]
        refine Scheme.Opens.eq_of_ι_app_eq (V c) (inf_le_left.trans
          (Scheme.Opens.ι_image_le _ _)) ?_
        have := congrArg ((V c).toScheme.presheaf.map (eqToHom (show (V c).ι ⁻¹ᵁ
            ((V c).ι ''ᵁ (𝒟 c).U i ⊓ (V c).ι ''ᵁ (𝒟 c).U j) = (𝒟 c).U i ⊓ (𝒟 c).U j by
          rw [← Scheme.Opens.image_ι_inf, Scheme.Hom.preimage_image_eq])).op)
          ((𝒟 c).ratio_mul i j k)
        rw [map_mul, ι_app_map_appIso_inv, ι_app_map_appIso_inv, ι_app_map_appIso_inv]
        simp only [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
        exact this
      · rw [sigmaRatio_of_ne V 𝒟 (a := ⟨c, i⟩) hl, sigmaRatio_of_ne V 𝒟 (a := ⟨c, j⟩) hl, map_zero,
          map_zero, mul_zero]
    · have h0 := inf_eq_bot_of_ne V 𝒟 hV hab
      have : ∀ O : X.Opens, O = ⊥ → Subsingleton Γ(X, O) := by
        rintro O rfl
        infer_instance
      exact (this _ h0).elim _ _
  iSup_U := by
    rw [eq_top_iff, ← hcov, iSup_le_iff]
    intro c
    rw [← Scheme.Opens.opensRange_ι (V c), ← Scheme.Hom.image_top_eq_opensRange, ← (𝒟 c).iSup_U,
      Scheme.Hom.image_iSup]
    exact iSup_le fun i ↦ le_iSup (fun a : Σ c, ι c ↦ (V a.1).ι ''ᵁ (𝒟 a.1).U a.2) ⟨c, i⟩

lemma sigma_U (a : Σ c, ι c) : (sigma V 𝒟 hV hcov).U a = (V a.1).ι ''ᵁ (𝒟 a.1).U a.2 := rfl

end Sigma

end Scheme.CoordinateCover

namespace Proj

open HomogeneousLocalization

variable {σ' : Type u} {A : Type u} [CommRing A] [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜] {d : ℕ} {f g h : A}

/-- The ratio `g / f` of two homogeneous elements of the same degree, a function on the basic
open `D₊(f)` of `Proj 𝒜`. -/
def ratio (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) : Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  awayToSection 𝒜 f (Away.mk 𝒜 hf 1 g (by simpa using hg))

@[simp]
lemma ratio_self (hf : f ∈ 𝒜 d) : ratio 𝒜 hf hf = 1 := by
  simp [ratio, Away.mk_self]

lemma basicOpen_ratio (hd : 0 < d) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) :
    (Proj 𝒜).basicOpen (ratio 𝒜 hf hg) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g := by
  have e : (⊤ : (Spec (.of (Away 𝒜 f))).Opens) ≤ awayι 𝒜 f hf hd ⁻¹ᵁ basicOpen 𝒜 f := by
    rw [← opensRange_awayι 𝒜 f hf hd]; exact (Scheme.Hom.preimage_opensRange _).ge
  have h₁ : awayι 𝒜 f hf hd ⁻¹ᵁ (Proj 𝒜).basicOpen (ratio 𝒜 hf hg) =
      awayι 𝒜 f hf hd ⁻¹ᵁ basicOpen 𝒜 g := by
    have := Scheme.basicOpen_appLE (awayι 𝒜 f hf hd) ⊤ (basicOpen 𝒜 f) e (ratio 𝒜 hf hg)
    rw [top_inf_eq] at this
    rw [← this, awayι_preimage_basicOpen 𝒜 hf hd hg hd]
    have h2 := ConcreteCategory.congr_hom (awayToSection_awayι_appLE 𝒜 hf hd)
      (Away.mk 𝒜 hf 1 g (by simpa using hg))
    rw [CommRingCat.comp_apply] at h2
    rw [ratio, h2, basicOpen_eq_of_affine]
    have hpow : (Away.mk 𝒜 hf 1 g (by simpa using hg)) ^ d =
        Away.isLocalizationElem hf hg := by
      rw [Away.mk_pow]
      simp only [mul_one]
    rw [← hpow, PrimeSpectrum.basicOpen_pow _ _ hd]
  calc (Proj 𝒜).basicOpen (ratio 𝒜 hf hg)
      = (awayι 𝒜 f hf hd).opensRange ⊓ (Proj 𝒜).basicOpen (ratio 𝒜 hf hg) := by
        rw [opensRange_awayι, inf_eq_right.mpr ((Proj 𝒜).basicOpen_le _)]
    _ = (awayι 𝒜 f hf hd).opensRange ⊓ basicOpen 𝒜 g := by
        rw [← Scheme.Hom.image_preimage_eq_opensRange_inf, h₁,
          Scheme.Hom.image_preimage_eq_opensRange_inf]
    _ = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g := by rw [opensRange_awayι]

lemma ratio_mul (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (hh : h ∈ 𝒜 d) :
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left :
        basicOpen 𝒜 f ⊓ basicOpen 𝒜 g ≤ basicOpen 𝒜 f)).op (ratio 𝒜 hf hh) =
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left :
        basicOpen 𝒜 f ⊓ basicOpen 𝒜 g ≤ basicOpen 𝒜 f)).op (ratio 𝒜 hf hg) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right :
        basicOpen 𝒜 f ⊓ basicOpen 𝒜 g ≤ basicOpen 𝒜 g)).op (ratio 𝒜 hg hh) := by
  have e : basicOpen 𝒜 (g * f) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g := by
    rw [basicOpen_mul, inf_comm]
  refine Scheme.eq_of_map_eq_of_eq e ?_
  rw [map_mul]
  simp only [Scheme.presheaf_map_map, ratio]
  have hF := ConcreteCategory.congr_hom
    (awayMap_awayToSection 𝒜 hg (mul_comm g f)) (Away.mk 𝒜 hf 1 h (by simpa using hh))
  have hF' := ConcreteCategory.congr_hom
    (awayMap_awayToSection 𝒜 hg (mul_comm g f)) (Away.mk 𝒜 hf 1 g (by simpa using hg))
  have hG := ConcreteCategory.congr_hom
    (awayMap_awayToSection 𝒜 hf (rfl : g * f = g * f)) (Away.mk 𝒜 hg 1 h (by simpa using hh))
  simp only [ConcreteCategory.comp_apply] at hF hF' hG
  rw [← hF, ← hF', ← hG, ← map_mul]
  congr 1
  exact (awayMap_mk_one_eq_mul 𝒜 hg hf _).trans (mul_comm _ _)

end Proj

namespace Scheme.CoordinateCover

/-- The coordinate cover attached to a morphism `ρ : X ⟶ Proj 𝒜` and a family of homogeneous
elements `fᵢ` of the same positive degree whose basic opens cover the image of `ρ`: the charts are
the preimages of the `D₊(fᵢ)` and the ratios are the pullbacks of the functions `fⱼ / fᵢ`. -/
def ofProj {X : Scheme.{u}} {ι : Type u} {σ' A : Type u} [CommRing A] [SetLike σ' A]
    [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜] (ρ : X ⟶ Proj 𝒜) {d : ℕ} (hd : 0 < d)
    (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 d) (hcov : ⨆ i, ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (f i) = ⊤) :
    X.CoordinateCover ι where
  U i := ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (f i)
  ratio i j := ρ.app _ (Proj.ratio 𝒜 (hf i) (hf j))
  ratio_self i := by simp
  basicOpen_ratio i j := by
    rw [← Scheme.preimage_basicOpen, Proj.basicOpen_ratio 𝒜 hd]
    rfl
  ratio_mul i j l := by
    have := congrArg (ρ.app _) (Proj.ratio_mul 𝒜 (hf i) (hf j) (hf l))
    rw [map_mul] at this
    simp only [← CommRingCat.comp_apply, ρ.naturality] at this
    exact this
  iSup_U := hcov

lemma ofProj_U {X : Scheme.{u}} {ι : Type u} {σ' A : Type u} [CommRing A] [SetLike σ' A]
    [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜] (ρ : X ⟶ Proj 𝒜) {d : ℕ} (hd : 0 < d)
    (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 d) (hcov : ⨆ i, ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (f i) = ⊤) (i : ι) :
    (ofProj 𝒜 ρ hd f hf hcov).U i = ρ ⁻¹ᵁ Proj.basicOpen 𝒜 (f i) := rfl

end Scheme.CoordinateCover

end AlgebraicGeometry
