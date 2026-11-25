/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Where a global section generates a module

A global section `σ` of an `𝒪_X`-module `M` *generates `M` at `x`* if it is a free generator of
`M` on some open neighbourhood of `x`. For an invertible `M` this means that `σ` does not vanish
at `x`: if `σ = c • e` for a free generator `e` near `x`, then `σ` generates `M` at `x` if and
only if `x` lies in the basic open of `c`.

We also describe sections of `J ⊗ N` for an invertible ideal sheaf `J` and an invertible module
`N`: their images in `N` are locally of the form `(v π) • e` with `π` a local generator of `J`,
and a section of `N` whose local coefficients lie in `J` maps to zero in `N ⧸ J N`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.GeneratesAt`: `σ` generates `M` at `x`.
- `AlgebraicGeometry.Scheme.Modules.generatingLocus`: the open locus where `σ` generates `M`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_generatingLocus`: `σ` is a free generator
  of `M` on its generating locus.
- `AlgebraicGeometry.Scheme.Modules.generatesAt_iff_mem_basicOpen`: `σ = c • e` generates at
  `x` if and only if `x` lies in the basic open of `c`.
- `AlgebraicGeometry.Scheme.Modules.exists_app_leftUnitor_whiskerRight_toModulesι`: the local
  shape of the image of a section of `J ⊗ N` in `N`.
- `AlgebraicGeometry.Scheme.Modules.app_cokernel_π_eq_zero`: a section of `N` with local
  coefficients in `J` vanishes in `N ⧸ J N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- A global section `σ` of `M` *generates `M` at `x`* if it is a free generator of `M` on some
open neighbourhood of `x`. -/
def GeneratesAt (σ : Γ(M, ⊤)) (x : X) : Prop :=
  ∃ W : X.Opens, x ∈ W ∧ IsFreeGenerator (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ)

/-- The open locus where a global section `σ` of `M` generates `M`. -/
def generatingLocus (σ : Γ(M, ⊤)) : X.Opens where
  carrier := {x | GeneratesAt σ x}
  is_open' := isOpen_iff_forall_mem_open.mpr fun _ ⟨W, hxW, hW⟩ ↦
    ⟨W, fun _ hy ↦ ⟨W, hy, hW⟩, W.2, hxW⟩

lemma mem_generatingLocus {σ : Γ(M, ⊤)} {x : X} : x ∈ generatingLocus σ ↔ GeneratesAt σ x :=
  .rfl

/-- A global section is a free generator on its generating locus. -/
lemma isFreeGenerator_generatingLocus (σ : Γ(M, ⊤)) :
    IsFreeGenerator (M.presheaf.map (homOfLE (le_top : generatingLocus σ ≤ ⊤)).op σ) := by
  refine isFreeGenerator_of_mem _ (S := ⟨fun V _ ↦ ∃ W : X.Opens, V ≤ W ∧
      IsFreeGenerator (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ),
      fun ⟨W, hVW, hW⟩ f ↦ ⟨W, f.le.trans hVW, hW⟩⟩) (fun x hx ↦ ?_) fun V i ⟨W, hVW, hW⟩ ↦ ?_
  · obtain ⟨W, hxW, hW⟩ := id hx
    exact ⟨W ⊓ generatingLocus σ, homOfLE inf_le_right, ⟨W, inf_le_left, hW⟩, hxW, hx⟩
  · have h := hW.map hVW
    rwa [presheaf_map_homOfLE_map_homOfLE, ← presheaf_map_homOfLE_map_homOfLE
      (le_top : generatingLocus σ ≤ ⊤) i.le] at h

section Coefficient

variable {W : X.Opens} {e : Γ(M, W)} {σ : Γ(M, ⊤)} {c : Γ(X, W)}

/-- If `σ = c • e` on `W` for a free generator `e`, then `σ` generates `M` at the points of the
basic open of `c`. -/
lemma generatesAt_of_mem_basicOpen (he : IsFreeGenerator e)
    (hσ : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ = c • e) {x : X}
    (hx : x ∈ X.basicOpen c) : GeneratesAt σ x := by
  have hle : X.basicOpen c ≤ W := X.basicOpen_le c
  refine ⟨X.basicOpen c, hx, ?_⟩
  have hu : IsUnit (X.presheaf.map (homOfLE hle).op c) := X.toRingedSpace.isUnit_res_basicOpen c
  have h : M.presheaf.map (homOfLE (le_top : X.basicOpen c ≤ ⊤)).op σ =
      hu.unit.1 • M.presheaf.map (homOfLE hle).op e := by
    rw [← presheaf_map_homOfLE_map_homOfLE (le_top : W ≤ ⊤) hle, hσ, map_smul]
    rfl
  rw [h]
  exact (he.map hle).units_smul _

/-- If `σ = c • e` on `W` for a free generator `e` and `σ` generates `M` at `x ∈ W`, then `x`
lies in the basic open of `c`. -/
lemma mem_basicOpen_of_generatesAt (he : IsFreeGenerator e)
    (hσ : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ = c • e) {x : X} (hxW : x ∈ W)
    (h : GeneratesAt σ x) : x ∈ X.basicOpen c := by
  obtain ⟨W', hxW', hW'⟩ := h
  have hV : W ⊓ W' ≤ W := inf_le_left
  obtain ⟨u, hu⟩ := (he.map hV).exists_unit_smul_eq
    (hW'.map (inf_le_right : W ⊓ W' ≤ W'))
  rw [presheaf_map_homOfLE_map_homOfLE, ← presheaf_map_homOfLE_map_homOfLE (le_top : W ≤ ⊤) hV,
    hσ, map_smul] at hu
  have hc : X.presheaf.map (homOfLE hV).op c = u.1 := (he.map hV).smul_left_injective hu
  have : x ∈ X.basicOpen (X.presheaf.map (homOfLE hV).op c) := by
    rw [hc, X.basicOpen_of_isUnit u.isUnit]
    exact ⟨hxW, hxW'⟩
  rw [Scheme.basicOpen_res] at this
  exact this.2

lemma generatesAt_iff_mem_basicOpen (he : IsFreeGenerator e)
    (hσ : M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ = c • e) {x : X} (hxW : x ∈ W) :
    GeneratesAt σ x ↔ x ∈ X.basicOpen c :=
  ⟨mem_basicOpen_of_generatesAt he hσ hxW, generatesAt_of_mem_basicOpen he hσ⟩

end Coefficient

section Twist

variable (J : X.IdealSheafData) (N : X.Modules)

/-- **The image of a section of `J ⊗ N` in `N`.** Let `J` be an invertible ideal sheaf and `N`
an invertible module. For a global section `u` of `J ⊗ N` and a point `x` of an open `O`, there
is an affine open `W ∋ x` inside `O`, a free generator `e` of `N` on `W` and a generator `π` of
`J` on `W` such that the image of `u` in `N` is `(v π) • e` on `W`, where `v` does not vanish at
`x` if `u` generates `J ⊗ N` at `x`. -/
lemma exists_app_leftUnitor_whiskerRight_toModulesι (hJ : J.IsInvertible) [N.IsInvertible]
    (u : Γ(J.toModules ⊗ N, ⊤)) {x : X} {O : X.Opens} (hxO : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ O ∧ ∃ (e : Γ(N, W.1)) (v π : Γ(X, W.1)),
      IsFreeGenerator e ∧ Ideal.span {π} = J.ideal W ∧
      N.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
        ((J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ u) = (v * π) • e ∧
      (GeneratesAt u x → x ∈ X.basicOpen v) := by
  have := hJ.isInvertible_toModules
  have := IsInvertible.sheafOfModules_isInvertible J.toModules
  have := IsInvertible.sheafOfModules_isInvertible N
  obtain ⟨W, hxW, hWO, ⟨π', hπ'⟩, e, he⟩ := exists_isFreeGenerator₂ J.toModules N hxO
  let π : Γ(X, W.1) := J.toModulesι.app W.1 π'
  have hspan : Ideal.span {π} = J.ideal W := by
    refine le_antisymm (Ideal.span_le.mpr ?_) fun a ha ↦ ?_
    · rintro _ rfl
      exact (J.range_toModulesι_app W).subset ⟨π', rfl⟩
    · obtain ⟨m, rfl⟩ := (J.range_toModulesι_app W).superset ha
      obtain ⟨r, rfl⟩ := hπ'.exists_smul_eq m
      rw [Hom.app_smul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hg := hπ'.tmulSection he
  obtain ⟨v, hv⟩ := hg.exists_smul_eq
    ((J.toModules ⊗ N).presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op u)
  refine ⟨W, hxW, hWO, e, v, π, he, hspan, ?_, fun h ↦ ?_⟩
  · rw [← Hom.app_presheaf_map, ← hv, Hom.app_smul, Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection]
    erw [leftUnitor_hom_app_tmulSection']
    rw [mul_smul]
    rfl
  · exact mem_basicOpen_of_generatesAt hg hv.symm hxW h

/-- **A section with coefficients in `J` vanishes in `N ⧸ J N`.** If near every point a global
section `σ` of `N` is `c • e` for a free generator `e` and a coefficient `c` in `J`, then its
image in the cokernel of `J ⊗ N ⟶ 𝒪_X ⊗ N ≅ N` is zero. -/
lemma app_cokernel_π_eq_zero (σ : Γ(N, ⊤))
    (h : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ (e : Γ(N, W.1)) (c : Γ(X, W.1)),
      c ∈ J.ideal W ∧ N.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op σ = c • e) :
    ((λ_ N).inv ≫ cokernel.π (J.toModulesι ▷ N)).app ⊤ σ = 0 := by
  choose W hxW e c hc hσ using h
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(cokernel (J.toModulesι ▷ N)).presheaf,
    (cokernel (J.toModulesι ▷ N)).isSheaf⟩ (fun x ↦ (W x).1) ⊤ (fun x ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) _ _ fun x ↦ ?_
  obtain ⟨a, ha⟩ := (J.range_toModulesι_app (W x)).superset (hc x)
  change (cokernel (J.toModulesι ▷ N)).presheaf.map (homOfLE le_top).op _ =
    (cokernel (J.toModulesι ▷ N)).presheaf.map (homOfLE le_top).op 0
  rw [map_zero, ← Hom.app_presheaf_map, hσ x, Hom.comp_app, ConcreteCategory.comp_apply,
    leftUnitor_inv_app, tmulSection_smul, ← smul_tmulSection]
  have h1 : c x • unitSectionsEquiv (W x).1 1 = J.toModulesι.app (W x).1 a := by
    rw [← unitSectionsEquiv_eq_smul_one]
    exact ha.symm
  have h2 := whiskerRight_app_tmulSection J.toModulesι (N := N) a (e x)
  rw [h1]
  erw [← h2]
  have h3 : ((J.toModulesι ▷ N) ≫ cokernel.π (J.toModulesι ▷ N)).app (W x).1
      (tmulSection a (e x)) = 0 := by
    rw [cokernel.condition]
    rfl
  exact h3

end Twist

end AlgebraicGeometry.Scheme.Modules
