/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Non-vanishing loci of sections are affine

Let `X` be universally closed over an affine scheme, and let `ℒ` be an invertible `𝒪_X`-module
with finitely many global sections `x j` whose non-vanishing loci `X_{x j}` are affine and cover
`X`, as for the pullback of `𝒪(1)` along a closed immersion into projective space. Then the
non-vanishing locus `X_s` of every global section `s` of `ℒ` is affine
(`AlgebraicGeometry.Scheme.Modules.isAffineOpen_compl_support_zeroLocus`).

## Implementation details

On `X_{x j}` write `s = a j • x j`, so that `X_s ∩ X_{x j} = D(a j)`; on `X_s` write
`x j = g j • s`. Then `a j * g j = 1` on `X_s ∩ X_{x j}` and `D(g j) ⊆ X_{x j}`, and
`AlgebraicGeometry.IsAffineOpen.of_universallyClosed` applies.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The value `φ(1)` of a section `φ : 𝒪_X ⟶ ℒ` is compatible with restriction. -/
lemma presheaf_map_app_unitSectionsEquiv_one {L : X.Modules} (φ : 𝟙_ X.Modules ⟶ L)
    {V W : X.Opens} (h : W ≤ V) :
    L.presheaf.map (homOfLE h).op (φ.app V (unitSectionsEquiv V 1)) =
      φ.app W (unitSectionsEquiv W 1) := by
  rw [← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one]

/-- **A positive power of a section vanishes where the section does**: for `m > 0`, the zero
scheme of `s^{⊗ m}` has the same support as the zero scheme of `s`. On an affine open where `ℒ`
has a free generator `e` and `s = f • e`, one has `s^{⊗ m} = f ^ m • e^{⊗ m}`, and
`D(f ^ m) = D(f)`. -/
lemma compl_support_zeroLocus_tensorPowSection (L : X.Modules) [L.IsInvertible]
    (s : 𝟙_ X.Modules ⟶ L) {m : ℕ} (hm : 0 < m) :
    (Hom.zeroLocus (tensorPowSection s m)).support.compl = (Hom.zeroLocus s).support.compl := by
  have := IsInvertible.sheafOfModules_isInvertible L
  have := IsInvertible.sheafOfModules_isInvertible (L.tensorPow m)
  ext x
  obtain ⟨V, hxV, -, e, he⟩ := exists_isFreeGenerator L (x := x) (W := ⊤) trivial
  obtain ⟨f, hf⟩ := he.exists_smul_eq (s.app V.1 (unitSectionsEquiv _ 1))
  obtain ⟨E, hE, hsE⟩ := exists_tensorPowSectionOne_eq_pow_smul s he hf.symm m
  have h₁ := basicOpen_coeff_eq s V he
  have h₂ := basicOpen_coeff_eq (tensorPowSection s m) V hE
  rw [(he.coeff_eq_iff _ _).mpr hf] at h₁
  rw [(hE.coeff_eq_iff _ _).mpr hsE.symm, X.basicOpen_pow _ hm, h₁] at h₂
  have := congrArg (x ∈ ·) h₂
  simp only [TopologicalSpace.Opens.mem_inf, eq_iff_iff] at this
  exact ⟨fun h ↦ (this.mpr ⟨hxV, h⟩).2, fun h ↦ (this.mp ⟨hxV, h⟩).2⟩

/-- **The non-vanishing locus of a section is affine.** Let `f : X ⟶ S` be universally closed
with `S` affine, and let `ℒ` be an invertible `𝒪_X`-module with finitely many global sections
`x j` whose non-vanishing loci `X_{x j}` are affine and cover `X`. Then the non-vanishing locus
`X_s`, the complement of the zero scheme of `s`, of every global section `s` of `ℒ` is affine. -/
theorem isAffineOpen_compl_support_zeroLocus {S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    [IsAffine S] (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L] {ι : Type*}
    [Finite ι] (x : ι → (𝟙_ X.Modules ⟶ L))
    (hx : ∀ j, IsAffineOpen (Hom.zeroLocus (x j)).support.compl)
    (hcov : ⨆ j, (Hom.zeroLocus (x j)).support.compl = ⊤) (s : 𝟙_ X.Modules ⟶ L) :
    IsAffineOpen (Hom.zeroLocus s).support.compl := by
  set D : ι → X.Opens := fun j ↦ (Hom.zeroLocus (x j)).support.compl
  set U : X.Opens := (Hom.zeroLocus s).support.compl
  have he (j : ι) := isFreeGenerator_app_one_of_le (x j) (le_refl (D j))
  have hσ := isFreeGenerator_app_one_of_le s (le_refl U)
  choose a ha' using fun j ↦ (he j).exists_smul_eq (s.app (D j) (unitSectionsEquiv _ 1))
  choose g hg' using fun j ↦ hσ.exists_smul_eq ((x j).app U (unitSectionsEquiv _ 1))
  have ha (j : ι) : U ⊓ D j = X.basicOpen (a j) := by
    rw [← ((he j).coeff_eq_iff _ _).mpr (ha' j), basicOpen_coeff_eq s ⟨D j, hx j⟩ (he j),
      inf_comm]
  have hg (j : ι) : X.basicOpen (g j) ≤ D j := by
    intro p hp
    have hpU : p ∈ U := X.basicOpen_le _ hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hpU U.2
    replace hVU : V ≤ U := hVU
    have h := basicOpen_coeff_eq (x j) ⟨V, hV⟩ (hσ.map hVU)
    rw [← presheaf_map_app_unitSectionsEquiv_one (x j) hVU, hσ.coeff_map hVU,
      (hσ.coeff_eq_iff _ _).mpr (hg' j), X.basicOpen_res] at h
    have : p ∈ V ⊓ X.basicOpen (g j) := ⟨hpV, hp⟩
    rw [h] at this
    exact this.2
  have hag (j : ι) : X.presheaf.map (homOfLE inf_le_right : U ⊓ D j ⟶ D j).op (a j) *
      X.presheaf.map (homOfLE inf_le_left : U ⊓ D j ⟶ U).op (g j) = 1 := by
    have h₁ := congrArg (L.presheaf.map (homOfLE inf_le_right : U ⊓ D j ⟶ D j).op) (ha' j)
    rw [map_smul, presheaf_map_app_unitSectionsEquiv_one,
      presheaf_map_app_unitSectionsEquiv_one] at h₁
    have h₂ := congrArg (L.presheaf.map (homOfLE inf_le_left : U ⊓ D j ⟶ U).op) (hg' j)
    rw [map_smul, presheaf_map_app_unitSectionsEquiv_one,
      presheaf_map_app_unitSectionsEquiv_one] at h₂
    have hσW : IsFreeGenerator (s.app (U ⊓ D j) (unitSectionsEquiv _ 1)) := by
      rw [← presheaf_map_app_unitSectionsEquiv_one s (inf_le_left : U ⊓ D j ≤ U)]
      exact hσ.map inf_le_left
    refine hσW.smul_left_injective ?_
    change (_ * _) • s.app (U ⊓ D j) (unitSectionsEquiv _ 1) =
      (1 : Γ(X, U ⊓ D j)) • s.app (U ⊓ D j) (unitSectionsEquiv _ 1)
    rw [one_smul, mul_smul]
    exact (congrArg (fun m ↦ X.presheaf.map (homOfLE inf_le_right : U ⊓ D j ⟶ D j).op (a j) • m)
      h₂).trans h₁
  exact IsAffineOpen.of_universallyClosed f D hx hcov U a ha g hg hag

end AlgebraicGeometry.Scheme.Modules
