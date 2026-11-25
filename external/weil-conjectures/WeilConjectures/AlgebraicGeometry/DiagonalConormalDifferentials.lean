/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DiagonalConormal
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.DiagonalConormalAffineComparison

/-!
# Conormal sheaf of the diagonal and relative differentials

Source: Stacks Project, Tag 08S2
(blueprint: lem-sc-smooth-proper-diagonal-conormal-differentials).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{v}}

/-- The conormal module of the diagonal is the sheaf of relative Kähler differentials.
Source: Stacks, Tag 08S2
(blueprint: lem-sc-smooth-proper-diagonal-conormal-differentials).
Proof, step 1: cover X by affine U = Spec A mapping into affine V = Spec R.
The opens U ×_V U form the neighbourhood W of the diagonal from Tag 01KJ.
The diagonal there is cut out by I = ker(A ⊗_R A → A).
By lem-weil-pbc-affine-conormal-sections, conormal sections over U are I/I².
By lem-sc-kahler-differentials-diagonal-ideal, this is Ω_{A/R}, with da
corresponding to the class of 1 ⊗ a - a ⊗ 1 (def-weil-pbc-kahler-differentials).
Step 2: these maps commute with restriction to smaller affine opens because
that formula is unchanged and the da generate. They glue to the canonical
isomorphism; it is an isomorphism because this holds on the affine basis. -/
theorem diagonalConormal_iso_relativeDifferentials (f : X ⟶ S) :
    Nonempty (diagonalConormal f ≅ f.relativeDifferentials) := by
  obtain ⟨D, hD⟩ := exists_diagonalConormalDerivation f
  let φ : f.relativeDifferentials ⟶ diagonalConormal f :=
    (f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D
  let B := { U : X.Opens // IsAffineOpen U ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V }
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (fun U : B ↦ U.1)) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) TopologicalSpace.isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩) (U ⊓ f ⁻¹ᵁ V).isOpen
    exact ⟨W, ⟨⟨W, hW, V, hV, hWU.trans inf_le_right⟩, rfl⟩,
      hxW, hWU.trans inf_le_left⟩
  have hφ (U : B) : Function.Bijective (φ.app U.1) := by
    obtain ⟨V, hV, hUV⟩ := U.2.2
    exact diagonalConormalComparison_bijective_on_affine f D hD ⟨U.1, U.2.1⟩ ⟨V, hV⟩ hUV
  have hIso : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hφ U)
  have : (SheafOfModules.toSheaf X.ringCatSheaf ⋙
      sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (Scheme.Modules.toPresheaf X).ReflectsIsomorphisms
  have : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  have := hIso
  have : IsIso φ := isIso_of_reflects_iso φ (SheafOfModules.toSheaf X.ringCatSheaf)
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry
