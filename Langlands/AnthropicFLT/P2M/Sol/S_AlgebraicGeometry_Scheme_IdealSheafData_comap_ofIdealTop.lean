/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f
      = Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  let ι := {p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : ι => i.1.1) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩
  · rintro ⟨⟨U, V⟩, hUV⟩
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le _ f V U hUV, Scheme.IdealSheafData.ofIdealTop_ideal,
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [← Category.assoc, f.naturality, Category.assoc, ← Functor.map_comp]
    rfl
