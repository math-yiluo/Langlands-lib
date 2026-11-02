/-
The proof of `smooth_of_smooth_of_surjective_of_smooth_comp` is adapted from
`P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem (commit
6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and
`ATTRIBUTION.md`.
Modified: the hypotheses `QuasiCompact` on the covering map and `LocallyOfFinitePresentation`
on `g` are removed, the latter being proved here; names are changed. The paired Markdown file
lists the changes.
-/
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentStatement
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth

/-!
# Smoothness descends along a surjective smooth map on the source

Stacks Project, Tag 05B5 (Descent, Lemma 35.14.5), for a surjective smooth (in particular etale)
covering map of the source.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- If `p : W ⟶ X` is smooth and surjective and `p ≫ g` is smooth, then `g` is smooth. -/
theorem smooth_of_smooth_of_surjective_of_smooth_comp
    {W X S : Scheme.{u}} (p : W ⟶ X) (g : X ⟶ S) [Smooth p] [Surjective p]
    [Smooth (p ≫ g)] : Smooth g := by
  have : LocallyOfFinitePresentation g := locallyOfFinitePresentation_of_surjective_flat_comp p g
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := p.surjective y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (p x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyU (U.2.preimage g.continuous)
  obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hOV⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ p ⁻¹ᵁ V from hyV)
      (V.2.preimage p.continuous)
  have hOU : O ≤ (p ≫ g) ⁻¹ᵁ U := fun w hw => hVU (hOV hw)
  have hfp := g.finitePresentation_appLE hU hV hVU
  have hsm := p.smooth_appLE hV hO hOV
  let algRS := (g.appLE U V hVU).hom.toAlgebra
  let algST := (p.appLE V O hOV).hom.toAlgebra
  let algRT := ((p ≫ g).appLE U O hOU).hom.toAlgebra
  have : IsScalarTower Γ(S, U) Γ(X, V) Γ(W, O) := IsScalarTower.of_algebraMap_eq fun r => by
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE p g U V O hVU hOV]
  have : Algebra.FinitePresentation Γ(S, U) Γ(X, V) := hfp
  have : Algebra.Smooth Γ(X, V) Γ(W, O) := hsm
  have hx' : Algebra.IsSmoothAt Γ(S, U) (hO.primeIdealOf ⟨x, hxO⟩).asIdeal := by
    have H : ((p ≫ g).stalkMap x).hom.FormallySmooth :=
      (Scheme.Hom.mem_smoothLocus (f := p ≫ g)).mp (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
    exact (formallySmooth_stalkMap_iff U hU O hO hOU hxO).mp H
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hyV]
  have hunder : (hO.primeIdealOf ⟨x, hxO⟩).asIdeal.under Γ(X, V) =
      (hV.primeIdealOf ⟨p x, hyV⟩).asIdeal := by
    rw [Ideal.under_def]
    exact congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV O hO hOV hxO).1)
  exact Algebra.IsSmoothAt.of_isSmoothAt_of_smooth Γ(S, U) Γ(X, V) Γ(W, O) _ hx' _ hunder

/-- **Stacks 05B5**, smoothness along a surjective etale map: if `p : W ⟶ X` is etale and
surjective and `p ≫ g` is smooth, then `g` is smooth. -/
theorem smoothEtaleSourceDescent : SmoothEtaleSourceDescentStatement.{u} := by
  intro W X S p g hp hsurj hpg
  exact smooth_of_smooth_of_surjective_of_smooth_comp p g

end Langlands.AlgebraicGeometry
