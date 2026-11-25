/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Pullback and the long exact sequence of etale cohomology

Source: Stacks Project, Cohomology on Sites, Tag 01FT; Homology, Tag 010S;
Etale Cohomology, Tags 04I0 and 0A5C
(blueprint: lem-weil-pbc-pullback-cohomology-long-exact-ladder).

We use the existing `Sheaf.H` and `Etale.cohomologyMap` encoding of the recorded
cohomology and pullback nodes. The boundary is postcomposition with `hS.extClass`.
Its derived morphism is exactly `hS.singleδ` (`ShortExact.extClass_hom`), not an
arbitrary choice of a connecting morphism. Identifying Ext cohomology with derived
global sections identifies this boundary with cohomology of the shifted `RΓ(singleδ)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- Pullback takes a short exact sequence to a short exact sequence, and its cohomology
maps give a commuting ladder of the two long exact sequences, including the initial zero.
Source: Stacks 01FT, 010S, 04I0, 0A5C
(blueprint: lem-weil-pbc-pullback-cohomology-long-exact-ladder).

Proof (the node's eleven steps):
1. `prop-weil-pbc-inverse-image-exact` gives exactness of the pulled-back sequence.
2. `lem-sf-derived-ses-triangle` gives the two canonical `singleδ` triangles, whose
   vertices are in D+ (`def-weil-pbc-derived-categories`).
3. Apply triangulated derived global sections
   (`lem-weil-pbc-derived-direct-image-triangulated`) and then
   `lem-sf-derived-homology-long-exact`; `def-weil-pbc-etale-cohomology` identifies the terms.
4. `lem-weil-pbc-dplus-injective-representative` makes negative cohomology vanish, giving
   the initial injection in degree zero.
5. The pullback is the natural derived adjunction unit, followed by the global sections
   comparison (`lem-weil-pbc-cohomology-pullback-derived-unit`,
   `prose-04-06`).
6. Exact inverse image preserves the canonical triangle and its boundary
   (`lem-weil-pbc-exact-functor-ses-triangle-image`).
7. Naturality of that unit and comparison gives naturality in the derived object
   (`proposition-cohomology-p-1-over-henselian--1`).
8. Shift K-injective representatives (`lem-weil-pbc-kinjective-shift`), using uniqueness
   of comparisons, to see that the natural transformation commutes with shifts.
9. `lem-weil-pbc-commshift-nattrans-triangle-morphism` gives a morphism of triangles.
10. On cohomology the vertical maps are the specified pullback maps
    (`def-weil-pbc-cohomology-pullback`).
11. `lem-weil-pbc-derived-cohomology-ladder` gives the three commuting squares.
In the existing Ext encoding, `ShortExact.extClass_hom` identifies the boundary with
`singleδ`; Ext exactness and `Ext.mapExactFunctor_extClass` give the same ladder. -/
theorem pullbackCohomology_longExact_ladder {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) :
    ∃ hY : (S.map ((f)^*[AddCommGrpCat.{u + 1}])).ShortExact,
    ∃ δX : ∀ q : ℕ, Sheaf.H S.X₃ q →+ Sheaf.H S.X₁ (q + 1),
    ∃ δY : ∀ q : ℕ,
      Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₃) q →+
        Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₁) (q + 1),
      (∀ (q : ℕ) (x : Sheaf.H S.X₃ q), δX q x = x.comp hS.extClass rfl) ∧
      (∀ (q : ℕ) (x : Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj S.X₃) q),
        δY q x = x.comp hY.extClass rfl) ∧
      Function.Injective (Sheaf.H.map S.f 0) ∧
      Function.Injective (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) 0) ∧
      (∀ q : ℕ,
        Function.Exact (Sheaf.H.map S.f q) (Sheaf.H.map S.g q) ∧
        Function.Exact (Sheaf.H.map S.g q) (δX q) ∧
        Function.Exact (δX q) (Sheaf.H.map S.f (q + 1))) ∧
      (∀ q : ℕ,
        Function.Exact (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) q)
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q) ∧
        Function.Exact (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q) (δY q) ∧
        Function.Exact (δY q)
          (Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) (q + 1))) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₁ q),
        cohomologyMap f S.X₂ q (Sheaf.H.map S.f q x) =
          Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.f) q
            (cohomologyMap f S.X₁ q x)) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₂ q),
        cohomologyMap f S.X₃ q (Sheaf.H.map S.g q x) =
          Sheaf.H.map (((f)^*[AddCommGrpCat.{u + 1}]).map S.g) q
            (cohomologyMap f S.X₂ q x)) ∧
      (∀ (q : ℕ) (x : Sheaf.H S.X₃ q),
        cohomologyMap f S.X₁ (q + 1) (δX q x) = δY q (cohomologyMap f S.X₃ q x)) := by
  have hY := hS.map_of_exact ((f)^*[AddCommGrpCat.{u + 1}])
  have := hS.mono_f
  have := hY.mono_f
  refine ⟨hY, Sheaf.H.δSucc hS, Sheaf.H.δSucc hY, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro q x
    rfl
  · intro q x
    rfl
  · exact Ext.postcomp_mk₀_injective_of_mono _ S.f
  · exact Ext.postcomp_mk₀_injective_of_mono _ (((f)^*[AddCommGrpCat.{u + 1}]).map S.f)
  · intro q
    exact ⟨Sheaf.H.exact_map_map hS q, Sheaf.H.exact_map_δSucc hS q,
      Sheaf.H.exact_δSucc_map hS q⟩
  · intro q
    exact ⟨Sheaf.H.exact_map_map hY q, Sheaf.H.exact_map_δSucc hY q,
      Sheaf.H.exact_δSucc_map hY q⟩
  · intro q x
    exact cohomologyMap_map f q S.f x
  · intro q x
    exact cohomologyMap_map f q S.g x
  · intro q x
    change cohomologyMap f S.X₁ (q + 1) (x.comp hS.extClass rfl) =
      (cohomologyMap f S.X₃ q x).comp hY.extClass rfl
    rw [cohomologyMap_apply,
      cohomologyMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
    exact (Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)).symm

end AlgebraicGeometry.Etale
