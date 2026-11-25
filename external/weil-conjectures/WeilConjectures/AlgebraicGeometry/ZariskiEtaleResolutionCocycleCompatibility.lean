/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ObjectCohomologyResolutionCocycleEquivalence

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- Naturality of the class of a section cycle under a chain map.

Source: Stacks Project, Section 01FT, equation-cohomology-object-site;
Tag 06XR (1), lemma-compute-ext-resolutions.
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-compatibility)

Proof: Injectivity of the inclusion of cycles and its naturality show that the
cycles map takes the cycle of x to the cycle of y. Naturality of the homology
projection then identifies their homology classes. This works for every chain
map of abelian-group cochain complexes, with no site or resolution hypotheses. -/
theorem zariski_etale_resolution_cocycle_compatibility
    {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ} (f : K ⟶ L)
    (q : ℕ) (x : K.X q) (hx : (K.d q (q + 1)).hom x = 0)
    (y : L.X q) (hy : (L.d q (q + 1)).hom y = 0)
    (h : (f.f q).hom x = y) :
    (HomologicalComplex.homologyMap f q).hom (sectionCycleClass K q x hx) =
      sectionCycleClass L q y hy := by
  set_option backward.isDefEq.respectTransparency false in
    let zx := (K.sc q).abCyclesIso.inv ⟨x, sectionCycle_mem_kernel K q x hx⟩
    let zy := (L.sc q).abCyclesIso.inv ⟨y, sectionCycle_mem_kernel L q y hy⟩
    have hz : (HomologicalComplex.cyclesMap f q).hom zx = zy := by
      apply (AddCommGrpCat.mono_iff_injective (L.iCycles q)).mp inferInstance
      change ((HomologicalComplex.cyclesMap f q) ≫ L.iCycles q) zx = (L.iCycles q) zy
      rw [HomologicalComplex.cyclesMap_i]
      change (f.f q) ((K.iCycles q) zx) = (L.iCycles q) zy
      dsimp only [zx, zy, HomologicalComplex.iCycles]
      erw [(K.sc q).abCyclesIso_inv_apply_iCycles,
        (L.sc q).abCyclesIso_inv_apply_iCycles]
      exact h
    change ((K.homologyπ q) ≫ HomologicalComplex.homologyMap f q) zx =
      (L.homologyπ q) zy
    rw [HomologicalComplex.homologyπ_naturality]
    change (L.homologyπ q) ((HomologicalComplex.cyclesMap f q) zx) = _
    rw [hz]

