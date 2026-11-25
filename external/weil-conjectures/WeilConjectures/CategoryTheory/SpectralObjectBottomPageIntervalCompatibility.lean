/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Page homology compatibility with the finite interval

Source: Mathlib spectral-object homology data, Page.lean and Cycles.lean.
(blueprint: lem-sc-spectral-object-bottom-page-interval-compatibility)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits ComposableArrows
namespace CategoryTheory.Abelian.SpectralObject

/-- Compatibility of the page homology comparison with the canonical maps to
`H^p(0,r-1)`. This only concerns finite intervals; it uses no inverse map from
`H^p(0,r-1)` to `H^p(bottom,r-1)` and no map to the abutment.
Source: Mathlib SpectralObject/SpectralSequence.lean (`spectralSequence_iso`,
`spectralSequenceHomologyData_left_i`, `spectralSequenceHomologyData_left_π`),
Page.lean (`map_ιE`) and Cycles.lean (`opcyclesMap_fromOpcycles`).
(blueprint: lem-sc-spectral-object-bottom-page-interval-compatibility)

Proof: Put a=2-r and c=r-1. The page homology data have kernel object
E^p(a-1,0,1,c), with inclusion changing a-1 to a and quotient changing
c to c+1. Rewrite the page homology comparison by `spectralSequence_iso`.
The cycles isomorphism of these left homology data identifies the cycles
inclusion with that kernel inclusion and the homology projection with
that quotient. Cancel the page comparison isomorphisms. Apply `map_ιE`
to the two maps: changing a leaves the opcycles object unchanged, while
changing c induces its opcycles map. Thus both sides start with ιE from
E^p(a-1,0,1,c). Apply `opcyclesMap_fromOpcycles` to the right side:
its opcycles map followed by fromOpcycles at c+1 equals fromOpcycles at
c followed by H^p(0,c) to H^p(0,c+1), which is the left side. All interval
inequalities follow from r≥2, including the identity intervals at r=2;
p=0 uses the degree -1 in exactly the same homology data. -/
theorem bottomPage_interval_compatibility
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]
    (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
    let m (s : ℤ) (hs : 2 ≤ s) :
        (Y.E₂SpectralSequenceNat.page s hs).X (p, 0) ⟶
          (Y.H p).obj (mk₁ (homOfLE
            (show ((0 : ℤ) : EInt) ≤ (s - 1 : ℤ) by simp; omega))) :=
    (Y.spectralSequencePageXIso coreE₂CohomologicalNat s hs (p, 0)
      (2 - s : ℤ) (0 : ℤ) (1 : ℤ) (s - 1 : ℤ)
      (by simp; congr 1; omega) rfl (by simp) (by simp)
      (p - 1) p (p + 1) (by simp)).hom ≫
    Y.ιE (homOfLE (show ((2 - s : ℤ) : EInt) ≤ (0 : ℤ) by simp; omega))
      (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
      (homOfLE (show ((1 : ℤ) : EInt) ≤ (s - 1 : ℤ) by simp; omega))
      (p - 1) p (p + 1) ≫
    Y.fromOpcycles (homOfLE (show ((0 : ℤ) : EInt) ≤ (1 : ℤ) by simp))
      (homOfLE (show ((1 : ℤ) : EInt) ≤ (s - 1 : ℤ) by simp; omega))
      (homOfLE (show ((0 : ℤ) : EInt) ≤ (s - 1 : ℤ) by simp; omega))
      (Subsingleton.elim _ _) p
    (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ m r hr ≫
        (Y.H p).map (twoδ₂Toδ₁' ((0 : ℤ) : EInt) (r - 1 : ℤ) (r + 1 - 1 : ℤ)
          (WithBotTop.coe_le_coe.2 (by omega))
          (WithBotTop.coe_le_coe.2 (by omega))) =
      (Y.E₂SpectralSequenceNat.page r hr).homologyπ (p, 0) ≫
        (Y.E₂SpectralSequenceNat.iso r (r + 1) (p, 0) rfl hr).hom ≫
          m (r + 1) (by omega) := by
  dsimp only
  let D := Y.spectralSequenceHomologyData coreE₂CohomologicalNat r (r + 1) rfl hr
    ((ComplexShape.spectralSequenceNat (r, 1 - r)).prev (p, 0)) (p, 0)
    ((ComplexShape.spectralSequenceNat (r, 1 - r)).next (p, 0)) rfl rfl
    (2 - (r + 1) : ℤ) (2 - r : ℤ) (0 : ℤ) (1 : ℤ) (r - 1 : ℤ)
    (r + 1 - 1 : ℤ)
    (by simp; congr 1; omega) (by simp; congr 1; omega) rfl (by simp)
    (by simp) (by simp) (p - 1) p (p + 1) (by simp)
  rw [Y.spectralSequence_iso coreE₂CohomologicalNat r (r + 1) rfl hr
    ((ComplexShape.spectralSequenceNat (r, 1 - r)).prev (p, 0)) (p, 0)
    ((ComplexShape.spectralSequenceNat (r, 1 - r)).next (p, 0)) rfl rfl
    (2 - (r + 1) : ℤ) (2 - r : ℤ) (0 : ℤ) (1 : ℤ) (r - 1 : ℤ)
    (r + 1 - 1 : ℤ)
    (by simp; congr 1; omega) (by simp; congr 1; omega) rfl (by simp)
    (by simp) (by simp) (p - 1) p (p + 1) (by simp)]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, HomologicalComplex.homologyIsoSc'_eq_refl,
    Iso.refl_hom, Category.id_comp]
  change _ = _ ≫ D.left.homologyIso.hom ≫ _
  erw [D.left.homologyπ_comp_homologyIso_hom_assoc]
  have hc := D.left.cyclesIso_hom_comp_i
  change D.left.cyclesIso.hom ≫ D.left.i =
    (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) at hc
  rw [← hc]
  simp only [Category.assoc]
  simp only [D, spectralSequenceHomologyData_left_i, spectralSequenceHomologyData_left_π,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [mapFourδ₁Toδ₀', mapFourδ₄Toδ₃']
  rw [Y.map_ιE_assoc _ _ _ _ _ _ _ (𝟙 _) (p - 1) p (p + 1)]
  rw [Y.opcyclesMap_id, Category.id_comp]
  rw [Y.map_ιE_assoc _ _ _ _ _ _ _
    (threeδ₃Toδ₂' ((0 : ℤ) : EInt) (1 : ℤ) (r - 1 : ℤ) (r + 1 - 1 : ℤ)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))
      (WithBotTop.coe_le_coe.2 (by omega))) (p - 1) p (p + 1)]
  rw [Y.opcyclesMap_fromOpcycles _ _ _ _ _ _ _ _ _
    (twoδ₂Toδ₁' ((0 : ℤ) : EInt) (r - 1 : ℤ) (r + 1 - 1 : ℤ)
      (WithBotTop.coe_le_coe.2 (by omega)) (WithBotTop.coe_le_coe.2 (by omega))) p]

end CategoryTheory.Abelian.SpectralObject
