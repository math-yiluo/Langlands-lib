import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.KPLocalTorusRootCommutatorStatement
import Langlands.Geometry.Building.UnramifiedStabilizerDescent
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Root compatibility of the torus filtration over `F^ur`

Clause 2 of the `K`-level copy of KP Lemma 7.2.3 (`QuasiSplitLocalTorusFiltrationStatement`),
for D1's filtration
`j(Z(K)_r) = B.centralizerTorusImage hZ r`: for `z ∈ j(Z(K)_r)` and `u ∈ U_{a,x,s}`,
`z u z⁻¹ u⁻¹ ∈ U_{a,x,r+s} U_{2a,x,r+s}`. Depth `0` is proved from V6; positive depth is
derived from `KPLocalTorusRootCommutatorStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

/-- At positive depth the common torus filtration lies in the geometric congruence subgroup. -/
theorem localTorusFiltration_le_localGeometricCharacterCongruence
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) {r : ℝ≥0} (hr : r ≠ 0) :
    localTorusFiltration F T hT r ≤ localGeometricCharacterCongruence F T r := by
  let S := localTorusSplittingData F T hT
  change localTorusFiltrationAtSplitting F S.L T r ≤ _
  simp only [localTorusFiltrationAtSplitting, ite_eq_right hr]
  exact inf_le_right

namespace MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H)

/-- A point of `Z(K)^1` normalizes every `U_{a,x,s}`. -/
theorem conj_mem_filtration_of_mem_characterValuationKernel
    {z : rationalPoints B.centralizer.Z}
    (hz : z ∈ characterValuationKernel (valuation F) B.centralizer.Z)
    {x : B.Apartment} {a : characterLattice B.S} {s : ℝ} {u : rationalPoints H}
    (hu : u ∈ B.filtration x a s) :
    rationalPoints.map B.centralizer.j z * u * (rationalPoints.map B.centralizer.j z)⁻¹ ∈
      B.filtration x a s := by
  have h := B.apartment.conj_mem_filtration (B.centralizer.toNormalizer z) hu
  rw [B.isOmegaCompatible.smul_eq_self hz x, CentralizerDatum.toNormalizer,
    weylAction_centralizerToNormalizer, coe_centralizerToNormalizer] at h
  exact h

variable (hZ : IsTorus B.centralizer.Z)

/-- Every point of `Z(K)_r` lies in `Z(K)^1`, for the valuation of the building data. -/
theorem centralizerTorusFiltration_le_characterValuationKernel_valuation (r : ℝ≥0) :
    B.centralizerTorusFiltration hZ r ≤
      characterValuationKernel (valuation F) B.centralizer.Z := by
  rw [characterValuationKernel_eq_of_isEquiv (valuation_isEquiv F)]
  exact B.centralizerTorusFiltration_le_characterValuationKernel hZ r

/-- Clause 2 of KP Lemma 7.2.3 over `K` (root compatibility of `j(Z(K)_r)`), assuming the
positive-depth torus action on root-group filtrations. -/
theorem centralizerTorusImage_isRootCompatible_of_torusRoot
    (hroot : KPLocalTorusRootCommutatorStatement.{u}) :
    ∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1 := by
  rintro x a r s _ ⟨t, ht, rfl⟩ u hu
  by_cases hr : r = 0
  · subst hr
    have hz := B.centralizerTorusFiltration_le_characterValuationKernel_valuation hZ 0 ht
    refine ⟨_, ?_, 1, Subgroup.one_mem _, mul_one _⟩
    rw [zero_add]
    exact Subgroup.mul_mem _ (B.conj_mem_filtration_of_mem_characterValuationKernel hz hu)
      (Subgroup.inv_mem _ hu)
  · exact hroot F H B hZ x a r s (pos_iff_ne_zero.mpr hr) t
      (localTorusFiltration_le_localGeometricCharacterCongruence _ hZ hr ht) u hu

end MaximalUnramified.BuildingData

end Langlands.Geometry.Building
