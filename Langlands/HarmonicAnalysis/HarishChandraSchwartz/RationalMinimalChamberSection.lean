import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamber
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Representation.Plancherel.SplitTorusCompactKernel

/-! # The full minimal chamber modulo its compact torus kernel

Every full chamber point is a compact norm-kernel point times a point of
the common-uniformizer chamber section. The same decomposition preserves
the ambient common norm kernel.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.BruhatTits.Cartan

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The actual torus norm kernel, mapped to the ambient group. -/
def rationalMinimalTorusCompactKernel : Subgroup (rationalPoints G) :=
  (rationalCommonNormKernel S.toGrp).map (rationalPoints.map i)

omit [IsAffineHom G.X.hom] in
/-- Every point of the torus norm kernel lies in the ambient norm kernel. -/
theorem rationalMinimalTorusCompactKernel_le_normKernel :
    rationalMinimalTorusCompactKernel i ≤ rationalCommonNormKernel G := by
  rintro _ ⟨a, ha, rfl⟩
  exact SplitTorus.map_mem_commonNormKernel i ha

omit [IsAffineHom G.X.hom] in
/-- The character order vanishes on the intrinsic common norm kernel. -/
theorem characterOrder_eq_zero_of_mem_normKernel {a : rationalPoints S.toGrp}
    (ha : a ∈ rationalCommonNormKernel S.toGrp) (α : characterLattice S) :
    RenardLeviCones.characterOrder S α a = 0 :=
  (mem_rationalCommonNormKernel_iff_valuation S.toGrp a).mp ha _

omit [IsAffineHom G.X.hom] in
/-- The common-uniformizer representative has exactly the character orders
of the original torus point. -/
theorem characterOrder_latticeSection_eq {a : rationalPoints S.toGrp}
    {c : Multiplicative (cocharacterLattice S)}
    (hc : a * (CocharacterUniformizer.latticeSection F S c)⁻¹ ∈
      rationalCommonNormKernel S.toGrp) (α : characterLattice S) :
    RenardLeviCones.characterOrder S α (CocharacterUniformizer.latticeSection F S c) =
      RenardLeviCones.characterOrder S α a := by
  have h := characterOrder_eq_zero_of_mem_normKernel hc α
  have hinv :
      RenardLeviCones.characterOrder S α
          (CocharacterUniformizer.latticeSection F S c)⁻¹ =
        -RenardLeviCones.characterOrder S α (CocharacterUniformizer.latticeSection F S c) := by
    simp only [RenardLeviCones.characterOrder, map_inv, toAdd_inv, AddMonoidHom.neg_apply]
  rw [RenardLeviCones.characterOrder_mul, hinv] at h
  linarith

/-- The full minimal chamber is the compact norm-kernel thickening of its
common-uniformizer section. No equality of the section and full chamber
is asserted. -/
theorem rationalMinimalChamber_eq_compactKernel_mul_section
    (hS : IsSplitTorus S.toGrp) :
    rationalMinimalChamber i ν =
      (rationalMinimalTorusCompactKernel i : Set (rationalPoints G)) *
        Langlands.BruhatTits.SpecialCompact.standardComponentCAplus i ν ∅ (𝟙 S.toGrp) := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨x, rfl, hx⟩ := (mem_rationalMinimalChamber_iff_order i ν a).mp ha
    obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F S hS).2.2 x
    let s := CocharacterUniformizer.latticeSection F S c
    have hs : rationalPoints.map i s ∈
        Langlands.BruhatTits.SpecialCompact.standardComponentCAplus i ν ∅ (𝟙 S.toGrp) := by
      rw [standardComponentCAplus_minimal_id_eq_latticeCut]
      refine ⟨s, ⟨⟨c, rfl⟩, ?_⟩, rfl⟩
      rw [RenardLeviCones.mem_componentPlus_iff_order,
        RenardLeviCones.restrictedSimpleCharacters_minimal]
      intro α hα
      rw [characterOrder_latticeSection_eq hc α]
      exact hx α hα
    refine Set.mem_mul.mpr ⟨rationalPoints.map i (x * s⁻¹), ⟨x * s⁻¹, hc, rfl⟩,
      rationalPoints.map i s, hs, ?_⟩
    rw [← map_mul]
    congr 1
    group
  · rintro a ⟨k, ⟨x, hx, rfl⟩, b, hb, rfl⟩
    rw [standardComponentCAplus_minimal_id_eq_latticeCut] at hb
    obtain ⟨s, ⟨-, hs⟩, rfl⟩ := hb
    rw [RenardLeviCones.mem_componentPlus_iff_order,
      RenardLeviCones.restrictedSimpleCharacters_minimal] at hs
    apply (mem_rationalMinimalChamber_iff_order i ν _).mpr
    refine ⟨x * s, map_mul _ _ _, fun α hα => ?_⟩
    rw [RenardLeviCones.characterOrder_mul, characterOrder_eq_zero_of_mem_normKernel hx α,
      zero_add]
    exact hs α hα

/-- Intersecting the full chamber with the ambient norm kernel preserves
the same compact-times-section decomposition. -/
theorem rationalMinimalChamberInNormKernel_eq_compactKernel_mul_section
    (hS : IsSplitTorus S.toGrp) :
    rationalMinimalChamberInNormKernel i ν =
      (rationalMinimalTorusCompactKernel i : Set (rationalPoints G)) *
        (Langlands.BruhatTits.SpecialCompact.standardComponentCAplus i ν ∅ (𝟙 S.toGrp) ∩
          (rationalCommonNormKernel G : Set (rationalPoints G))) := by
  ext a
  constructor
  · rintro ⟨ha, ha1⟩
    rw [rationalMinimalChamber_eq_compactKernel_mul_section i ν hS] at ha
    obtain ⟨k, hk, b, hb, rfl⟩ := ha
    refine Set.mem_mul.mpr ⟨k, hk, b, ⟨hb, ?_⟩, rfl⟩
    have hk1 := rationalMinimalTorusCompactKernel_le_normKernel i hk
    have h := (rationalCommonNormKernel G).mul_mem
      ((rationalCommonNormKernel G).inv_mem hk1) ha1
    change b ∈ rationalCommonNormKernel G
    simpa only [inv_mul_cancel_left] using h
  · rintro ⟨k, hk, b, ⟨hb, hb1⟩, rfl⟩
    refine ⟨?_, (rationalCommonNormKernel G).mul_mem
      (rationalMinimalTorusCompactKernel_le_normKernel i hk) hb1⟩
    rw [rationalMinimalChamber_eq_compactKernel_mul_section i ν hS]
    exact Set.mem_mul.mpr ⟨k, hk, b, hb, rfl⟩

section Compactness

variable [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

omit [LocallyOfFiniteType G.X.hom] in
/-- For an actual split torus the mapped intrinsic norm kernel is compact
in the ambient rational-point topology. -/
theorem isCompact_rationalMinimalTorusCompactKernel (hS : IsSplitTorus S.toGrp) :
    IsCompact (rationalMinimalTorusCompactKernel i : Set (rationalPoints G)) := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  let : TopologicalSpace (rationalPoints S.toGrp) := rationalPointTopology F S.X
  exact (SplitTorus.isCompact_commonNormKernel hS).image
    (continuous_rationalPointMap F i.hom.hom)

end Compactness

end Langlands.HarishChandraSchwartz
