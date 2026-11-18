import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.BruhatTits.SpecialCompact.InheritedNormalBasis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights

/-! # Localizing a supplied simultaneous standard basis

The structural subgroup need not itself be compact or open. A compact
open member of its basis has the same simultaneous property, and can be
chosen inside any prescribed open subgroup.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Generic

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- The subfamily of a subgroup basis contained in a specified subgroup. -/
def normalBasisBelow (B : Set (Subgroup Γ)) (L : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | K ∈ B ∧ K ≤ L}

/-- Restricting to an open subgroup below the structural normalizer gives
a cofinal normal compact-open basis for that subgroup. -/
theorem CompactOpenNormalBasis.restrict_below
    {K0 L : Subgroup Γ} {B : Set (Subgroup Γ)}
    (hB : CompactOpenNormalBasis K0 B) (hL : L ≤ K0)
    (hLo : IsOpen (L : Set Γ)) :
    CompactOpenNormalBasis L (normalBasisBelow B L) := by
  constructor
  · rintro K ⟨hKB, hKL⟩
    obtain ⟨hKK0, hKN, hKo, hKc⟩ := hB.1 K hKB
    refine ⟨hKL, ?_, hKo, hKc⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr
      (hL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKK0).mp hKN))
  · refine hasBasis_iff.mpr fun V => ⟨?_, ?_⟩
    · intro hV
      obtain ⟨K, hKB, hK⟩ :=
        hB.2.mem_iff.mp (inter_mem hV (hLo.mem_nhds L.one_mem))
      exact ⟨K, ⟨hKB, fun x hx => (hK hx).2⟩, fun x hx => (hK hx).1⟩
    · rintro ⟨K, ⟨hKB, hKL⟩, hKV⟩
      exact mem_of_superset (hB.2.mem_of_mem hKB) hKV

end Generic

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K0 : Subgroup (rationalPoints G)}

attribute [local instance] HarishChandraSchwartz.rationalWeightsIsAffine
  HarishChandraSchwartz.rationalWeightsTopology
  HarishChandraSchwartz.rationalWeightsTopologicalGroup
  HarishChandraSchwartz.rationalWeightsT2Field
  HarishChandraSchwartz.rationalWeightsLocallyCompact

omit [LocallyOfFiniteType G.X.hom] in
/-- A supplied simultaneous basis can be localized inside any prescribed
open subgroup, keeping its actual split components and basis properties.
No compactness or openness of the original structural subgroup is needed. -/
theorem SimultaneousStandardBasisAt.exists_compactOpen_le
    (h : SimultaneousStandardBasisAt i ν K0)
    (H : OpenSubgroup (rationalPoints G)) :
    ∃ L : OpenSubgroup (rationalPoints G),
      IsCompact (L : Set (rationalPoints G)) ∧ L ≤ H ∧ L.toSubgroup ≤ K0 ∧
        SimultaneousStandardBasisAt i ν L.toSubgroup := by
  obtain ⟨B, hB, hstd⟩ := h
  obtain ⟨L, hLB, hLH⟩ := hB.2.mem_iff.mp (H.isOpen.mem_nhds H.one_mem)
  obtain ⟨hLK0, -, hLo, hLc⟩ := hB.1 L hLB
  have hBL := hB.restrict_below hLK0 hLo
  refine ⟨⟨L, hLo⟩, hLc, hLH, hLK0, normalBasisBelow B L, hBL, ?_⟩
  intro J hJ
  obtain ⟨-, A, q, hA, hmember⟩ := hstd J hJ
  refine ⟨hBL.inherited (isClosed_standardLeviPoints i ν J),
    A, q, hA, ?_⟩
  intro K hK
  exact hmember K hK.1

end Rational

end Langlands.BruhatTits.SpecialCompact
