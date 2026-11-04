import Langlands.Representation.Aubert.General.RationalLatticeQuotientVolumeStatement
import Langlands.Representation.Aubert.General.RationalRayVolumeIndex
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LatticeQuotientVolumeBound
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Actual full-center lattice-cell volume bounds -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal BigOperators
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology Langlands.HarishChandraSchwartz

namespace Langlands.Aubert.General.RationalPointFamily

/-- The supplied simultaneous basis gives the actual Haar-volume bounds. -/
theorem rationalLatticeQuotientVolume : RationalLatticeQuotientVolumeStatement.{u,w} := by
  intro F _ _ _ _ G hG S i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU K0 hbasis I _ _ J x hx0 hxpos z hz K hK F₀ hF₀ _ _ measure _
  classical
  let : Smooth G.X.hom := hG.smooth
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨B, hB, hBJ⟩ := hbasis
  obtain ⟨L, hLB, hLK⟩ := hB.2.mem_iff.mp (K.isOpen.mem_nhds K.one_mem)
  let Lop : OpenSubgroup (RationalPoint F G.X) := ⟨L, (hB.1 L hLB).2.2.1⟩
  let r (a : I) : ℝ :=
    ((HaarModulus.closedRestrictCharacter (unipotent i ν (J a)) (hU (J a))
      (levi i ν (J a)) (levi_le_normalizer i ν (J a))
      (z a : levi i ν (J a)) : ℝ≥0) : ℝ)⁻¹
  have hr (a : I) : 0 ≤ r a := by dsimp [r]; positivity
  have hray (a : I) :
      doubleCosetIndex L (uniformizerPowers i (.ofAdd (x a))) ≠ 0 ∧
      (doubleCosetIndex L (uniformizerPowers i (.ofAdd (x a))) : ℝ) ≤ r a := by
    obtain ⟨_, A, q, hcomp, hmem⟩ := hBJ (rootSet i ν (J a)) (rootSet_subset i ν (J a))
    have hexists := (hStandard F G hG S i hi ν hν
      (rootSet i ν (J a)) (rootSet_subset i ν (J a))).1
    exact standardBasisMember_rayIndex i ν hi hfinite (J a) hexists (hU (J a))
      q hcomp Lop (hB.1 L hLB).2.2.2 (hmem L hLB) (x a) (hx0 a) (hxpos a) (z a) (hz a)
  exact latticeCentralQuotientVolume K Lop hK (hB.1 L hLB).2.2.2 hLK
    (uniformizerPowers i) x r hr hray F₀ hF₀ measure

end Langlands.Aubert.General.RationalPointFamily
