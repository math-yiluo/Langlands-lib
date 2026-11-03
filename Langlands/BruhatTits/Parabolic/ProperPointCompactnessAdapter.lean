import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointStatements
import Langlands.AlgebraicGeometry.PointTopology.SchemeHausdorffProofs
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen
import Mathlib.Topology.Category.CompHaus.Basic

/-! # Nonarchimedean specialization of proper-scheme point compactness -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- The original topology of a nonarchimedean local field is nondiscrete. -/
theorem localField_not_discreteTopology : ¬ DiscreteTopology F := by
  intro hd
  let : DiscreteTopology F := hd
  have hopen : IsOpen ({0} : Set F) := isOpen_discrete _
  have hzero : ({0} : Set F) ∈ 𝓝 (0 : F) := hopen.mem_nhds (by simp)
  obtain ⟨r, hr, hball⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hzero
  obtain ⟨γ, hγ, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (r * γ)
  have hxr : ValuativeRel.valuation F x < r := by
    rw [hx]
    simpa using mul_lt_mul_of_pos_left hγ1 (zero_lt_iff.mpr hr)
  have hx0 : x = 0 := Set.mem_singleton_iff.mp (hball hxr)
  have hpos : 0 < r * γ := mul_pos (zero_lt_iff.mpr hr) hγ
  have hmul : r * γ = 0 := by simpa [hx0] using hx.symm
  exact hpos.ne' hmul

/-- Specialize the general proper-point assertion to the exact point carrier
and original field topology consumed by dynamic-parabolic compactness. -/
theorem properSchemePointCompactness_of_localFieldProperty
    (hproper : ∀ (K : Type u) [Field K] [TopologicalSpace K]
      [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
      (hK : ¬ DiscreteTopology K), ProperSchemeLocalPointCompactnessProperty K hK)
    (Q : Over (Spec (CommRingCat.of F))) (hQ : IsProper Q.hom) :
    @CompactSpace (RingPoint F Q F) (schemePointTopology F Q F) := by
  let : T2Space F := localField_t2Space F
  let : IsProper Q.hom := hQ
  exact hproper F (localField_not_discreteTopology F) Q

/-- The full local-field point theorem supplies the same application premise
through its absolute compactness component. -/
theorem properSchemePointCompactness_of_localFieldProperties
    (hproper : ∀ (K : Type u) [Field K] [TopologicalSpace K]
      [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
      (hK : ¬ DiscreteTopology K), LocalFieldProperPointProperties K hK)
    (Q : Over (Spec (CommRingCat.of F))) (hQ : IsProper Q.hom) :
    @CompactSpace (RingPoint F Q F) (schemePointTopology F Q F) :=
  properSchemePointCompactness_of_localFieldProperty F
    (fun K _ _ _ _ _ hK => (hproper K hK).2) Q hQ

/-- Actual proper-scheme points, bundled with their original compact Hausdorff
topology, conditional on the general proper-point assertion. -/
def properSchemePointCompHaus
    (hproper : ∀ (K : Type u) [Field K] [TopologicalSpace K]
      [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
      (hK : ¬ DiscreteTopology K), LocalFieldProperPointProperties K hK)
    (Q : Over (Spec (CommRingCat.of F))) (hQ : IsProper Q.hom) : CompHaus.{u} := by
  let : TopologicalSpace (RingPoint F Q F) := schemePointTopology F Q F
  let : CompactSpace (RingPoint F Q F) :=
    properSchemePointCompactness_of_localFieldProperties F hproper Q hQ
  let : T2Space F := localField_t2Space F
  let : IsProper Q.hom := hQ
  let : T2Space (RingPoint F Q F) := t2Space_schemePointTopology F F Q
  exact CompHaus.of (RingPoint F Q F)

@[simp] theorem properSchemePointCompHaus_coe
    (hproper : ∀ (K : Type u) [Field K] [TopologicalSpace K]
      [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
      (hK : ¬ DiscreteTopology K), LocalFieldProperPointProperties K hK)
    (Q : Over (Spec (CommRingCat.of F))) (hQ : IsProper Q.hom) :
    (properSchemePointCompHaus F hproper Q hQ : Type u) = RingPoint F Q F := rfl

@[simp] theorem properSchemePointCompHaus_topology
    (hproper : ∀ (K : Type u) [Field K] [TopologicalSpace K]
      [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
      (hK : ¬ DiscreteTopology K), LocalFieldProperPointProperties K hK)
    (Q : Over (Spec (CommRingCat.of F))) (hQ : IsProper Q.hom) :
    (properSchemePointCompHaus F hproper Q hQ).toTop.str =
      schemePointTopology F Q F := rfl

end Langlands.BruhatTits
