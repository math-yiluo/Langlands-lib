import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralCoefficientFormula

/-! # The actual split-central mass and normalization of packet preimages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (s : T.toGrp ⟶ G)

/-- The literal central mass occurring in the group-Levi packet Fourier formula,
for the displayed Haar measure on the actual split-component point image. -/
def rationalSplitCentralMass (muA : Measure (rationalPoints.map s).range) : ℝ :=
  (muA (Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (rationalPoints G)))).toReal

/-- The compactness assertion is in the actual central subgroup, not only in
the ambient rational-point group. -/
theorem isCompact_splitCentralNormKernel_preimage (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s) :
    IsCompact (Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (rationalPoints G)) :
      Set (rationalPoints.map s).range) := by
  rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hrange : Set.range (Subtype.val : (rationalPoints.map s).range → rationalPoints G) =
      ((rationalPoints.map s).range : Set (rationalPoints G)) := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hg
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hrange, Set.inter_comm]
  exact isCompact_splitComponent_inf_commonNormKernel G s hG hs

/-- Every Haar measure gives positive finite mass to `A_G(F) ∩ G¹`. -/
theorem splitCentralNormKernel_mass_pos_lt_top (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    0 < muA (Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (rationalPoints G))) ∧
      muA (Subtype.val ⁻¹' (rationalCommonNormKernel G : Set (rationalPoints G))) < ⊤ := by
  have hopen : IsOpen (Subtype.val ⁻¹'
      (rationalCommonNormKernel G : Set (rationalPoints G)) :
        Set (rationalPoints.map s).range) :=
    (isOpen_rationalCommonNormKernel G).preimage continuous_subtype_val
  refine ⟨hopen.measure_pos muA ⟨1, ?_⟩,
    (isCompact_splitCentralNormKernel_preimage s hG hs).measure_lt_top⟩
  exact (rationalCommonNormKernel G).one_mem

/-- The real central mass is strictly positive for arbitrary Haar normalization. -/
theorem rationalSplitCentralMass_pos (hG : IsConnectedReductive G) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    0 < rationalSplitCentralMass s muA := by
  have hm := splitCentralNormKernel_mass_pos_lt_top s hG hs muA
  exact ENNReal.toReal_pos hm.1.ne' hm.2.ne

/-- The complex scalar in the packet projection formula can be divided out. -/
theorem coe_rationalSplitCentralMass_ne_zero (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    (rationalSplitCentralMass s muA : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (rationalSplitCentralMass_pos s hG hs muA).ne'

section Preimage

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- A cuspidal packet whose actual central projection is the source central
mass times a desired function gives an actual raw preimage after scalar division.
The central Haar measure itself is unchanged. -/
theorem mem_rationalCuspidalCentralImage_of_mass_smul (hG : IsConnectedReductive G)
    (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ)
    {φ : RationalSchwartzSpace hKc hPK ρ}
    (hφ : φ ∈ rationalCuspidalSubmodule hKc hPK ρ) {f : rationalPoints G → ℂ}
    (hproj : centralProjection muA χ (φ : rationalPoints G → ℂ) =
      (rationalSplitCentralMass s muA : ℂ) • f) :
    f ∈ rationalCuspidalCentralImage hKc hPK ρ muA χ := by
  let c : ℂ := rationalSplitCentralMass s muA
  have hc : c ≠ 0 := coe_rationalSplitCentralMass_ne_zero s hG hs muA
  refine ⟨c⁻¹ • φ, (rationalCuspidalSubmodule hKc hPK ρ).smul_mem c⁻¹ hφ, ?_⟩
  funext g
  change centralProjection muA χ (fun x => c⁻¹ * φ x) g = f g
  rw [centralProjection_const_mul, hproj]
  change c⁻¹ * (c * f g) = f g
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Preimage

end Langlands.HarishChandraSchwartz
