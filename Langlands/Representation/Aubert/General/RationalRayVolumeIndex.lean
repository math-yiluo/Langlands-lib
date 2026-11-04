import Langlands.Representation.Aubert.General.RationalWeakChamberVolume
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwahoriContractionUpperBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ContractionHaarIndex

/-! # Actual chamber-ray indices from the simultaneous basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily BruhatTits.SpecialCompact HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (RationalPoint F G.X) := pointTopology

/-- Each compatible basis member has its actual double-coset ray index bounded
by the inverse of the actual standard-unipotent Haar modulus. -/
theorem standardBasisMember_rayIndex
    [LocallyCompactSpace (RationalPoint F G.X)]
    [NonarchimedeanGroup (RationalPoint F G.X)]
    (hi : IsMaximalSplitTorus i) (hfinite : (simpleRelativeRoots i ν).Finite)
    (J : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ)
    (hU : IsClosed (unipotent i ν J : Set (RationalPoint F G.X)))
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (q : A.toGrp ⟶ S.toGrp)
    (hcomp : IsCompatibleStandardSplitComponent i ν (rootSet i ν J) A q)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hmem : StandardParabolicBasisMember i ν (rootSet i ν J) q K.toSubgroup)
    (y : cocharacterLattice S)
    (hy : ∀ β ∈ J, simpleRootPairing i ν β y = 0)
    (hypos : ∀ β ∉ J, 0 ≤ simpleRootPairing i ν β y)
    (z : Subgroup.center (levi i ν J))
    (hz : ((z : levi i ν J) : RationalPoint F G.X) =
      uniformizerPowers i (.ofAdd y)) :
    doubleCosetIndex K.toSubgroup (uniformizerPowers i (.ofAdd y)) ≠ 0 ∧
      (doubleCosetIndex K.toSubgroup (uniformizerPowers i (.ofAdd y)) : ℝ) ≤
        ((HaarModulus.closedRestrictCharacter (unipotent i ν J) hU
          (levi i ν J) (levi_le_normalizer i ν J) (z : levi i ν J) : ℝ≥0) : ℝ)⁻¹ := by
  have hgplus := uniformizerPowers_mem_standardComponentCAplus i ν hi hfinite J
    hexists q hcomp y hy hypos
  have hgCA : uniformizerPowers i (.ofAdd y) ∈ standardComponentCA i q := by
    obtain ⟨a, ha, hga⟩ := hgplus
    exact ⟨a, ha.1, hga⟩
  have hweak := hmem.2.2.1 _ hgplus
  let g : Subgroup.normalizer (unipotent i ν J : Set (RationalPoint F G.X)) :=
    ⟨((z : levi i ν J) : RationalPoint F G.X), levi_le_normalizer i ν J z.val.property⟩
  have hindex := contractedIntersection_relIndex K hK (unipotent i ν J) hU g
    (by simpa only [g, hz] using hweak.1)
  have hupper := doubleCosetIndex_le_unipotent_contraction K.toSubgroup
    (levi i ν J) (unipotent i ν J)
    (standardOppositeUnipotentPoints i ν (rootSet i ν J))
    (uniformizerPowers i (.ofAdd y)) hmem.1 (hmem.2.1 _ hgCA) hweak.2
    (by simpa only [g, hz] using hindex.1)
  refine ⟨hupper.1, ?_⟩
  have heq : ((conjSubgroup (uniformizerPowers i (.ofAdd y))
      (K.toSubgroup ⊓ unipotent i ν J)).relIndex
        (K.toSubgroup ⊓ unipotent i ν J) : ℝ) =
      ((HaarModulus.closedRestrictCharacter (unipotent i ν J) hU
        (levi i ν J) (levi_le_normalizer i ν J) (z : levi i ν J) : ℝ≥0) : ℝ)⁻¹ := by
    rw [← hz]
    exact hindex.2
  rw [← heq]
  exact_mod_cast hupper.2

end Langlands.Aubert.General
