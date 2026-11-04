import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityReductionStatement
import Langlands.Representation.Aubert.General.RationalFiniteChamberCartanCoverProof
import Langlands.Representation.Aubert.General.RationalLatticeQuotientVolumeProof
import Langlands.Representation.Aubert.General.RationalCompactTranslateCoefficientBoundProof
import Langlands.Representation.MatrixCoefficient.CartanLatticeL2Proof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Strict Jacquet square integrability from one joint geometric witness -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

/-- The joint geometry supplies all geometric premises of the actual L2 assembly. -/
theorem rationalStrictJacquetSquareIntegrabilityReduction :
    RationalStrictJacquetSquareIntegrabilityReductionStatement.{u, v} := by
  intro hjoint k _ _ _ _ G hG S i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU A hA hc hstrict _ _ measure _
  classical
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Smooth G.X.hom := hG.smooth
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (SimpleRoot i ν) := hfinite.fintype
  obtain ⟨D, x, Z, j, s, _, _, hsj, h, _, hsc, _, _, _, _, hcompat, hbasis⟩ :=
    hjoint k G hG S i hi ν hν
  obtain ⟨F₀, hF₀⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  obtain ⟨gen, hgenpos, hgenzero, T, hT, hcover, _⟩ :=
    rationalFiniteChamberCartanCover k G hG S i hi ν hν hStandard
      D x Z j s h hsj hsc hcompat F₀ hF₀
  let J : SimpleRoot i ν → Finset (SimpleRoot i ν) := fun a => Finset.univ.erase a
  have hzero : ∀ a β, β ∈ J a → simpleRootPairing i ν β (gen a) = 0 := by
    intro a β hβ
    exact hgenzero a β (Finset.mem_erase.mp hβ).1
  have hpos : ∀ a β, β ∉ J a → 0 < simpleRootPairing i ν β (gen a) := by
    intro a β hβ
    have hβa : β = a := by simpa [J] using hβ
    subst β
    exact hgenpos a
  have hout : ∀ a, ∃ β, β ∉ J a := fun a => ⟨a, by simp [J]⟩
  obtain ⟨z, hz, hcoeff⟩ := rationalCompactTranslateCoefficientBound
    k G hG S i hi ν hν hStandard hU A hA hstrict
      (D.specialCompactSubgroup x) hbasis (SimpleRoot i ν) J gen hzero hpos hout
  let K : OpenSubgroup (RationalPoint k G.X) :=
    ⟨D.specialCompactSubgroup x, hsc.2.1.2.1⟩
  have hK : IsCompact (K : Set (RationalPoint k G.X)) := hsc.2.1.1
  let w (a : SimpleRoot i ν) : ℝ :=
    ((HaarModulus.closedRestrictCharacter (unipotent i ν (J a)) (hU (J a))
      (levi i ν (J a)) (levi_le_normalizer i ν (J a))
      (z a : levi i ν (J a)) : ℝ≥0) : ℝ)⁻¹
  have hw : ∀ a, 0 ≤ w a := by intro a; dsimp [w]; positivity
  obtain ⟨Cvol, hCvol, hvol⟩ := rationalLatticeQuotientVolume
    k G hG S i hi ν hν hStandard hU (D.specialCompactSubgroup x) hbasis
      (SimpleRoot i ν) J gen hzero (fun a β hβ => (hpos a β hβ).le)
      z hz K hK T hT measure
  obtain ⟨c⟩ := hc
  apply cartanLatticeL2 (RationalPoint k G.X) A (SimpleRoot i ν)
    (fun n => uniformizerPowers i (.ofAdd (∑ a, n a • gen a))) w hw
    K.toSubgroup T hT hcover A.representation hA c measure
  · exact ⟨Cvol, hCvol.le, fun n t ht => (hvol n t ht).2⟩
  · intro φ v
    obtain ⟨r, hr, C, hC, hbound⟩ :=
      hcoeff (K : Set (RationalPoint k G.X)) K T hK hK hT φ v
    exact ⟨r, fun a => ⟨(hr a).1.le, (hr a).2⟩, C, hC.le, hbound⟩

end Langlands.Aubert.General.RationalPointFamily
