import Langlands.Representation.Geometric.GeometricFineScalarCoordinates
import Langlands.Representation.Geometric.ChamberRealPartProjection
import Langlands.Representation.Exponents.CentralEigencharacterExtensionProof
import Langlands.Representation.Parabolic.UpperRefinedJacquetAdmissibilityProof
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Geometric.RefinedJacquetRealTwist
import Langlands.Representation.Classification.MaximalConeLifting

/-! Source untwisting in the actual geometric-piece real projection. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear Finset
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

set_option maxHeartbeats 1200000 in
/-- Actual coarse occurrence for a real-twisted source gives a genuine open
fine character of the untwisted source Jacquet action and the exact coarse
projection, including the source coarse twist on every diagonal coordinate. -/
theorem geometricPiece_untwisted_real_projection :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsAdmissible A.representation →
    ∀ t : Fin B.length → ℝ,
    let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
      ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
    ∀ (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ)
      (y : Fin C.length → ℝ),
    IsGeneralizedEigencharacter
      ((((geometricPieceFunctor T B C w S R hS hR).obj At).ρ).comp
        (C.blockScalarLevi F.Carrier)) χ →
    T.IsRealPartOf χ y →
    ∃ (ψ : (Fin (B.flatten S).length → F.Carrierˣ) →* ℂˣ)
      (x : Fin (B.flatten S).length → ℝ),
      IsOpen (ψ.ker : Set (Fin (B.flatten S).length → F.Carrierˣ)) ∧
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet B S A.representation).comp
          (flattenedBlockScalar B S F.Carrier)) ψ ∧
      T.IsRealPartOf ψ x ∧
      ∀ j : Fin C.length,
        (∑ b : Fin (C.size j),
          (x (blockIndex (B.flatten S) (w.symm (C.index j b))) /
            ((B.flatten S).size (blockIndex (B.flatten S) (w.symm (C.index j b))) : ℝ) +
            t (blockIndex B (w.symm (C.index j b))))) = y j := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro A hadm t
  dsimp only
  intro χ y hχ hy
  let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
    ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
  let φ := flattenedBlockScalar B S F.Carrier
  let β := chamberRestriction B C w S F.Carrier
  let η := ((T.leviRealPowerCharacter B t).comp
    (refinedLevi F.Carrier B S).subtype).comp φ
  have href := geometricPiece_coarse_character_reflects_fineScalars
    B C w S R T hS hR At χ hχ
  have href0 : IsGeneralizedEigencharacter
      (((T.normalizedRefinedJacquet B S A.representation).comp φ).comp β)
      (χ * (η.comp β)⁻¹) :=
    (T.normalizedRefinedJacquetRealTwist_isGeneralizedEigencharacter_iff
      B S A.representation t (φ.comp β) χ).mp href
  obtain ⟨ψ, hopen, hgen, hext⟩ := exists_eigencharacter_extension
    (T.normalizedRefinedJacquet B S A.representation)
    (Parabolic.isAdmissible_normalizedRefinedJacquet F T B S _ A.representation hadm)
    φ (continuous_flattenedBlockScalar B S F.Carrier)
    (flattenedBlockScalar_commute B S F.Carrier) β (χ * (η.comp β)⁻¹) href0
  obtain ⟨x, hx⟩ := T.exists_isRealPartOf ψ hopen
  have hη : η =
      (T.leviRealPowerCharacter (B.flatten S) (fun k => t (B.flattenOuter S k))).comp
        ((B.flatten S).blockScalarLevi F.Carrier) := by
    apply MonoidHom.ext
    intro a
    exact T.leviRealPowerCharacter_flatten B S t ((B.flatten S).blockScalarLevi F.Carrier a)
  have hxt : T.IsRealPartOf (ψ * η)
      (fun k => x k + ((B.flatten S).size k : ℝ) * t (B.flattenOuter S k)) := by
    rw [hη]
    exact T.isRealPartOf_mul_leviRealPowerCharacter (B.flatten S) hx
      (fun k => t (B.flattenOuter S k))
  have hextt : (ψ * η).comp β = χ := by
    apply MonoidHom.ext
    intro a
    have ha := congrArg (fun f : (Fin C.length → F.Carrierˣ) →* ℂˣ => f a) hext
    change ψ (β a) = χ a * (η (β a))⁻¹ at ha
    change ψ (β a) * η (β a) = χ a
    rw [ha, mul_assoc, inv_mul_cancel, mul_one]
  have hproj := ChamberProjection.diagonal_projection_of_character_extension
    T B C w S hS hxt hy hextt
  have hdivide (a : Fin n) :
      (x (blockIndex (B.flatten S) a) +
          ((B.flatten S).size (blockIndex (B.flatten S) a) : ℝ) *
            t (B.flattenOuter S (blockIndex (B.flatten S) a))) /
          ((B.flatten S).size (blockIndex (B.flatten S) a) : ℝ) =
        x (blockIndex (B.flatten S) a) /
          ((B.flatten S).size (blockIndex (B.flatten S) a) : ℝ) + t (blockIndex B a) := by
    have hd : ((B.flatten S).size (blockIndex (B.flatten S) a) : ℝ) ≠ 0 := by
      exact_mod_cast ((B.flatten S).positive (blockIndex (B.flatten S) a)).ne'
    rw [ProductLeviMinimalIndex.blockIndex_eq_flatten B S a]
    change (_ + _ * t _) / _ = _ / _ + t _
    dsimp only [BlockShape.flattenOuter]
    field_simp
  refine ⟨ψ, x, hopen, hgen, hx, ?_⟩
  intro j
  simpa only [hdivide] using hproj j

end Langlands.Geometric
