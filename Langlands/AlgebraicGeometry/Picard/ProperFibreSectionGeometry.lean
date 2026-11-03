import Langlands.AlgebraicGeometry.LinearSystem.ProperFibre
import Langlands.AlgebraicGeometry.RelativeProjectiveSpaceFibreAffineOpen
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof

/-! # Ampleness near a proper fibre from a generating power-section system -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite generating power-section system whose generation opens on the
specified scheme-theoretic fibre are affine. -/
structure FibrePowerSectionSystem {X S : Scheme.{u}} (p : X ⟶ S)
    (L : LineBundle X) (s : S) where
  degree : ℕ
  degree_pos : 0 < degree
  dimension : ℕ
  sections : Fin (dimension + 1) → L.powSections degree
  covers : ∀ x : X, ∃ i, x ∈ L.sectionOpen (sections i)
  fibre_affine : ∀ i, IsAffineOpen (p.fiberι s ⁻¹ᵁ L.sectionOpen (sections i))

variable {X S : Scheme.{u}} {p : X ⟶ S} {L : LineBundle X} {s : S}

/-- A generating system with affine opens on a proper fibre makes the fixed
line bundle ample over an affine neighbourhood of the base point. -/
lemma FibrePowerSectionSystem.exists_ample_neighbourhood [IsProper p]
    (D : FibrePowerSectionSystem p L s) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      ((LineBundle.pullback (p ⁻¹ᵁ V).ι).obj L).IsAmple := by
  let K : LineBundle X := ⟨tensorPow L.obj D.degree,
    tensorPow_isLocallyFreeRankOne X L D.degree⟩
  have hσ : ∀ x : X, ∃ i, x ∈ nonvanishingLocus K.obj (D.sections i) := by
    intro x
    obtain ⟨i, hi⟩ := D.covers x
    refine ⟨i, ?_⟩
    rw [lineBundleResidueOpenComparison]
    exact hi
  let φ := LinearSystem.relativeLinearSystemMap p hσ
  let g := RelativeProjectiveSpace.toBase S D.dimension
  obtain ⟨V, hsV, hV, hfin⟩ :=
    LinearSystem.exists_isFinite_relativeLinearSystemMap_restrict p hσ s D.fibre_affine
  let Q : (RelativeProjectiveSpace S D.dimension).Opens := g ⁻¹ᵁ V
  let U : X.Opens := φ ⁻¹ᵁ Q
  have he : U = p ⁻¹ᵁ V := by
    dsimp [U, Q, φ, g]
    rw [← Scheme.Hom.comp_preimage, LinearSystem.relativeLinearSystemMap_toBase]
  have : IsFinite (φ ∣_ Q) := hfin
  have hI : IsAffineHom (Q.ι ≫ RelativeProjectiveSpace.toIntegral S D.dimension) :=
    RelativeProjectiveSpace.isAffineHom_preimage_ι_toIntegral D.dimension V hV
  have hA (i : Fin (D.dimension + 1)) :
      IsAffineOpen (U.ι ⁻¹ᵁ L.sectionOpen (D.sections i)) := by
    have hC : IsAffineOpen (Q.ι ⁻¹ᵁ
        RelativeProjectiveSpace.coordinateOpen S D.dimension i) := by
      rw [RelativeProjectiveSpace.coordinateOpen, ← Scheme.Hom.comp_preimage]
      exact (isAffineOpen_projectiveSpaceCoordinateOpen (ULift.{u} ℤ)
        D.dimension i).preimage (Q.ι ≫ RelativeProjectiveSpace.toIntegral S D.dimension)
    have hP := hC.preimage (φ ∣_ Q)
    have hpre := congrArg
      (fun ψ : U.toScheme ⟶ RelativeProjectiveSpace S D.dimension =>
        ψ ⁻¹ᵁ RelativeProjectiveSpace.coordinateOpen S D.dimension i)
      (morphismRestrict_ι φ Q)
    simp only [Scheme.Hom.comp_preimage] at hpre
    rw [hpre] at hP
    change IsAffineOpen (U.ι ⁻¹ᵁ
      (LinearSystem.relativeLinearSystemMap p hσ ⁻¹ᵁ
        RelativeProjectiveSpace.coordinateOpen S D.dimension i)) at hP
    rw [LinearSystem.relativeLinearSystemMap_preimage] at hP
    exact hP
  have hcompact : CompactSpace U := by
    have hc : IsCompact (U : Set X) := by
      rw [he]
      exact p.isCompact_preimage hV.isCompact
    exact isCompact_iff_compactSpace.mp hc
  have hample : ((LineBundle.pullback U.ι).obj L).IsAmple := by
    refine ⟨hcompact, ?_⟩
    intro x
    obtain ⟨i, hi⟩ := D.covers (U.ι x)
    refine ⟨D.degree, D.degree_pos, L.pullbackPowSection U.ι (D.sections i), ?_, ?_⟩
    · rw [LineBundle.sectionOpen_pullbackPowSection]
      exact hi
    · rw [LineBundle.sectionOpen_pullbackPowSection]
      exact hA i
  refine ⟨V, hsV, hV, ?_⟩
  exact (congrArg (fun W : X.Opens =>
    ((LineBundle.pullback W.ι).obj L).IsAmple) he).mp hample

/-- Choose an affine ampleness neighbourhood from such a section system. -/
def FibrePowerSectionSystem.ampleNeighbourhood [IsProper p]
    (D : FibrePowerSectionSystem p L s) :
    {V : S.Opens // s ∈ V ∧ IsAffineOpen V ∧
      ((LineBundle.pullback (p ⁻¹ᵁ V).ι).obj L).IsAmple} :=
  ⟨D.exists_ample_neighbourhood.choose, D.exists_ample_neighbourhood.choose_spec⟩

end Langlands.AlgebraicGeometry.Picard
