import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenStatements
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Whole section generation opens of an ample line bundle form a basis -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- The affine generation opens supplied by ampleness imply quasi-separatedness. -/
theorem LineBundle.IsAmple.quasiSeparatedSpace {X : Scheme.{u}} {L : LineBundle X}
    (hL : L.IsAmple) : QuasiSeparatedSpace X := by
  classical
  choose n hn s hx hs using hL.2
  let U : X → X.Opens := fun x ↦ L.sectionOpen (s x)
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U ?_ (fun x ↦ hs x) ?_
  · change iSup U = ⊤
    refine eq_top_iff.mpr fun x _ ↦ ?_
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x y
    let M : LineBundle X := ⟨tensorPow L.obj (n y), tensorPow_isLocallyFreeRankOne X L (n y)⟩
    exact (affineGenerationLocusIntersection X M (s y) (U x) (hs x)).isCompact

/-- Whole generation opens of positive-power sections of an ample line bundle
form a basis of the topology. -/
theorem ampleSectionOpenBasis : AmpleSectionOpenBasisStatement.{u} := by
  intro X L hL W x hxW
  let : CompactSpace X := hL.compactSpace
  let : QuasiSeparatedSpace X := hL.quasiSeparatedSpace
  obtain ⟨n, hn, s, hxs, ha⟩ := hL.exists_section x
  obtain ⟨r, hrW, hxr⟩ := ha.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxs
  let M : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  obtain ⟨m, hm, t, ht⟩ := principalGenerationOpenLift X M s r
  let e := tensorPowMulIso L.obj n m
  have hOpen : L.sectionOpen (e.hom.app ⊤ t) = X.basicOpen r :=
    (trivializationOpen_mapIso e t).trans ht
  refine ⟨n * m, by simpa using Nat.mul_le_mul hn hm, e.hom.app ⊤ t, ?_, ?_⟩
  · rw [hOpen]
    exact hxr
  · rw [hOpen]
    exact hrW

/-- A direct consumer of the ample section-open basis theorem. -/
theorem ampleSectionOpenBasis_apply (X : Scheme.{u}) (L : LineBundle X)
    (hL : L.IsAmple) (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
      x ∈ L.sectionOpen s ∧ L.sectionOpen s ≤ W :=
  ampleSectionOpenBasis X L hL W x hx

end Langlands.AlgebraicGeometry.Picard
