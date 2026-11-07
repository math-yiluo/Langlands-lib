import Langlands.AlgebraicGeometry.Picard.PointFiberArtinianLifting
import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement
import Langlands.AlgebraicGeometry.Picard.VersalSmoothNeighbourhoodStatement

/-! # Smooth open neighbourhoods of versal points, from openness of versality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation

/-- Openness of versality for actual Picard families gives, around every versal
finite-type point of a locally finite-type family, an open subscheme over which
the restricted family has smooth actual point fibres. -/
theorem versalSmoothNeighbourhood_of_openness
    (hO : PicardOpennessOfVersalityStatement.{u}) :
    VersalSmoothNeighbourhoodStatement.{u} := by
  intro R _ _ X hprop hflat U hU L u₀ K _ _ e p hp hlft hv
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : IsProper X.hom := hprop
  have : Flat X.hom := hflat
  have : LocallyOfFiniteType U.hom := hU
  have : LocallyOfFinitePresentation X.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨W, hW, hVers⟩ := hO R X hprop hflat U hU L u₀ K p e hp hlft hv
  let V : Over (Spec (CommRingCat.of R)) := Over.mk (W.ι ≫ U.hom)
  let j : V ⟶ U := Over.homMk W.ι rfl
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion W.ι
    infer_instance
  have : LocallyOfFiniteType V.hom := by
    change LocallyOfFiniteType (W.ι ≫ U.hom)
    infer_instance
  refine ⟨V, j, hj, ?_, ?_⟩
  · change u₀ ∈ Set.range W.ι
    rw [Scheme.Opens.range_ι]
    exact hW
  · refine PointFiberArtinianLifting.exists_smooth_pointFiberScheme_of_versal X.hom
      (restrictBundle X.hom L j) (fun K' _ _ p' hp' ↦ ?_)
    apply PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle
    refine hVers K' (p' ≫ j) ?_ ?_
    · change LocallyOfFiniteType (p'.left ≫ W.ι)
      infer_instance
    · rintro _ ⟨z, rfl⟩
      change W.ι (p'.left z) ∈ (W : Set U.left)
      rw [← Scheme.Opens.range_ι W]
      exact Set.mem_range_self _

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
