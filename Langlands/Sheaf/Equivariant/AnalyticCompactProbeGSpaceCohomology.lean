import Langlands.Geometry.Analytic.CommonPointField.Choice
import Langlands.Sheaf.Equivariant.AnalyticCompactProbeCompactCohomology

/-! # Compactly supported cohomology of continuous Hausdorff analytic actions -/

noncomputable section

universe u v uL z w

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : GSpace.{u, v, v} K G)

/-- A Hausdorff analytic group space has finite refinements by discrete test objects
for the twisted compact-probe topology. -/
theorem compactProbeGSpace_hasFiniteEquivariantRefinements :
    (compactLiftSystem X.obj.ρAut).HasFiniteEquivariantRefinements
      (twistedCompactProbeQuasiEtaleTopology X.obj.ρAut) :=
  compactProbe_hasFiniteEquivariantRefinements X.obj.ρAut X.property.1 X.property.2

variable (R : Type (max u (v + 1) uL)) [CommRing R] [Small.{max u (v + 1) uL} G]

/-- Smooth compactly supported cohomology for the actual continuous action, using a
common field that realizes every point of the space. -/
def compactProbeGSpaceCompactCohomology (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := compactProbeGSpace_hasFiniteEquivariantRefinements X
  let L := chooseCommonPointField.{u, v, uL} X.obj.V
  compactProbeQuasiEtaleGSheafCompactCohomology L.carrier X.obj.ρAut R q

variable [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The bounded below complex of compactly supported smooth sections for the actual
continuous action. -/
def compactProbeGSpaceCompactComplex :
    CompactProbeQuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  haveI := compactProbeGSpace_hasFiniteEquivariantRefinements X
  let L := chooseCommonPointField.{u, v, uL} X.obj.V
  compactProbeQuasiEtaleGSheafCompactComplex L.carrier X.obj.ρAut R

/-- The degreewise functor computes the homology of the selected derived complex. -/
def compactProbeGSpaceCompactHomologyIso
    (F : CompactProbeQuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((compactProbeGSpaceCompactComplex.{u, v, uL} X R).obj F) ≅
      (compactProbeGSpaceCompactCohomology.{u, v, uL} X R q).obj F :=
  haveI := compactProbeGSpace_hasFiniteEquivariantRefinements X
  let L := chooseCommonPointField.{u, v, uL} X.obj.V
  compactProbeQuasiEtaleGSheafCompactComplexHomologyIso L.carrier X.obj.ρAut R F q

/-- Compactly supported derived sections applied to a coefficient inverse diagram. -/
def compactProbeGSpaceCompactCoefficientSystem
    (T : ℕᵒᵖ ⥤ CompactProbeQuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{max u (v + 1) uL} R)) :
    ℕᵒᵖ ⥤ DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  T ⋙ compactProbeGSpaceCompactComplex.{u, v, uL} X R

end Langlands.Sheaf.Equivariant.Analytic
