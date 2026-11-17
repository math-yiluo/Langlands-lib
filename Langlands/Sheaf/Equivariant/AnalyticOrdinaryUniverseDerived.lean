import Langlands.Sheaf.Equivariant.AnalyticOrdinaryUniverseTransport
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleCohomology
import Langlands.Cohomology.DerivedComparison
import Langlands.Cohomology.TopologicalDerivedSections

/-! # Actual compact cohomology across ordinary universe lift -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

section Additive

variable [HasSheafify (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
  (ModuleCat.{max u (v + 1) uL} R)]

/-- The actual universe-transport equivalence is additive. -/
theorem underlyingTopologyLift_additive :
    (underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.Additive where
  map_add := by
    intro F G f g
    rfl

end Additive

/-- The support-preserving actual sheaf equivalence identifies the existing
ordinary compact right-derived functor with native compact cohomology after lift. -/
def underlyingTopologyLiftCompactCohomologyIso (q : ℕ) :
    underlyingTopologyCompactCohomology.{u, v, uL} X R q ≅
      (underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor ⋙
        TopologicalDerivedSections.compactCohomology
          (TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) R q := by
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := underlyingTopology_enoughInjectives.{u, v, uL} X R
  have := underlyingTopologyCompactSections_additive.{u, v, uL} X R
  have := underlyingTopologyLift_additive.{u, v, uL} X R
  let Φ := underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R)
  let T := (underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor
  let Ψ := Langlands.Sheaf.CompactSupport.functor
    (X := TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) (R := R)
  let e : Φ ⋙ 𝟭 (ModuleCat.{max u (v + 1) uL} R) ≅ T ⋙ Ψ :=
    Functor.rightUnitor Φ ≪≫ underlyingTopologyLiftCompactIso.{u, v, uL} X R
  exact (Functor.rightUnitor _).symm ≪≫
    DerivedComparison.rightDerivedCompIso Φ (𝟭 _) T Ψ e q

/-- Native compact cohomology vanishing on the lifted sheaf transfers to the
existing independent-universe ordinary compact cohomology. -/
theorem isZero_underlyingTopologyCompactCohomology_of_lift
    (F : TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X))
    (q : ℕ)
    (hzero : IsZero ((TopologicalDerivedSections.compactCohomology
      (TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) R q).obj
        ((underlyingTopologyLiftEquivalence.{u, v, uL} X R).functor.obj F))) :
    IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R q).obj F) :=
  hzero.of_iso ((underlyingTopologyLiftCompactCohomologyIso.{u, v, uL} X R q).app F)

end Langlands.Sheaf.Equivariant.Analytic
