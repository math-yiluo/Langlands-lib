import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonProof
import Langlands.Geometry.Analytic.EquivariantCompactProbeTopology
import Langlands.Geometry.Analytic.QuasiEtaleToEtaleProof
import Langlands.Sheaf.Equivariant.AnalyticEtaleToposComparison.Statement
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Full faithfulness of equivariant change from étale to quasi-étale sheaves

The unit of the change-of-site adjunction on the equivariant compact-probe
site is the map in Berkovich's Corollary 1.4.3.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation

universe u v z uR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (X : GSpace.{u, v, v} K G)
variable (R : Type (max u (v + 1) z uR)) [CommRing R]

local notation "i" => EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X
local notation "Je" => equivariantEtaleTopology X
local notation "Jq" => equivariantCompactProbeQuasiEtaleTopology X

/-- The inclusion of equivariant étale objects is continuous for the
compact-probe topology, by the Hausdorff comparison of the covering rules. -/
private theorem equivariantEtaleToCompactProbe_isContinuous : (i).IsContinuous Je Jq := by
  rw [equivariantCompactProbeQuasiEtaleTopology_eq_of_comparison
    (compactProbeQuasiEtaleHausdorffComparison K) X]
  exact ((quasiEtaleToEtale.{u, v, z} K).2 G X).2

private theorem equivariantCompactProbe_hasSheafify :
    HasSheafify Jq (ModuleCat.{max u (v + 1) z uR} R) := by
  let : Small.{max u (v + 1) z uR} (EquivariantQuasiEtaleSite X) :=
    small_lift.{max u (v + 1) z, uR, max u (v + 1) z} _
  let : LocallySmall.{max u (v + 1) z uR} (EquivariantQuasiEtaleSite X) :=
    ⟨fun V W => small_lift.{max u (v + 1), max z uR, max u (v + 1)} (V ⟶ W)⟩
  exact hasSheafifyEssentiallySmallSite Jq (ModuleCat.{max u (v + 1) z uR} R)

private theorem equivariantEtaleToCompactProbe_hasLeftKanExtension
    (F : (EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) z uR} R) :
    (i).op.HasLeftKanExtension F := by
  let : ∀ U, Small.{max u (v + 1) z uR} (CostructuredArrow (i).op U) :=
    fun U => small_lift.{max u (v + 1) z, uR, max u (v + 1) z} _
  let : (i).op.HasPointwiseLeftKanExtension F := fun U => by
    let : HasColimitsOfShape (CostructuredArrow (i).op U) AddCommGrpCat.{max u (v + 1) z uR} :=
      AddCommGrpCat.hasColimitsOfShape
    exact (ModuleCat.hasColimitsOfShape (J := _) (R := R)).has_colimit _
  exact Functor.HasLeftKanExtension.mk _ (Functor.pointwiseLeftKanExtensionUnit (i).op F)

/-- Sheafification of left Kan extension along the inclusion of the
étale test objects in the equivariant quasi-étale site. -/
def equivariantEtaleToCompactProbeInverseImage :
    Sheaf Je (ModuleCat.{max u (v + 1) z uR} R) ⥤
      Sheaf Jq (ModuleCat.{max u (v + 1) z uR} R) :=
  let := equivariantEtaleToCompactProbe_isContinuous X
  let := equivariantCompactProbe_hasSheafify.{u, v, z, uR} X R
  let := equivariantEtaleToCompactProbe_hasLeftKanExtension.{u, v, z, uR} X R
  Functor.sheafPullbackConstruction.sheafPullback i (ModuleCat.{max u (v + 1) z uR} R) Je Jq

/-- Change of site is left adjoint to restriction to equivariant étale
objects. -/
def equivariantEtaleToCompactProbeAdjunction :
    equivariantEtaleToCompactProbeInverseImage.{u, v, z, uR} X R ⊣
      (let := equivariantEtaleToCompactProbe_isContinuous X
       (i).sheafPushforwardContinuous (ModuleCat.{max u (v + 1) z uR} R) Je Jq) :=
  let := equivariantEtaleToCompactProbe_isContinuous X
  let := equivariantCompactProbe_hasSheafify.{u, v, z, uR} X R
  let := equivariantEtaleToCompactProbe_hasLeftKanExtension.{u, v, z, uR} X R
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous i
    (ModuleCat.{max u (v + 1) z uR} R) Je Jq

/-- Berkovich's Corollary 1.4.3, unit clause for sheaves of modules:
`F ⟶ μ_* μ^* F` is an isomorphism. -/
def EquivariantEtaleToCompactProbeStatement [IsTopologicalGroup G] : Prop :=
  OpenQuotientsSmall.{v, z} (G := G) →
    IsIso (equivariantEtaleToCompactProbeAdjunction.{u, v, z, uR} X R).unit

end Langlands.Sheaf.Equivariant.Analytic
