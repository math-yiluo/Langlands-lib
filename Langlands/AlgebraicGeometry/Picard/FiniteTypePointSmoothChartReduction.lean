import Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartStatement
import Langlands.AlgebraicGeometry.Picard.VersalSmoothNeighbourhoodStatement

/-! # Smooth Picard charts from versal charts and smooth neighbourhoods -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

section PointLift

variable {S : Scheme.{u}} {U V W : Over S}

/-- A map of charts whose image lies in an open subchart, as a map into it. -/
def pointLift (j : V ⟶ U) [IsOpenImmersion j.left] (p : W ⟶ U)
    (h : Set.range p.left ⊆ Set.range j.left) : W ⟶ V :=
  Over.homMk (IsOpenImmersion.lift j.left p.left h) (by
    rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w p])

@[reassoc (attr := simp)]
lemma pointLift_comp (j : V ⟶ U) [IsOpenImmersion j.left] (p : W ⟶ U)
    (h : Set.range p.left ⊆ Set.range j.left) : pointLift j p h ≫ j = p := by
  ext1
  exact IsOpenImmersion.lift_fac j.left p.left h

variable {X : Scheme.{u}} (f : X ⟶ S) (L : LineBundle ((relativeSpace f).obj U))

/-- Pulling back the restricted family along the lifted map is pulling back the
original family along the original map. -/
def pointLiftBundleIso (j : V ⟶ U) [IsOpenImmersion j.left] (p : W ⟶ U)
    (h : Set.range p.left ⊆ Set.range j.left) :
    (LineBundle.pullback ((relativeSpace f).map (pointLift j p h))).obj
        ((LineBundle.pullback ((relativeSpace f).map j)).obj L) ≅
      (LineBundle.pullback ((relativeSpace f).map p)).obj L :=
  (LineBundle.pullbackComp ((relativeSpace f).map (pointLift j p h))
      ((relativeSpace f).map j)).app L ≪≫
    eqToIso (by rw [← Functor.map_comp, pointLift_comp])

end PointLift

open Deformation in
/-- Versal charts at finite-type field points, together with smooth open
neighbourhoods of versal points, give smooth charts through every finite-type
field point. -/
theorem finiteTypePointSmoothChart_of_versal
    (hA : FiniteTypeVersalChartStatement.{u})
    (hB : VersalSmoothNeighbourhoodStatement.{u}) :
    FiniteTypePointSmoothChartStatement.{u} := by
  intro R _ _ X hp hf K _ _ _ L₀
  obtain ⟨U, L, u₀, e, p, hpe, hU, hv, ⟨c⟩⟩ := hA R X hp hf K L₀
  have : LocallyOfFiniteType U.hom := hU
  have hpft : LocallyOfFiniteType p.left := by
    have : LocallyOfFiniteType (p.left ≫ U.hom) := by
      rw [Over.w p]
      change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    exact locallyOfFiniteType_of_comp p.left U.hom
  obtain ⟨V, j, hj, hu, hsm⟩ := hB R X hp hf U hU L u₀ K e p hpe hpft hv
  have : IsOpenImmersion j.left := hj
  have hrange : Set.range p.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    have hx : p.left x = u₀ := by
      rw [hpe]
      exact Scheme.fromSpecResidueField_apply u₀ ((Spec.map e.hom) x)
    rw [hx]
    exact hu
  refine ⟨V, (LineBundle.pullback ((relativeSpace X.hom).map j)).obj L,
    pointLift j p hrange, ?_, hsm, ⟨pointLiftBundleIso X.hom L j p hrange ≪≫ c⟩⟩
  rw [← Over.w j]
  infer_instance

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
