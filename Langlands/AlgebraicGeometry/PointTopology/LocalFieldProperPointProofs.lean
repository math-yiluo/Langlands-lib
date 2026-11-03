import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointStatements
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointLimits
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldUltrapower
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperCompactnessReduction

/-! # Proper maps on actual points over locally compact fields: proofs -/

noncomputable section

universe u

open CategoryTheory Topology Filter
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [Field K] [TopologicalSpace K]

/-- Proper relative morphisms induce proper maps on actual points. -/
theorem schemePointLocalProperness_proof
    [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
    (hnondiscrete : ¬ DiscreteTopology K) :
    SchemePointLocalPropernessProperty K hnondiscrete := by
  intro X Y _ _ _ _ _ _ f _
  let _ : TopologicalSpace (RingPoint K X K) := schemePointTopology K X K
  let _ : TopologicalSpace (RingPoint K Y K) := schemePointTopology K Y K
  refine (isProperMap_iff_ultrafilter (X := RingPoint K X K) (Y := RingPoint K Y K)
    (f := fun p => (p ≫ f : RingPoint K Y K))).mpr
    ⟨schemePointContinuity_proof K K X Y f, fun 𝒰 y hy => ?_⟩
  obtain ⟨x, hxy, hx⟩ := exists_limit_of_valuationSubring f 𝒰 id y hy
    (ultrapowerMap K 𝒰)
    (fun g₁ g₂ h => by rw [ultrapowerMap_apply, ultrapowerMap_apply]; exact Germ.coe_eq.2 h)
    (convergentGerms K 𝒰 hnondiscrete) (standardPart K 𝒰 hnondiscrete)
    (fun g c hg => (mem_convergentGerms_iff K 𝒰 hnondiscrete).2 ⟨c, hg⟩)
    (fun a g h => tendsto_standardPart K 𝒰 hnondiscrete a h)
  exact ⟨x, hxy, tendsto_id'.mp hx⟩

/-- Local properness and compactness of actual points of proper schemes. -/
theorem localFieldProperPointProperties_proof
    [IsTopologicalDivisionRing K] [T2Space K] [LocallyCompactSpace K]
    (hnondiscrete : ¬ DiscreteTopology K) :
    LocalFieldProperPointProperties K hnondiscrete :=
  ⟨schemePointLocalProperness_proof K hnondiscrete,
    properSchemeLocalPointCompactness_of_properness K hnondiscrete
      (schemePointLocalProperness_proof K hnondiscrete)⟩

end Langlands.AlgebraicGeometry.PointTopology
