import Langlands.Global.AdelicSubgroupHaarNormalization
import Langlands.Global.AdelicSubgroupQuotientTransport
import Langlands.Global.DiscreteLeftCosetMeasureTransport

/-! # Transport of quotient-normalized measures on actual adelic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicSubgroupPoints

namespace AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  (e : G ≅ H) (V : SubgroupFunctor H)
  [hV : IsClosed (adelicPoints F H V : Set (AdelicGroupPoints F H))]

/-- The isomorphism on actual adelic subgroups preserves the Library measure
`normalizedHaarMeasure`. The scale is the reciprocal of the principal
quotient mass, with infinite mass giving the zero measure. -/
theorem measurePreserving_adelicSubgroupIso_normalizedHaarMeasure :
    letI := isClosed_adelicPoints_comap F e V
    MeasurePreserving (adelicSubgroupIso F e V)
      (normalizedHaarMeasure F G (V.comap e.hom)) (normalizedHaarMeasure F H V) := by
  let hU := isClosed_adelicPoints_comap F e V
  let A := adelicPoints F G (V.comap e.hom)
  let B := adelicPoints F H V
  let : LocallyCompactSpace A := hU.locallyCompactSpace
  let : LocallyCompactSpace B := hV.locallyCompactSpace
  let a := adelicSubgroupIso F e V
  let sourceHaar : Measure A := Measure.haar
  let targetHaar : Measure B := Measure.map a sourceHaar
  let : targetHaar.IsHaarMeasure := a.isHaarMeasure_map sourceHaar
  have ha : MeasurePreserving a sourceHaar targetHaar := ⟨a.continuous.measurable, rfl⟩
  let Γ := rationalSubgroup F G (V.comap e.hom)
  let Λ := rationalSubgroup F H V
  let hΓ := isDiscrete_rationalSubgroup F G (V.comap e.hom)
  let hΛ := isDiscrete_rationalSubgroup F H V
  have hq := LeftCosetSpace.measurePreserving_discreteQuotientMeasure a Γ Λ
    (adelicSubgroupIso_mem_rationalSubgroup_iff F e V) hΓ hΛ sourceHaar targetHaar ha
  have hv : targetHaar (LeftCosetSpace.fundamentalDomain Λ hΛ) =
      sourceHaar (LeftCosetSpace.fundamentalDomain Γ hΓ) := by
    have hm := congrArg (fun M : Measure (LeftCosetSpace Λ) => M univ) hq.map_eq
    rw [Measure.map_apply hq.measurable MeasurableSet.univ, preimage_univ,
      LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
      LeftCosetSpace.quotientMeasure_univ, LeftCosetSpace.quotientMeasure_univ] at hm
    exact hm.symm
  refine ⟨ha.measurable, ?_⟩
  change Measure.map a (normalizedHaarMeasure F G (V.comap e.hom)) = normalizedHaarMeasure F H V
  rw [← normalizedHaarMeasureFrom_eq F G (V.comap e.hom) sourceHaar,
    ← normalizedHaarMeasureFrom_eq F H V targetHaar]
  change Measure.map a ((sourceHaar (LeftCosetSpace.fundamentalDomain Γ hΓ))⁻¹ • sourceHaar) =
    (targetHaar (LeftCosetSpace.fundamentalDomain Λ hΛ))⁻¹ • targetHaar
  rw [hv, Measure.map_smul _ ha.measurable.aemeasurable]

/-- The same transport applies to any closed subgroup functor identified
with the inverse image. It preserves the principal subgroup as well. -/
theorem exists_adelicSubgroupIso_of_eq_comap
    (U : SubgroupFunctor G) [IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
    (hU : U = V.comap e.hom) :
    ∃ a : adelicPoints F G U ≃ₜ* adelicPoints F H V,
      (∀ x, (a x : AdelicGroupPoints F H) =
        G.affinePointsTarget e.hom (CommAlgCat.of F (AdeleRing (𝓞 F) F)) x) ∧
      (∀ x, a x ∈ rationalSubgroup F H V ↔ x ∈ rationalSubgroup F G U) ∧
      MeasurePreserving a (normalizedHaarMeasure F G U) (normalizedHaarMeasure F H V) := by
  subst U
  exact ⟨adelicSubgroupIso F e V, fun _ => rfl, adelicSubgroupIso_mem_rationalSubgroup_iff F e V,
    measurePreserving_adelicSubgroupIso_normalizedHaarMeasure F e V⟩

end AdelicSubgroupPoints

/-- Ambient isomorphisms transport the Library quotient-normalized measure
of an actual closed adelic subgroup to that of its image. -/
def AdelicSubgroupNormalizedHaarTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (e : G ≅ H) (V : SubgroupFunctor H)
    [IsClosed (adelicPoints F H V : Set (AdelicGroupPoints F H))],
    letI := isClosed_adelicPoints_comap F e V
    MeasurePreserving (adelicSubgroupIso F e V)
      (normalizedHaarMeasure F G (V.comap e.hom)) (normalizedHaarMeasure F H V)

theorem adelicSubgroupNormalizedHaarTransport : AdelicSubgroupNormalizedHaarTransportStatement.{u} := by
  intro F _ _ G H _ _ _ _ e V _
  exact measurePreserving_adelicSubgroupIso_normalizedHaarMeasure F e V

end Langlands.Global
