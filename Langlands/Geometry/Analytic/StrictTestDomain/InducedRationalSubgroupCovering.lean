import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpectrum
import Langlands.Topology.GroupAction.InducedSubgroupCovering

/-! # Coverings for actual rational-spectrum subgroup restriction -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable {U V : OpenSubgroup G} (h : V ≤ U) (d : ρ.InvariantRationalDomain U)

/-- The actual subgroup-change arrow retains the identity point label. -/
@[simp]
theorem subgroupRestriction_label : (subgroupRestriction h d).label = 1 := rfl

/-- The original bounded identity pullback induces the identity on the original spectrum. -/
@[simp]
theorem subgroupRestriction_localSpectrumMap (x : BanachSpectrum d.obj.algebra) :
    (subgroupRestriction h d).localSpectrumMap x = x := by
  change BanachSpectrum.comap (subgroupRestriction h d).restriction.toBoundedRingHom x = x
  rw [subgroupRestriction_restriction]
  exact BanachSpectrum.ext fun _ => rfl

/-- The original source action is exactly the restriction of the original target action. -/
theorem subgroupRestriction_localSpectrumAction :
    letI : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
    localSpectrumSubgroupMulAction
        ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)) =
      MulAction.compHom ((inclusion U).obj d).LocalSpectrum
        (Subgroup.inclusion (show V.toSubgroup ≤ U.toSubgroup from h)) := rfl

set_option maxHeartbeats 800000 in
/-- The original rational transport map is exactly the generic subgroup map. -/
theorem subgroupRestriction_inducedMap_eq :
    letI : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
    let : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
    (subgroupRestriction h d).inducedMap =
      TopologicalInduction.subgroupMap
        (X := ((inclusion U).obj d).LocalSpectrum)
        (show V.toSubgroup ≤ U.toSubgroup from h) := by
  let : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
  let : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
  ext z
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨g, x⟩
    change (subgroupRestriction h d).inducedMap
      (((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).inducedMk g x) = _
    rw [Hom.inducedMap_mk, subgroupRestriction_label]
    erw [subgroupRestriction_localSpectrumMap h d x]
    rw [inv_one, mul_one]
    exact (TopologicalInduction.subgroupMap_mk
      (X := ((inclusion U).obj d).LocalSpectrum)
      (show V.toSubgroup ≤ U.toSubgroup from h) g x).symm

set_option maxHeartbeats 800000 in
/-- A product chart for the unchanged original rational subgroup-change map. -/
def subgroupRestrictionProductHomeomorph :
    ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).InducedSpectrum ≃ₜ
      ((inclusion U).obj d).InducedSpectrum × (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) := by
  letI : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
  letI : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
  exact TopologicalInduction.subgroupProductHomeomorph
    (X := ((inclusion U).obj d).LocalSpectrum)
    (show V.toSubgroup ≤ U.toSubgroup from h) V.isOpen' U.isOpen'

set_option maxHeartbeats 800000 in
/-- Its first coordinate is the original rational map, with no map replacement. -/
@[simp]
theorem subgroupRestrictionProductHomeomorph_fst
    (z : ((inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d)).InducedSpectrum) :
    (subgroupRestrictionProductHomeomorph h d z).1 =
      (subgroupRestriction h d).inducedMap z := by
  let : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
  let : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
  rw [subgroupRestriction_inducedMap_eq]
  exact TopologicalInduction.subgroupProductHomeomorph_fst
    (X := ((inclusion U).obj d).LocalSpectrum)
    (show V.toSubgroup ≤ U.toSubgroup from h) V.isOpen' U.isOpen' z

set_option maxHeartbeats 800000 in
/-- Every original target point is evenly covered with all relative cosets. -/
theorem subgroupRestriction_inducedMapEvenlyCovered
    (y : ((inclusion U).obj d).InducedSpectrum) :
    IsEvenlyCovered (subgroupRestriction h d).inducedMap y
      (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) := by
  let : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
  let : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
  rw [subgroupRestriction_inducedMap_eq]
  exact TopologicalInduction.subgroupMapEvenlyCovered
    (show V.toSubgroup ≤ U.toSubgroup from h) V.isOpen' U.isOpen' y

/-- The actual rational subgroup-change map is a covering without an index premise. -/
theorem isCoveringMap_subgroupRestriction_inducedMap :
    IsCoveringMap (subgroupRestriction h d).inducedMap :=
  fun y => (subgroupRestriction_inducedMapEvenlyCovered h d y).to_isEvenlyCovered_preimage

/-- Relative cosets identify the entire literal fiber of the original rational map. -/
def subgroupRestrictionFiberHomeomorph
    (y : ((inclusion U).obj d).InducedSpectrum) :
    (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup) ≃ₜ
      (subgroupRestriction h d).inducedMap ⁻¹' {y} :=
  (subgroupRestriction_inducedMapEvenlyCovered h d y).fiberHomeomorph

/-- Finite relative cosets give finite entire original fibers. -/
theorem finite_subgroupRestriction_inducedMap_fiber
    [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]
    (y : ((inclusion U).obj d).InducedSpectrum) :
    Finite ((subgroupRestriction h d).inducedMap ⁻¹' {y}) :=
  Finite.of_equiv (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)
    (subgroupRestrictionFiberHomeomorph h d y).toEquiv

/-- The actual map has precisely the relative index as its fiber cardinality. -/
theorem card_subgroupRestriction_inducedMap_fiber
    (y : ((inclusion U).obj d).InducedSpectrum) :
    Nat.card ((subgroupRestriction h d).inducedMap ⁻¹' {y}) =
      V.toSubgroup.relIndex U.toSubgroup :=
  Nat.card_congr (subgroupRestrictionFiberHomeomorph h d y).toEquiv.symm

set_option maxHeartbeats 800000 in
/-- Finite relative cosets make the actual rational subgroup-change map proper. -/
theorem isProperMap_subgroupRestriction_inducedMap
    [Finite (U ⧸ V.toSubgroup.subgroupOf U.toSubgroup)] :
    IsProperMap (subgroupRestriction h d).inducedMap := by
  let : MulAction U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupMulAction ((inclusion U).obj d)
  let : ContinuousSMul U.toSubgroup ((inclusion U).obj d).LocalSpectrum :=
      localSpectrumSubgroupContinuousSMul ((inclusion U).obj d)
  rw [subgroupRestriction_inducedMap_eq]
  exact TopologicalInduction.isProperMap_subgroupMap
    (show V.toSubgroup ≤ U.toSubgroup from h) V.isOpen' U.isOpen'

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
