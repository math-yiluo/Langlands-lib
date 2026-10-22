import Langlands.Cohomology.Continuous.EquivalenceTransport
import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An ambient open subgroup viewed inside another open subgroup. -/
def towerOpenSubgroup (K H : OpenSubgroup G) : OpenSubgroup H :=
  K.comap H.toSubgroup.subtype continuous_subtype_val

omit [IsTopologicalGroup G] in
@[simp]
theorem towerOpenSubgroup_toSubgroup (K H : OpenSubgroup G) :
    (towerOpenSubgroup K H).toSubgroup = K.toSubgroup.subgroupOf H.toSubgroup := rfl

/-- The same coefficients under the canonical equivalence of the two subgroup coordinates. -/
def continuousTowerCoefficientIso (A : DiscreteModule k G)
    {K H : Subgroup G} (h : K ≤ H) :
    TopRep.res (Subgroup.subgroupOfContinuousMulEquivOfLe h : K.subgroupOf H →ₜ* K)
        (A.restrict K).toTopRep ≅
      ((A.restrict H).restrict (K.subgroupOf H)).toTopRep :=
  Iso.refl _

/-- Rebracketing a subgroup tower on actual continuous cohomology. -/
noncomputable def continuousTowerCohomologyIso (A : DiscreteModule k G)
    {K H : Subgroup G} (h : K ≤ H) (q : ℕ) :
    continuousCohomology q (A.restrict K).toTopRep ≅
      continuousCohomology q ((A.restrict H).restrict (K.subgroupOf H)).toTopRep :=
  continuousCohomologyIso (Subgroup.subgroupOfContinuousMulEquivOfLe h)
    (continuousTowerCoefficientIso A h) q

@[simp]
theorem continuousTowerCohomologyIso_hom (A : DiscreteModule k G)
    {K H : Subgroup G} (h : K ≤ H) (q : ℕ) :
    (continuousTowerCohomologyIso A h q).hom =
      ContinuousCohomology.map
        (Subgroup.subgroupOfContinuousMulEquivOfLe h : K.subgroupOf H →ₜ* K)
        (continuousTowerCoefficientIso A h).hom q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Direct restriction agrees with iterated restriction after the canonical tower transport. -/
theorem continuousRestriction_comp_tower (A : DiscreteModule k G)
    {K H : Subgroup G} (h : K ≤ H) (q : ℕ) :
    continuousRestriction A K q ≫ (continuousTowerCohomologyIso A h q).hom =
      continuousRestriction A H q ≫
        continuousRestriction (A.restrict H) (K.subgroupOf H) q := by
  change HomologicalComplex.homologyMap
      (ContinuousCohomology.cochainsMap (subgroupInclusion K)
        (𝟙 (A.restrict K).toTopRep)) q ≫
      HomologicalComplex.homologyMap
        (ContinuousCohomology.cochainsMap
          (Subgroup.subgroupOfContinuousMulEquivOfLe h : K.subgroupOf H →ₜ* K)
          (continuousTowerCoefficientIso A h).hom) q = _
  unfold continuousRestriction
  rw [← HomologicalComplex.homologyMap_comp, ContinuousCohomology.map,
    ContinuousCohomology.map, ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [← ContinuousCohomology.cochainsMap_comp, ← ContinuousCohomology.cochainsMap_comp]
  apply continuousCochainsMap_congr
  · ext g
    rfl
  · intro x
    rfl

end Langlands.Continuous
