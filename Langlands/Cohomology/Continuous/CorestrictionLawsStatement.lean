import Langlands.Cohomology.Continuous.Corestriction
import Langlands.Cohomology.Continuous.TowerStageTransport

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- Finite-stage corestriction is transitive through the explicit quotient tower coordinates. -/
def FiniteCorestrictionTower : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A : DiscreteModule k G) (K H : OpenSubgroup G)
    (h : K.toSubgroup ≤ H.toSubgroup) (N : OpenNormalSubgroup G)
    (hNK : N.toSubgroup ≤ K.toSubgroup) (q : ℕ),
    let : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
    finiteCorestriction A.toRep K N hNK q =
      finiteTowerCohomology A h N q ≫
        finiteCorestriction (A.restrict H.toSubgroup).toRep (towerOpenSubgroup K H)
          (restrictOpenNormal H N) (fun _ hn => hNK hn) q ≫
        finiteCorestriction A.toRep H N (fun _ hn => h (hNK hn)) q

/-- Actual continuous transfer agrees with finite transfer at every contained normal stage. -/
def ContinuousCorestrictionFiniteStage : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A : DiscreteModule k G) (H : OpenSubgroup G) (N : OpenNormalSubgroup G)
    (hNH : N.toSubgroup ≤ H.toSubgroup) (q : ℕ),
    finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H N) q ≫
        continuousCorestriction A H q =
      finiteCorestriction A.toRep H N hNH q ≫ finiteStageToContinuous A N q

/-- Actual continuous corestriction commutes with equivariant continuous coefficient maps. -/
def ContinuousCorestrictionNaturality : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A B : DiscreteModule k G) (f : A.toTopRep ⟶ B.toTopRep)
    (H : OpenSubgroup G) (q : ℕ),
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map (ContinuousMonoidHom.id H.toSubgroup)
          ((TopRep.resFunctor H.toSubgroup.subtype).map f) q) ≫
        continuousCorestriction B H q =
      continuousCorestriction A H q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q)

/-- Actual continuous subgroup restriction followed by corestriction multiplies by the index. -/
def ContinuousCorestrictionIndex : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A : DiscreteModule k G) (H : OpenSubgroup G) (q : ℕ),
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousRestriction A H.toSubgroup q) ≫ continuousCorestriction A H q =
      H.toSubgroup.index • 𝟙 ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology q A.toTopRep))

/-- Actual continuous corestriction is transitive through the explicit subgroup coordinates. -/
def ContinuousCorestrictionTower : Prop :=
  ∀ (k G : Type u) [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (A : DiscreteModule k G) (K H : OpenSubgroup G)
    (h : K.toSubgroup ≤ H.toSubgroup) (q : ℕ),
    letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
    continuousCorestriction A K q =
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousTowerCohomologyIso A h q).hom ≫
        continuousCorestriction (A.restrict H.toSubgroup) (towerOpenSubgroup K H) q ≫
        continuousCorestriction A H q

/-- The finite-stage and coefficient compatibility laws for continuous transfer. -/
def ContinuousCorestrictionCompatibility : Prop :=
  ContinuousCorestrictionFiniteStage.{u} ∧ ContinuousCorestrictionNaturality.{u}

/-- The index and transitivity laws for continuous transfer. -/
def ContinuousCorestrictionIndexTower : Prop :=
  ContinuousCorestrictionIndex.{u} ∧ ContinuousCorestrictionTower.{u}

/-- All advertised transfer laws on the actual continuous cohomology modules. -/
def ContinuousCorestrictionLaws : Prop :=
  ContinuousCorestrictionCompatibility.{u} ∧ ContinuousCorestrictionIndexTower.{u}

end Langlands.Continuous
