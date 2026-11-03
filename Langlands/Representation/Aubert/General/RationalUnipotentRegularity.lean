import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.BruhatTits.Unipotent.JacquetCompactContainmentProof

/-! # Closedness, compact containment and exact Jacquet restriction for standard points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hStandard hG hi hν

/-- At the canonical point topology, the actual standard unipotent subgroup is
closed over any Hausdorff topological field. -/
theorem standardUnipotent_isClosed_of_standardCocharacterStatement [T2Space k]
    (I : Finset (SimpleRoot i ν)) :
    IsClosed (unipotent i ν I : Set (RationalPoint k G.X)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨_, _, hU⟩ := hcompare ζ hζ
  change IsClosed
    (((standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _))) :
      Set (RationalPoint k G.X))
  rw [hU]
  exact BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints
    (CommGroupScheme.groupHom ζ ≫ i)

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Every compact subset of the actual standard unipotent subgroup lies in a
compact subgroup. The dynamic containment theorem discharges this property. -/
theorem standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
    (I : Finset (SimpleRoot i ν)) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨_, _, hU⟩ := hcompare ζ hζ
  change Jacquet.Localization.IsLimitOfCompactSubgroups
    ((standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)))
  rw [hU]
  exact BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
    BruhatTits.dynamicUnipotentCompactOpenContainment k G hG
    (CommGroupScheme.groupHom ζ ≫ i)

/-- A chosen actual compact subgroup containing the supplied compact subset
of the standard unipotent subgroup. -/
def standardUnipotentCompactContainer (I : Finset (SimpleRoot i ν))
    (C : Set (unipotent i ν I)) (hC : IsCompact C) :
    Subgroup (unipotent i ν I) :=
  Classical.choose
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I C hC)

/-- The chosen container is compact and contains the supplied subset. -/
theorem standardUnipotentCompactContainer_spec (I : Finset (SimpleRoot i ν))
    (C : Set (unipotent i ν I)) (hC : IsCompact C) :
    IsCompact
      (standardUnipotentCompactContainer i ν hStandard hG hi hν I C hC :
        Set (unipotent i ν I)) ∧
      C ⊆ (standardUnipotentCompactContainer i ν hStandard hG hi hν I C hC :
        Set (unipotent i ν I)) :=
  Classical.choose_spec
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I C hC)

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Inner conjugation in the actual standard unipotent subgroup has trivial
Haar modulus, for any supplied proof of closedness. -/
theorem standardUnipotent_isUnimodular_of_standardCocharacterStatement
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))) :
    IsUnimodularModulus (unipotent i ν I) hU :=
  isUnimodularModulus_of_isLimitOfCompactSubgroups _ hU
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I)

/-- Actual normalized Jacquet restriction preserves every short exact sequence,
at an independent representation universe and without a compact-limit premise. -/
theorem standardJacquetFunctor_map_isShortExact_of_standardCocharacterStatement
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    {A B C : SmoothRep.{0, _, v} ℂ (RationalPoint k G.X)}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : IsShortExact (hom f) (hom g)) :
    IsShortExact
      (hom ((jacquetFunctor.{_, v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        hU).map f))
      (hom ((jacquetFunctor.{_, v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        hU).map g)) :=
  jacquetFunctor_map_isShortExact _ hU
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) f g hfg

/-- The finite-length exactness predicate follows from the full exactness
theorem, with no assertion about preservation of finite length. -/
theorem standardJacquetFunctor_preservesShortExact_of_standardCocharacterStatement
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X))) :
    PreservesFiniteLengthShortExact
      (jacquetFunctor.{_, v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        hU) :=
  jacquetFunctor_preservesShortExact _ hU
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I)

end Langlands.Aubert.General.RationalPointFamily
