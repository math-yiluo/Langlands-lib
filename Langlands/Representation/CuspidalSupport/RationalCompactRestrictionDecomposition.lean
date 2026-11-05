import Langlands.Representation.CompactCoefficient.SubquotientDecomposition
import Langlands.Representation.CuspidalSupport.RationalCompactRestrictionInertiaReduction
import Langlands.Topology.Nonarchimedean.Subgroup

/-!
# Actual norm-kernel compact projector from fixed-level finiteness

The actual norm kernel is open in the canonical rational-point topology.
Its Haar measure and the published intrinsic complement theorem remove the
complement hypothesis from the normal-subgroup projector construction.
Fixed-level finiteness remains the only analytic input here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalCompactRestrictionPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
  [LocallyCompactSpace (GroupScheme.rationalPoints G)]

local instance rationalCompactRestrictionKernelLocallyCompact :
    LocallyCompactSpace (Plancherel.rationalCommonNormKernel G) :=
  (Plancherel.isOpen_rationalCommonNormKernel G).locallyCompactSpace

variable (hstrata :
  ∀ K : OpenSubgroup (Plancherel.rationalCommonNormKernel G),
    IsCompact (K : Set (Plancherel.rationalCommonNormKernel G)) →
      (CompactCoefficientClass.fixedStratum.{uF, uV} K.toSubgroup).Finite)

/-- The natural ambient compact projector for the actual norm kernel.
Only fixed-level finiteness is supplied; intrinsic complements are proved. -/
def rationalNormKernelCompactProjector
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    A.representation.IntertwiningMap A.representation :=
  CompactCoefficientClass.normalSubgroupProjector
    (Plancherel.rationalCommonNormKernel G)
    (fun c D => openSubgroup_isCompl_isotypic_annihilator
      (Plancherel.rationalCommonNormKernel G)
      (Plancherel.isOpen_rationalCommonNormKernel G) c D)
    hstrata A

theorem rationalNormKernelCompactProjector_idempotent
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (v : A) :
    rationalNormKernelCompactProjector G hstrata A
        (rationalNormKernelCompactProjector G hstrata A v) =
      rationalNormKernelCompactProjector G hstrata A v :=
  CompactCoefficientClass.normalSubgroupProjector_idempotent
    (Plancherel.rationalCommonNormKernel G) _ hstrata A v

/-- The range restricts to the actual total intrinsic compact isotypic part. -/
theorem rationalNormKernelCompactProjector_range
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    SmoothRep.restrictSubrepresentation (Plancherel.rationalCommonNormKernel G)
      (rationalNormKernelCompactProjector G hstrata A).range =
      CompactCoefficientClass.totalIsotypicSubrepresentation.{uF, uV}
        (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A) :=
  CompactCoefficientClass.normalSubgroupProjector_range
    (Plancherel.rationalCommonNormKernel G) _ hstrata A

/-- Naturality holds for every actual ambient intertwiner. -/
theorem rationalNormKernelCompactProjector_natural
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (f : A.representation.IntertwiningMap B.representation) (v : A) :
    rationalNormKernelCompactProjector G hstrata B (f v) =
      f (rationalNormKernelCompactProjector G hstrata A v) :=
  CompactCoefficientClass.normalSubgroupProjector_natural
    (Plancherel.rationalCommonNormKernel G) _ hstrata A B f v

include hstrata in
/-- Fixed-level finiteness gives the exact A.IX decomposition for the all/no
arbitrary-subquotient compact-restriction factors on actual rational points.
The comparison with proper-standard cuspidality is a separate obligation. -/
theorem rationalCompactRestrictionCategoryDecomposition_of_fixedStrata
    [T2Space (GroupScheme.rationalPoints G)] :
    Renard.IsCategoryDecomposition
      (SmoothRep.compactRestrictionSubquotientProperties.{uF, uV}
        (Plancherel.rationalCommonNormKernel G)) := by
  let : TotallyDisconnectedSpace F := BruhatTits.localField_totallyDisconnectedSpace F
  let : TotallyDisconnectedSpace (GroupScheme.rationalPoints G) :=
    BruhatTits.rationalPoint_totallyDisconnectedSpace F G
  let : MeasurableSpace (Plancherel.rationalCommonNormKernel G) :=
    borel (Plancherel.rationalCommonNormKernel G)
  let : BorelSpace (Plancherel.rationalCommonNormKernel G) := ⟨rfl⟩
  exact CompactCoefficientClass.categoryDecomposition_of_normalSubgroup_totalCompactness
    (Plancherel.rationalCommonNormKernel G)
    (fun c D => openSubgroup_isCompl_isotypic_annihilator
      (Plancherel.rationalCommonNormKernel G)
      (Plancherel.isOpen_rationalCommonNormKernel G) c D)
    hstrata (MeasureTheory.Measure.haar (G := Plancherel.rationalCommonNormKernel G))

end Langlands.CuspidalSupport
