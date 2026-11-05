import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The étale-chart topology on rational points of algebraic spaces

Conrad's construction in the proof of Proposition 5.4: the rational points of an algebraic
space over a field carry the strongest topology making every map `U(k) → X(k)` continuous,
for étale maps `U → X` from actual schemes of finite type over the field.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint schemePointTopology)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K : Type u) [Field K] [TopologicalSpace K]

/-- An étale chart of finite type: an étale morphism to `X` from the space of an actual
scheme of finite type (locally of finite type and quasi-compact) over `Spec K`. -/
structure EtaleFiniteTypeChart (X : AlgebraicSpace (Spec (CommRingCat.of K))) where
  /-- The actual chart scheme. -/
  scheme : Over (Spec (CommRingCat.of K))
  /-- The chart morphism to the space. -/
  hom : (schemeToSpace _).obj scheme ⟶ X
  isEtale : IsEtale (AlgebraicSpace.hom hom)
  locallyOfFiniteType : LocallyOfFiniteType scheme.hom
  quasiCompact : QuasiCompact scheme.hom

variable {K} in
/-- The map from the rational points of a chart scheme to the rational points of the
space. -/
def EtaleFiniteTypeChart.pointMap {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X) : RingPoint K c.scheme K → RingPoints K X K :=
  fun x => RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme K).symm x)

/-- The strongest topology on `X(K)` making every chart map continuous, where each chart
scheme's rational points carry the existing scheme point topology. -/
@[instance_reducible]
def etaleChartTopology (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    TopologicalSpace (RingPoints K X K) :=
  ⨆ c : EtaleFiniteTypeChart K X,
    TopologicalSpace.coinduced c.pointMap (schemePointTopology K c.scheme K)

variable {K}

/-- A set of rational points is open exactly when its preimage in every chart is open. -/
theorem etaleChartTopology_isOpen_iff (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (V : Set (RingPoints K X K)) :
    IsOpen[etaleChartTopology K X] V ↔
      ∀ c : EtaleFiniteTypeChart K X,
        IsOpen[schemePointTopology K c.scheme K] (c.pointMap ⁻¹' V) := by
  rw [etaleChartTopology, isOpen_iSup_iff]
  rfl

/-- Every chart map is continuous for the étale-chart topology. -/
theorem EtaleFiniteTypeChart.continuous_pointMap {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X) :
    Continuous[schemePointTopology K c.scheme K, etaleChartTopology K X] c.pointMap :=
  continuous_iff_coinduced_le.mpr (le_iSup (fun c : EtaleFiniteTypeChart K X =>
    TopologicalSpace.coinduced c.pointMap (schemePointTopology K c.scheme K)) c)

/-- A map out of `X(K)` is continuous exactly when its composite with every chart map is. -/
theorem etaleChartTopology_continuous_iff {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {Y : Type*} [TopologicalSpace Y] (h : RingPoints K X K → Y) :
    Continuous[etaleChartTopology K X, _] h ↔
      ∀ c : EtaleFiniteTypeChart K X,
        Continuous[schemePointTopology K c.scheme K, _] (h ∘ c.pointMap) := by
  rw [etaleChartTopology, continuous_iSup_dom]
  simp only [continuous_coinduced_dom]

end Langlands.AlgebraicGeometry.AlgebraicSpace
