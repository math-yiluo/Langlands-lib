import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.RingTheory.Henselian

/-!
# Integral points over a henselian valuation ring

Conrad's Corollary 5.7, with its scope corrected. Let `O` be the valuation ring of a
nontrivially normed non-archimedean field `K` and assume `O` is henselian. For an algebraic
space `X` over `Spec O`, the natural map `X(O) → X_K(K)` to the rational points of the
generic fibre has open image when `X` is quasi-separated and locally of finite type; it is
injective when `X` is separated, with closed image when `X` is moreover of finite type; and
its image is quasi-compact when `K` is locally compact and `X` is quasi-separated of finite
type. Closedness fails in the source's generality: there are quasi-separated finite type
spaces and separated locally finite type spaces whose image is not closed.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Corollary 5.7 (printed p.16), openness: let `K` be a nontrivially normed field
whose closed unit ball is a subring `O`, and assume `O` is henselian. For every
quasi-separated algebraic space `X` locally of finite type over `Spec O`, the image of the
map `X(O) → X_K(K)`, viewing an `O`-point as a `K`-point and then as a rational point of the
base change to `Spec K`, is open for the étale-chart topology. -/
def HenselianIntegralPointsOpenStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsQuasiSeparated X →
      LocallyOfFiniteTypeOverBase X →
      IsOpen[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)]
        (Set.range fun x : RingPoints O X O =>
          (baseChangeRingPointsEquiv O K K X).symm
            (RingPoints.changeRing (Algebra.ofId O K) x))

/-- Conrad's Corollary 5.7 (printed p.16), closedness with corrected scope: in the setting
of `HenselianIntegralPointsOpenStatement`, the map `X(O) → X_K(K)` is injective when `X` is
separated, and its image is closed for the étale-chart topology when `X` is moreover of
finite type over `Spec O`. -/
def HenselianIntegralPointsClosedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsSeparated X →
      let ι : RingPoints O X O → RingPoints K (baseChange (Spec.algebraMap O K) X) K :=
        fun x => (baseChangeRingPointsEquiv O K K X).symm
          (RingPoints.changeRing (Algebra.ofId O K) x)
      Function.Injective ι ∧
        (FiniteTypeOverRing O X →
          IsClosed[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)] (Set.range ι))

/-- Conrad's Corollary 5.7 (printed p.16), quasi-compactness: in the setting of
`HenselianIntegralPointsOpenStatement`, if `K` is locally compact and `X` is a
quasi-separated algebraic space of finite type over `Spec O`, the image of
`X(O) → X_K(K)` is quasi-compact for the étale-chart topology. -/
def HenselianIntegralPointsCompactStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O → LocallyCompactSpace K →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsQuasiSeparated X →
      FiniteTypeOverRing O X →
      @IsCompact _ (etaleChartTopology K (baseChange (Spec.algebraMap O K) X))
        (Set.range fun x : RingPoints O X O =>
          (baseChangeRingPointsEquiv O K K X).symm
            (RingPoints.changeRing (Algebra.ofId O K) x))

/-- The closedness assertion of Conrad's Corollary 5.7 fails without separatedness: in the
setting of `HenselianIntegralPointsOpenStatement`, there is a quasi-separated algebraic space
of finite type over `Spec O` for which the image of `X(O) → X_K(K)` is not closed. -/
def HenselianIntegralPointsNotClosedOfFiniteTypeStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O →
    ∃ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsQuasiSeparated X ∧
      FiniteTypeOverRing O X ∧
      ¬ IsClosed[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)]
        (Set.range fun x : RingPoints O X O =>
          (baseChangeRingPointsEquiv O K K X).symm
            (RingPoints.changeRing (Algebra.ofId O K) x))

/-- The closedness assertion of Conrad's Corollary 5.7 fails without quasi-compactness: in
the setting of `HenselianIntegralPointsOpenStatement`, there is a separated algebraic space
locally of finite type over `Spec O` for which the image of `X(O) → X_K(K)` is not
closed. -/
def HenselianIntegralPointsNotClosedOfSeparatedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O →
    ∃ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsSeparated X ∧
      LocallyOfFiniteTypeOverBase X ∧
      ¬ IsClosed[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)]
        (Set.range fun x : RingPoints O X O =>
          (baseChangeRingPointsEquiv O K K X).symm
            (RingPoints.changeRing (Algebra.ofId O K) x))

end Langlands.AlgebraicGeometry.AlgebraicSpace
