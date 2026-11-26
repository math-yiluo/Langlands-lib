import Langlands.Geometry.Building.TorusFiltration.Points
import Langlands.Geometry.Building.KPWeaklyInducedTorus

/-! # Structural statements for the minimal congruent torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- KP Lemma B.10.9 for tori over the maximal unramified field. The shallow
subgroup has an actual smooth model with geometrically connected fibres. -/
def MinimalCongruentShallowModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) (q : Set.Iio (1 : ℝ≥0)),
    0 < (q : ℝ≥0) →
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        M.integralPoints = minimalCongruentShallowSubgroup F T hT q

/-- Functoriality for every morphism of tori, as in KP Proposition B.10.10. -/
def MinimalCongruentFunctorialityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T U : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] [IsAffine U.X.left] (hT : IsTorus T.toGrp) (hU : IsTorus U.toGrp)
    (f : T ⟶ U) (r : ℝ≥0),
    (minimalCongruentPoints F T hT r).map (rationalPoints.map (CommGroupScheme.groupHom f)) ≤
      minimalCongruentPoints F U hU r

/-- The filtration is decreasing and separated, and its jump depths are
discrete as in KP Definitions B.5.2 and B.10.2. -/
def MinimalCongruentOrderStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp),
    Antitone (minimalCongruentPoints F T hT) ∧
      (⨅ r : ℝ≥0, minimalCongruentPoints F T hT r) = ⊥ ∧
      _root_.IsDiscrete { r : ℝ≥0 | minimalCongruentPlus F T hT r ≠
        (minimalCongruentPoints F T hT r : Set (rationalPoints T.toGrp)) }

/-- Schematicity and connectedness at every depth in KP Proposition B.10.10. -/
def MinimalCongruentConnectedModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) (r : ℝ≥0),
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        M.integralPoints = minimalCongruentPoints F T hT r

/-- The congruence equality of KP Definition B.5.3 and Proposition B.10.10. -/
def MinimalCongruentCongruenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp),
    M.IsSmooth → M.integralPoints = minimalCongruentPoints F T hT r →
      M.congruenceSubgroup = minimalCongruentPoints F T hT (r + 1)

/-- The comparison for weakly induced tori in KP Corollary B.10.13. -/
def MinimalCongruentWeaklyInducedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp),
    IsWeaklyInducedTorus F T →
      ∀ r : ℝ≥0, minimalCongruentPoints F T hT r = localTorusFiltration F T hT r

/-- The order, integral models, congruence property and weakly induced
comparison of the actual point family. -/
def MinimalCongruentStructuralStatements : Prop :=
  MinimalCongruentShallowModelStatement.{u} ∧
  MinimalCongruentFunctorialityStatement.{u} ∧
  MinimalCongruentOrderStatement.{u} ∧
  MinimalCongruentConnectedModelStatement.{u} ∧
  MinimalCongruentCongruenceStatement.{u} ∧
  MinimalCongruentWeaklyInducedStatement.{u}

end Langlands.Geometry.Building
