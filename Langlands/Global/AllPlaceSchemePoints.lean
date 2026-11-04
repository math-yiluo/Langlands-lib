import Langlands.Global.AdelicGenericFiberPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs

/-! # Actual adelic scheme points and their all-place components -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [PerfectField k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

/-- The original adelic coordinate projection, with its full-field scalar action. -/
def curvePlaceAdeleProjection (v : AlgebraicCurve.Place k F) :
    CurvePlaceAdeleRing k F →ₐ[F] curvePlaceCompletion v :=
  { RestrictedProduct.evalRingHom (fun v : AlgebraicCurve.Place k F =>
      curvePlaceCompletion v) v with commutes' := fun _ => rfl }

@[simp]
theorem curvePlaceAdeleProjection_apply (v : AlgebraicCurve.Place k F)
    (a : CurvePlaceAdeleRing k F) : curvePlaceAdeleProjection k F v a = a v := rfl

variable (Y : Over (Spec (CommRingCat.of F)))

/-- The full product of actual local scheme points over the original function field. -/
abbrev CurvePlaceLocalPoints :=
  ∀ v : AlgebraicCurve.Place k F, RingPoint F Y (curvePlaceCompletion v)

/-- Each factor has its independently constructed affine-chart point topology. -/
@[instance_reducible]
def curvePlaceLocalPointTopology : TopologicalSpace (CurvePlaceLocalPoints k F Y) :=
  @Pi.topologicalSpace (AlgebraicCurve.Place k F)
    (fun v => RingPoint F Y (curvePlaceCompletion v))
    (fun v => schemePointTopology F Y (curvePlaceCompletion v))

/-- Actual coefficient restriction at every curve place. -/
def curvePlaceAdelePointMap : CurvePlaceAdelePoints k F Y → CurvePlaceLocalPoints k F Y :=
  fun p v => p.changeRing (curvePlaceAdeleProjection k F v)

@[simp]
theorem curvePlaceAdelePointMap_left (p : CurvePlaceAdelePoints k F Y)
    (v : AlgebraicCurve.Place k F) :
    (curvePlaceAdelePointMap k F Y p v).left =
      Spec.map (CommRingCat.ofHom (curvePlaceAdeleProjection k F v).toRingHom) ≫ p.left := rfl

/-- Continuity here uses the chart topology on the adele-valued point carrier. -/
theorem continuous_curvePlaceAdelePointMap_charts :
    Continuous[schemePointTopology F Y (CurvePlaceAdeleRing k F),
      curvePlaceLocalPointTopology k F Y] (curvePlaceAdelePointMap k F Y) := by
  let (v : AlgebraicCurve.Place k F) :
      TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let := schemePointTopology F Y (CurvePlaceAdeleRing k F)
  let := curvePlaceLocalPointTopology k F Y
  apply continuous_pi
  intro v
  exact schemeCoefficientContinuity_proof F (CurvePlaceAdeleRing k F)
    (curvePlaceCompletion v) Y (curvePlaceAdeleProjection k F v)
      (RestrictedProduct.continuous_eval v)

variable {Y}

/-- Local postcomposition by an actual scheme morphism. -/
def curvePlaceLocalPointMap {Z : Over (Spec (CommRingCat.of F))} (f : Y ⟶ Z) :
    CurvePlaceLocalPoints k F Y → CurvePlaceLocalPoints k F Z :=
  fun p v => p v ≫ f

/-- Taking components commutes with the original scheme morphism. -/
theorem curvePlaceAdelePointMap_natural {Z : Over (Spec (CommRingCat.of F))}
    (f : Y ⟶ Z) (p : CurvePlaceAdelePoints k F Y) :
    curvePlaceAdelePointMap k F Z (p ≫ f) =
      curvePlaceLocalPointMap k F f (curvePlaceAdelePointMap k F Y p) := by
  funext v
  exact (Category.assoc _ _ _).symm

omit [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] in
/-- The independent local product topology is functorial in the scheme. -/
theorem continuous_curvePlaceLocalPointMap {Z : Over (Spec (CommRingCat.of F))}
    (f : Y ⟶ Z) :
    Continuous[curvePlaceLocalPointTopology k F Y, curvePlaceLocalPointTopology k F Z]
      (curvePlaceLocalPointMap k F f) := by
  let (v : AlgebraicCurve.Place k F) :
      TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let (v : AlgebraicCurve.Place k F) :
      TopologicalSpace (RingPoint F Z (curvePlaceCompletion v)) :=
    schemePointTopology F Z (curvePlaceCompletion v)
  let := curvePlaceLocalPointTopology k F Y
  let := curvePlaceLocalPointTopology k F Z
  apply continuous_pi
  intro v
  exact (schemePointContinuity_proof F (curvePlaceCompletion v) Y Z f).comp
    (continuous_apply v)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Projection to an archimedean completion as a morphism of K-algebras. -/
def numberFieldInfiniteAdeleProjection (v : InfinitePlace K) :
    Adeles K →ₐ[K] InfiniteCompletion K v :=
  { infiniteProjection K v with commutes' := fun _ => rfl }

/-- Projection to a finite completion as a morphism of K-algebras. -/
def numberFieldFiniteAdeleProjection (v : FinitePlace K) :
    Adeles K →ₐ[K] FiniteCompletion K v :=
  { finiteProjection K v with commutes' := fun _ => rfl }

variable (Y : Over (Spec (CommRingCat.of K)))

/-- All infinite factors and all finite factors, with no integrality restriction. -/
abbrev NumberFieldLocalPoints :=
  (∀ v : InfinitePlace K, RingPoint K Y (InfiniteCompletion K v)) ×
    (∀ v : FinitePlace K, RingPoint K Y (FiniteCompletion K v))

/-- The product of the independently constructed actual local scheme point topologies. -/
@[instance_reducible]
def numberFieldLocalPointTopology : TopologicalSpace (NumberFieldLocalPoints K Y) :=
  @instTopologicalSpaceProd _ _
    (@Pi.topologicalSpace (InfinitePlace K)
      (fun v => RingPoint K Y (InfiniteCompletion K v))
      (fun v => schemePointTopology K Y (InfiniteCompletion K v)))
    (@Pi.topologicalSpace (FinitePlace K)
      (fun v => RingPoint K Y (FiniteCompletion K v))
      (fun v => schemePointTopology K Y (FiniteCompletion K v)))

/-- The actual projection of adelic scheme points to all local scheme points. -/
def numberFieldAdelePointMap : NumberFieldAdelePoints K Y → NumberFieldLocalPoints K Y :=
  fun p => (fun v => p.changeRing (numberFieldInfiniteAdeleProjection K v),
    fun v => p.changeRing (numberFieldFiniteAdeleProjection K v))

@[simp]
theorem numberFieldAdelePointMap_infinite_left (p : NumberFieldAdelePoints K Y)
    (v : InfinitePlace K) :
    ((numberFieldAdelePointMap K Y p).1 v).left =
      Spec.map (CommRingCat.ofHom (infiniteProjection K v)) ≫ p.left := rfl

@[simp]
theorem numberFieldAdelePointMap_finite_left (p : NumberFieldAdelePoints K Y)
    (v : FinitePlace K) :
    ((numberFieldAdelePointMap K Y p).2 v).left =
      Spec.map (CommRingCat.ofHom (finiteProjection K v)) ≫ p.left := rfl

/-- This continuity statement uses the chart topology on the adelic carrier. -/
theorem continuous_numberFieldAdelePointMap_charts :
    Continuous[schemePointTopology K Y (Adeles K), numberFieldLocalPointTopology K Y]
      (numberFieldAdelePointMap K Y) := by
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let := schemePointTopology K Y (Adeles K)
  let := numberFieldLocalPointTopology K Y
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact schemeCoefficientContinuity_proof K (Adeles K) (InfiniteCompletion K v)
      Y (numberFieldInfiniteAdeleProjection K v) (continuous_infiniteProjection K v)
  · apply continuous_pi
    intro v
    exact schemeCoefficientContinuity_proof K (Adeles K) (FiniteCompletion K v)
      Y (numberFieldFiniteAdeleProjection K v) (continuous_finiteProjection K v)

variable {Y}

/-- Actual local postcomposition at all number-field places. -/
def numberFieldLocalPointMap {Z : Over (Spec (CommRingCat.of K))} (f : Y ⟶ Z) :
    NumberFieldLocalPoints K Y → NumberFieldLocalPoints K Z :=
  fun p => (fun v => p.1 v ≫ f, fun v => p.2 v ≫ f)

/-- The all-place map is natural for actual scheme morphisms. -/
theorem numberFieldAdelePointMap_natural {Z : Over (Spec (CommRingCat.of K))}
    (f : Y ⟶ Z) (p : NumberFieldAdelePoints K Y) :
    numberFieldAdelePointMap K Z (p ≫ f) =
      numberFieldLocalPointMap K f (numberFieldAdelePointMap K Y p) := by
  apply Prod.ext <;> funext v <;> exact (Category.assoc _ _ _).symm

/-- Local postcomposition is continuous for the independent product topologies. -/
theorem continuous_numberFieldLocalPointMap {Z : Over (Spec (CommRingCat.of K))}
    (f : Y ⟶ Z) :
    Continuous[numberFieldLocalPointTopology K Y, numberFieldLocalPointTopology K Z]
      (numberFieldLocalPointMap K f) := by
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Z (InfiniteCompletion K v)) :=
    schemePointTopology K Z (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Z (FiniteCompletion K v)) :=
    schemePointTopology K Z (FiniteCompletion K v)
  let (v : InfinitePlace K) : TopologicalSpace (ringTest K (InfiniteCompletion K v) ⟶ Z) :=
    schemePointTopology K Z (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (ringTest K (FiniteCompletion K v) ⟶ Z) :=
    schemePointTopology K Z (FiniteCompletion K v)
  let := numberFieldLocalPointTopology K Y
  let := numberFieldLocalPointTopology K Z
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact (schemePointContinuity_proof K (InfiniteCompletion K v) Y Z f).comp
      ((continuous_apply v).comp continuous_fst)
  · apply continuous_pi
    intro v
    exact (schemePointContinuity_proof K (FiniteCompletion K v) Y Z f).comp
      ((continuous_apply v).comp continuous_snd)

end NumberField

end Langlands.Global
