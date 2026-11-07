import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Analytic manifold structures on rational points of smooth algebraic spaces

Vocabulary for the analytic-manifold assertion in Conrad's Proposition 5.4 (printed p.15): for a
complete field `K` and a smooth algebraic space `X`, the rational points `X(K)` carry a unique
functorial `K`-analytic manifold structure that agrees with the scheme case and carries étale
maps to analytic local isomorphisms.

Mathlib's manifolds have one model space, so the structure is a family indexed by the relative
dimension `n`: on the rational points of every space in `IsSmoothPureDimensional K n`, a charted
space over `Fin n → K` for the étale-chart topology. This module defines that data and the
conditions of the assertion; the assertion itself is
`AnalyticPointManifoldStatement`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped ContDiff Manifold
open Langlands.AlgebraicGeometry.PointTopology (ringTest affineRingPointEquiv)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K : Type u) [NontriviallyNormedField K]

/-- The spaces of the analytic-manifold assertion in a fixed relative dimension `n`: quasi-separated,
locally separated and locally of finite type over `Spec K` (the class of the corrected
Proposition 5.4), with a surjective étale atlas that is smooth of relative dimension `n` over
`Spec K`. -/
def IsSmoothPureDimensional (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K))) : Prop :=
  IsLocallySeparatedLocallyFiniteType K X ∧
    HasAtlasProperty (@SmoothOfRelativeDimension.{u} n) X

/-- Affine `n`-space over `Spec K`, as an actual scheme: the spectrum of the polynomial ring in
`n` variables. -/
abbrev affineSpaceOver (n : ℕ) : Over (Spec (CommRingCat.of K)) :=
  ringTest K (MvPolynomial (Fin n) K)

/-- The coordinates of a rational point of affine `n`-space: the values of the `n` variables
under the corresponding `K`-algebra map. -/
def affineSpaceCoordinates (n : ℕ) :
    RingPoints K ((schemeToSpace _).obj (affineSpaceOver K n)) K → (Fin n → K) :=
  fun x i => affineRingPointEquiv K (MvPolynomial (Fin n) K) K
    (schemeRingPointsEquiv K (affineSpaceOver K n) K x) (MvPolynomial.X i)

/-- A family of charted-space structures modelled on `Fin n → K` on the rational points of every
space of `IsSmoothPureDimensional K n`, each for the étale-chart topology. -/
structure AnalyticPointStructure where
  /-- The charts on `X(K)` for a space of relative dimension `n`. -/
  chartedSpace : ∀ (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K))),
    IsSmoothPureDimensional K n X →
      @ChartedSpace (Fin n → K) _ (RingPoints K X K) (etaleChartTopology K X)

namespace AnalyticPointStructure

variable {K}

/-- Every structure of the family is an analytic manifold structure. -/
def IsAnalytic (σ : AnalyticPointStructure K) : Prop :=
  ∀ (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : IsSmoothPureDimensional K n X),
    @IsManifold K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) ω (RingPoints K X K)
      (etaleChartTopology K X) (σ.chartedSpace n X hX)

/-- Functoriality: every morphism of spaces in the family induces an analytic map on rational
points. -/
def IsFunctorial (σ : AnalyticPointStructure K) : Prop :=
  ∀ (n m : ℕ) (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) (hY : IsSmoothPureDimensional K m Y) (f : X ⟶ Y),
    @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) (RingPoints K X K)
      (etaleChartTopology K X) (σ.chartedSpace n X hX) (Fin m → K) _ _ (Fin m → K) _
      𝓘(K, Fin m → K) (RingPoints K Y K) (etaleChartTopology K Y) (σ.chartedSpace m Y hY) ω
      (RingPoints.map (A := K) f)

/-- Étale morphisms induce analytic local isomorphisms on rational points. -/
def IsEtaleLocalIso (σ : AnalyticPointStructure K) : Prop :=
  ∀ (n : ℕ) (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) (hY : IsSmoothPureDimensional K n Y) (f : X ⟶ Y),
    IsEtaleMorphism f →
      letI := etaleChartTopology K X
      letI := etaleChartTopology K Y
      letI := σ.chartedSpace n X hX
      letI := σ.chartedSpace n Y hY
      IsLocalDiffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω (RingPoints.map (A := K) f)

/-- Agreement with the scheme case, in the form that pins it down: on affine `n`-space the
coordinate map `Aⁿ(K) → Kⁿ` is an analytic diffeomorphism. -/
def AgreesWithAffineSpace (σ : AnalyticPointStructure K) : Prop :=
  ∀ (n : ℕ) (h : IsSmoothPureDimensional K n ((schemeToSpace _).obj (affineSpaceOver K n))),
    letI := etaleChartTopology K ((schemeToSpace _).obj (affineSpaceOver K n))
    letI := σ.chartedSpace n _ h
    ∃ Φ : Diffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
        (RingPoints K ((schemeToSpace _).obj (affineSpaceOver K n)) K) (Fin n → K) ω,
      ∀ x, Φ x = affineSpaceCoordinates K n x

/-- The conditions of Conrad's analytic-manifold assertion. -/
def IsAdmissible (σ : AnalyticPointStructure K) : Prop :=
  σ.IsAnalytic ∧ σ.IsFunctorial ∧ σ.IsEtaleLocalIso ∧ σ.AgreesWithAffineSpace

/-- Two families agree when, on every space, the identity of `X(K)` is analytic in both
directions between the two structures. -/
def Equivalent (σ τ : AnalyticPointStructure K) : Prop :=
  ∀ (n : ℕ) (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : IsSmoothPureDimensional K n X),
    @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) (RingPoints K X K)
        (etaleChartTopology K X) (σ.chartedSpace n X hX) (Fin n → K) _ _ (Fin n → K) _
        𝓘(K, Fin n → K) (RingPoints K X K) (etaleChartTopology K X) (τ.chartedSpace n X hX) ω
        id ∧
      @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) (RingPoints K X K)
        (etaleChartTopology K X) (τ.chartedSpace n X hX) (Fin n → K) _ _ (Fin n → K) _
        𝓘(K, Fin n → K) (RingPoints K X K) (etaleChartTopology K X) (σ.chartedSpace n X hX) ω
        id

end AnalyticPointStructure

end Langlands.AlgebraicGeometry.AlgebraicSpace
