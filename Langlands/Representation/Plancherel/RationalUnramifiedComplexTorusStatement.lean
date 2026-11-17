import Langlands.Representation.Plancherel.RationalUnramifiedComplexChart
import Langlands.Representation.Plancherel.RationalImageComplexExponential
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! # The complex torus `X(G)` and its real subtorus `Im X(G)` (Renard V.3.20): statements

Four component statements and their conjunction `RationalUnramifiedComplexTorusStatement`. Each
component quantifies over a nonarchimedean local field `F`, a connected reductive group scheme
`G` over `F` (with the canonical topology on `G(F)`) and an integer basis `b` of the valuation
image `Λ(G)`, and gives `X(G)` the one-chart charted space of `b`. -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Renard V.3.20, basis independence: with the chart of a basis `b` on `X(G)`, the chart of
every other basis `b'` is a local biholomorphism `X(G) → ℂ^r`. So all bases define the same
complex-analytic structure on `X(G)`. -/
def RationalUnramifiedBasisChartIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ b : Module.Basis (Fin (rationalImageRank G)) ℤ
        (Additive (rationalDiscreteValuationImage G)),
      letI := rationalUnramifiedBasisChartedSpace G b
      ∀ b' : Module.Basis (Fin (rationalImageRank G)) ℤ
          (Additive (rationalDiscreteValuationImage G)),
        IsLocalDiffeomorph 𝓘(ℂ, Fin (rationalImageRank G) → ℂ)
          𝓘(ℂ, Fin (rationalImageRank G) → ℂ) ω (rationalUnramifiedBasisCoordinates G b')

/-- Renard V.3.20, "le tore complexe `X(M)`": with the chart of any basis `b`, `X(G)` is a
complex Lie group (multiplication and inversion are holomorphic). -/
def RationalUnramifiedComplexLieGroupStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ b : Module.Basis (Fin (rationalImageRank G)) ℤ
        (Additive (rationalDiscreteValuationImage G)),
      letI := rationalUnramifiedBasisChartedSpace G b
      LieGroup 𝓘(ℂ, Fin (rationalImageRank G) → ℂ) ω
        (unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))

/-- Renard V.3.20, the morphism `𝔞*_ℂ → X(M)`: in the coordinates `s ↦ b.constr ℤ s` of
`𝔞*_ℂ = Hom(Λ(G), ℂ)` and with the chart of `b` on `X(G)`, the complex exponential is a local
biholomorphism `ℂ^r → X(G)`. -/
def RationalUnramifiedComplexExponentialStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ b : Module.Basis (Fin (rationalImageRank G)) ℤ
        (Additive (rationalDiscreteValuationImage G)),
      letI := rationalUnramifiedBasisChartedSpace G b
      IsLocalDiffeomorph 𝓘(ℂ, Fin (rationalImageRank G) → ℂ)
        𝓘(ℂ, Fin (rationalImageRank G) → ℂ) ω
        (fun s : Fin (rationalImageRank G) → ℂ =>
          rationalCanonicalUnramifiedComplexExponential G
            (Multiplicative.ofAdd (b.constr ℤ s).toAddMonoidHom))

/-- Renard V.3.20, "`Im(X(M))` … est une sous-variété réelle du tore complexe `X(M)`, … un tore
compact, isomorphe à `i𝔞*/(2iπ/ln q)ℝ`": with the chart of `b` on `X(G)`, regarded as a real
manifold, `Im X(G)` carries a real Lie group structure modelled on `ℝ^r` for which the inclusion
is a smooth embedding, and the imaginary exponential `t ↦ exp(b.constr ℤ (t·i))` is a local
diffeomorphism `ℝ^r → Im X(G)`. -/
def RationalUnitaryUnramifiedSubmanifoldStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ b : Module.Basis (Fin (rationalImageRank G)) ℤ
        (Additive (rationalDiscreteValuationImage G)),
      letI := rationalUnramifiedBasisChartedSpace G b
      ∃ (_ : ChartedSpace (Fin (rationalImageRank G) → ℝ)
          (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))),
        LieGroup 𝓘(ℝ, Fin (rationalImageRank G) → ℝ) ∞
          (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (rationalImageRank G) → ℝ)
          𝓘(ℝ, Fin (rationalImageRank G) → ℂ) ∞ (rationalUnitaryUnramifiedInclusion G) ∧
        ∃ e : (Fin (rationalImageRank G) → ℝ) →
            unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul),
          (∀ t, rationalUnitaryUnramifiedInclusion G (e t) =
            rationalCanonicalUnramifiedComplexExponential G
              (Multiplicative.ofAdd (b.constr ℤ (fun i => (t i : ℂ) * Complex.I)).toAddMonoidHom)) ∧
          IsLocalDiffeomorph 𝓘(ℝ, Fin (rationalImageRank G) → ℝ)
            𝓘(ℝ, Fin (rationalImageRank G) → ℝ) ∞ e

/-- Renard V.3.20, smooth structure of `X(G)` and `Im X(G)`: the conjunction of the four
component statements (basis independence of the complex chart, complex Lie group, exponential a
local biholomorphism, `Im X(G)` an embedded real Lie subgroup covered by `i𝔞*`). -/
def RationalUnramifiedComplexTorusStatement : Prop :=
  RationalUnramifiedBasisChartIndependenceStatement.{u} ∧
    RationalUnramifiedComplexLieGroupStatement.{u} ∧
    RationalUnramifiedComplexExponentialStatement.{u} ∧
    RationalUnitaryUnramifiedSubmanifoldStatement.{u}

end Langlands.Plancherel
