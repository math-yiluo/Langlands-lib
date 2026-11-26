import Langlands.Automorphic.GroupSchemeInvariantForms

/-! # Uniformly moderate growth of automorphic functions on `Γ \ G(𝔸)`

Mœglin–Waldspurger I.2.17 (printed pp. 38–39): for every parabolic `P = MU` and every automorphic
form `φ` on `U(𝔸)M(k) \ G`, "`φ` and its derivatives have moderate growth", in the uniform sense
of I.2.3 (printed p. 25): one exponent `r` serves every element of the enveloping algebra.

This file defines that uniform condition for plain complex functions on the actual adelic points,
through the enveloping action on their plot-smooth infinite slices, and states that it holds for
every function satisfying `IsAutomorphicFunctionOn` for an arbitrary left subgroup `Γ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- Uniformly moderate growth of a function on the actual adelic points (Mœglin–Waldspurger
I.2.3): there is one real exponent `r` such that for every element `a` of the complex enveloping
algebra some `C > 0` bounds the derivative `a` of every plot-smooth infinite slice by
`C ‖g‖ ^ r`, where `g = (x, b)` is the adelic point and `‖·‖` the adelic norm of `rho`. Slices that
are not plot-smooth impose no condition. -/
def HasUniformModerateGrowthFunction (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ r : ℝ, ∀ a : AdelicEnvelopingAlgebra F G hsmooth, ∃ C : ℝ, 0 < C ∧
    ∀ (b : FiniteAdelicGroupPoints F G)
      (h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G)
      (x : InfiniteAdelicGroupPoints F G),
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a
          ⟨functionInfiniteSlice F G φ b, h⟩ : InfiniteAdelicGroupPoints F G → ℂ) x‖ ≤
        C * RepresentationGrowth.adelicSourceNorm F G rho (AdelicGroupPoints.pair F G x b) ^ r

/-- Automorphic functions on `Γ \ G(𝔸)` have uniformly moderate growth (Mœglin–Waldspurger
I.2.17, printed pp. 38–39, with I.2.5, Lemma (a)). Let `G` be a connected reductive group over a
number field, `Kinf` a maximal compact subgroup of the infinite adelic points, `rho` a closed
matrix representation of positive size and `Γ` any subgroup of `G(𝔸)`. Every function that is
automorphic on `Γ \ G(𝔸)` in the sense of `IsAutomorphicFunctionOn` (left `Γ`-invariant, smooth,
`Kinf`-finite, finite under the centre of the enveloping algebra and of moderate growth for
`rho`) has uniformly moderate growth for `rho`. -/
def AutomorphicFunctionUniformGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (Γ : Subgroup (AdelicGroupPoints F G))
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N d : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    GroupScheme.IsConnectedReductive G → GroupScheme.IsClosedSubgroup rho →
    CompactIwasawa.IsMaximalCompact Kinf → 0 < N →
    ∀ φ : AdelicGroupPoints F G → ℂ,
      IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ →
        HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ

end Langlands.Automorphic.GroupSchemeFunctions
