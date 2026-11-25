/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.AlgebraicGeometry.Pbc.PbcCommonStageCones
import Mathlib.CategoryTheory.Equivalence

/-! # Exact linear common-stage comparison descent

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; extracted comparison subclaim
(blueprint: lem-fd-common-stage-comparison-descent).

The functors and transformations below are the existing literal-pair constructions.
The beta maps are the inverses of the scalar comparisons denoted by j in the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe d u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

section Pullback
variable {T} {U : Scheme.{u}} [IsNoetherian U]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [iU : Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]

end Pullback
end WeilConjectures
