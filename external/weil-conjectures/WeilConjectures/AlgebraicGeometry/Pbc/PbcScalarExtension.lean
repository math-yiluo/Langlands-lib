/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTriangulation
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationIdentity
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationShift

/-! # Finite scalar extension on the actual proper-base-change categories

Coefficient maps are specified on all finite reductions. Integral extension is the
existing universal derived tensor functor. Rational extension is its balanced map
on the actual localized Hom modules, without adjoining retracts.

## References

* Milne, Lectures on Etale Cohomology, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

variable {Z : Scheme.{u}} (h : Z ⟶ X)

section
attribute [local irreducible] pbcActualCompletedPull pbcActualCompletion
  reductionDerivedChange completedAdicDerivedChange

end

end AmbientOperations
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

attribute [local irreducible] pbcStageTransition

end AlgebraicGeometry.Scheme
