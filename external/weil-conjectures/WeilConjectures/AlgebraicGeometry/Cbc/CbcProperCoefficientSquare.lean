/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportExchangeModel
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap

/-! # The proper factor of the completed coefficient square

Source: the coefficient-coherence proof, proper mate and completion-unit steps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The proper exchange commutes with the unit-normalized scalar comparisons.
The comparison at the upper horizontal map is constructed at the same time; its
unit fixes it uniquely. No constructibility condition on the proper source is used.

Source: current blueprint, coefficient coherence proof steps 5, 9 and 10.
(blueprint: lem-cbc-proper-coefficient-square).

Proof: finite free tensor commutes with the principal Koszul completion reflector.
The equality of the two radical ideals under ramification identifies the target
reflectors by their units. Transport this unit-preserving comparison to the strict
completed pullback; this constructs Q. Transpose the ordinary coefficient/exchange
square under the larger-ring pullback/direct-image adjunction. The proper scalar
comparison transposes to coefficient extension of the counit, and ordinary exchange
transposes to pullback of the same counit. Tensor balancing and Cartesian pasting
identify these transposes. The strict tower exchange extends this ordinary mate:
its reconstruction maps preserve the quotient units and the direct-image/limit
comparison preserves their cones. Precompose the completed square by the larger
completion unit. The unit equations for P and Q reduce it to the ordinary square.
The target is complete because direct image preserves completeness and finite free
tensor preserves completeness. The reflector Hom bijection cancels that unit.
The same construction is natural in the input and in coefficient inclusions,
including repeated fields, zero objects and empty schemes. -/
theorem cbcProperCoefficientSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {Z Z' Y Y' : Scheme.{u}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'}
    {g : Y' ⟶ Y} {gb : Z' ⟶ Z} [IsProper p]
    (sq : ChosenCartesianSquare gb p' p g)
    (P : CbcCompletedScalarComparison l Ω g) :
    ∃ Q : CbcCompletedScalarComparison l Ω gb,
      ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
        (M : pbcAmbientStage l Ω Z E),
        (pbcStageDatum.{u} l Ω E).TowerComplete Z M →
        (pbcStageDatum.{u} l Ω F).completedExchange sq
            ((pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Z).obj M) ≫
          ((pbcStageDatum.{u} l Ω F).push p').map ((Q.map h).app M) ≫
          (pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) p').inv.app
            (((pbcStageDatum.{u} l Ω E).completedPull gb).obj M) =
        ((pbcStageDatum.{u} l Ω F).completedPull g).map
            ((pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) p).inv.app M) ≫
          (P.map h).app (((pbcStageDatum.{u} l Ω E).push p).obj M) ≫
          (pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Y').map
            ((pbcStageDatum.{u} l Ω E).completedExchange sq M) := by sorry

end AlgebraicGeometry.Scheme
