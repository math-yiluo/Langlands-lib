/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QbarCompactSupportExchangeModel
import all WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import all WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport

/-! # The open factor of the completed coefficient square

Source: the coefficient-coherence proof, open tensor and completion-unit steps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Completed open exchange respects the canonical open scalar mates and every
unit-normalized completed pullback comparison.

Source: current blueprint, coefficient coherence proof steps 6--8.
(blueprint: lem-cbc-open-coefficient-square).

Proof: first transpose the ordinary square under the open adjunction. Both
transposes are the same balancing map on extension summands: an indexed section
x tensor s goes to its pulled-back indexed section with coefficient s. Exact
extension by zero and K-flat scalar representatives descend this equality to the
derived categories. Precompose the completed square with the ordinary-to-completed
unit at the larger coefficient field. Use the unit equations of both supplied
comparisons and the defining unit equations of both completed open exchanges.
Naturality of the open scalar mate changes the resulting equation into the
ordinary square followed by the target completion unit. The target is complete:
completed pullback preserves completeness, extension by zero preserves it on a
quasicompact open, and finite free scalar extension preserves it. The source is
the reflection of ordinary pullback with the same unit, so its Hom bijection
cancels the precomposition. This argument is independent of the generating tuple
and applies also to zero inputs, repeated coefficient fields and empty schemes. -/
theorem cbcOpenCoefficientSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {U U' Z Z' : Scheme.{u}} {j : U ⟶ Z} {j' : U' ⟶ Z'}
    {g : Z' ⟶ Z} {gu : U' ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare gu j' j g) [QuasiCompact j]
    (P : CbcCompletedScalarComparison l Ω g)
    (P' : CbcCompletedScalarComparison l Ω gu)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (s : ℕ) (b : Fin s → PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
    (hb : Ideal.span (Set.range b) = (pbcStageDatum.{u} l Ω F).ideal)
    (K : pbcAmbientStage l Ω U E)
    (hK : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) U r a ha K)
    (hCK : cbcCompleteProperty (pbcStageDatum.{u} l Ω F) U s b hb
      ((pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) U).obj K)) :
    (cbcDatumCompletedExchange (pbcStageDatum.{u} l Ω F) sq s b hb).app ⟨_, hCK⟩ ≫
        (cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω F) j' sq.isOpenImmersion').map
          ((P'.map h).app K) ≫
        (cbcScalarOpenInverse l _ _ (pbcFiniteFieldInclusion l Ω h)
          j').app
          (((pbcStageDatum.{u} l Ω E).completedPull gu).obj K) =
      ((pbcStageDatum.{u} l Ω F).completedPull g).map
          ((cbcScalarOpenInverse l _ _ (pbcFiniteFieldInclusion l Ω h)
            j).app K) ≫
        (P.map h).app ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) j
          sq.isOpenImmersion).obj K) ≫
        (pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Z').map
          ((cbcDatumCompletedExchange (pbcStageDatum.{u} l Ω E) sq r a ha).app
            ⟨K, hK⟩) := by sorry

end AlgebraicGeometry.Scheme
