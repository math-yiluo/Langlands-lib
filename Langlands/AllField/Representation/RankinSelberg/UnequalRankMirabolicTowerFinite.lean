import Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite
import Langlands.AllField.Representation.Parabolic.JacquetCenterSpanProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# Spectral finiteness of tower data

Let `(ρ, q)` be a tower datum at level `i + 1` for a representation `η` of
`GL_(N+1)`. The upper unipotent radical of the block shape `(i + 1, N - i)` acts on
`q`-images through embedded radical elements of `P_(i+1)`. Hence `q` descends to a
map from the unnormalized Jacquet module of `η` for this shape to the quotient of
the carrier of `ρ` by its radical span. The block scalar `diag(a I_(i+1), I_(N-i))`
is the embedded element `leviScalar a`. If the block-scalar action on the Jacquet
module has finite-dimensional span, then `ρ (leviScalar a)` satisfies a nonzero
polynomial modulo the radical span.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.UnequalRankTower
open Langlands.RankinSelberg.UnequalRankTower
open Langlands.AllField.RankinSelberg.UnequalRankTower
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Polynomial
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker

universe uF uW uA

section Polynomial

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {M' : Type*} [AddCommGroup M'] [Module ℂ M']

end Polynomial

section Shape

variable {F : Type uF} [Field F]

end Shape

section Tower

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

end Tower

section Padic

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]

/-- For an admissible irreducible `η`, the operator `ρ (leviScalar a)` of a tower datum
at a positive level is annihilated modulo the radical span by a nonzero polynomial. -/
theorem IsTower.exists_polynomial {F : Type uF} [Field F]
    (T : LocalFieldData F) :
    letI := T.topology
    ∀ {ψ : UnitaryAdditiveCharacter F} {N i : ℕ}
      {η : Representation ℂ (Langlands.GeneralLinear (N + 1) F) W} (h : i + 1 ≤ N)
      {ρ : Representation ℂ (mirabolic (i + 1) F) A} {q : W →ₗ[ℂ] A},
      IsTower ψ η h ρ q → IsAdmissible η → η.IsIrreducible → ∀ a : Fˣ,
        ∃ P : ℂ[X], P ≠ 0 ∧ ∀ y : A,
          aeval (ρ (MirabolicRigidity.leviScalar a)) P y ∈
            (MirabolicRigidity.radicalSpan ρ).toSubmodule := by
  let := T.topology
  intro ψ N i η h ρ q hT hadm hirr a
  exact hT.exists_polynomial_of_finiteDimensional h
    (Langlands.AllField.Parabolic.jacquetCenterSpan.{uF, uW} F T (N + 1) (towerShape h) W η hadm
      (moduleFinite_asModule_of_isIrreducible η hirr)) a

end Padic

end Langlands.AllField.RankinSelberg.UnequalRankTower
