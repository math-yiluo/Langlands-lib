import Langlands.Global.ArchimedeanCompact
import Langlands.Representation.Archimedean.OrthogonalGroupAveraging
import Langlands.TraceFormula.ArchimedeanUnitaryCharacterSeparationStatement

/-! # Polynomial rank bounds for compact averaging at infinity -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.TraceFormula.ArchimedeanUnitary

open Langlands.Global Langlands.Archimedean

universe uF uE

section Coordinates

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

/-- The matrix coordinates of the standard infinite compact subgroup. -/
def compactMatrix : C(standardInfiniteCompact F n, ArchimedeanMatrix F n) :=
  ⟨fun k => (archimedeanGLCoordinates F n k.val).val,
    Units.continuous_val.comp ((archimedeanGLCoordinates F n).continuous.comp
      continuous_subtype_val)⟩

/-- Evaluate a complex polynomial on real coordinates of the compact matrices. -/
def compactCoordinatePolynomial
    (p : MvPolynomial (Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) ℂ) :
    C(standardInfiniteCompact F n, ℂ) :=
  MvPolynomial.aeval (fun i =>
    let e := (Module.finBasis ℝ (ArchimedeanMatrix F n)).equivFun.toContinuousLinearEquiv
    ⟨fun k => (e (compactMatrix F n k) i : ℂ),
      Complex.continuous_ofReal.comp ((continuous_apply i).comp
        (e.continuous.comp (compactMatrix F n).continuous))⟩) p

@[simp]
theorem compactCoordinatePolynomial_apply
    (p : MvPolynomial (Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) ℂ)
    (k : standardInfiniteCompact F n) :
    compactCoordinatePolynomial F n p k =
      p.eval (fun i => ((Module.finBasis ℝ (ArchimedeanMatrix F n)).equivFun
        (compactMatrix F n k) i : ℂ)) := by
  change ContinuousMap.evalAlgHom ℂ ℂ k (compactCoordinatePolynomial F n p) = _
  rw [compactCoordinatePolynomial, MvPolynomial.comp_aeval_apply]
  rfl

/-- The usual completion topology on the archimedean group is second countable. -/
theorem infiniteGL_secondCountableTopology : SecondCountableTopology (InfiniteAdelicGL F n) := by
  let A := ArchimedeanMatrix F n
  let e := (Module.finBasis ℝ A).equivFun.toContinuousLinearEquiv
  let : SecondCountableTopology A := e.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ((Units.isEmbedding_embedProduct (M := A)).comp
    (archimedeanGLCoordinates F n).toHomeomorph.isEmbedding).secondCountableTopology

end Coordinates

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "G" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n

/-- The actual bounded operator obtained by averaging a coordinate polynomial over the
standard compact subgroup. -/
def compactPolynomialAverage [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] (π : G →* (E →L[ℂ] E))
    (hπ : IsContinuousRepresentation π)
    (p : MvPolynomial (Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) ℂ) : E →L[ℂ] E :=
  letI : SecondCountableTopology G := infiniteGL_secondCountableTopology F n
  letI : SecondCountableTopology K := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  compactAverage ν (A := fun k : K => π k.val)
    (hπ.comp (continuous_subtype_val.prodMap continuous_id))
    (compactCoordinatePolynomial F n p)

@[simp]
theorem compactPolynomialAverage_apply [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] (π : G →* (E →L[ℂ] E))
    (hπ : IsContinuousRepresentation π)
    (p : MvPolynomial (Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) ℂ) (x : E) :
    compactPolynomialAverage ν π hπ p x =
      ∫ k : K, compactCoordinatePolynomial F n p k • π k.val x ∂ν := rfl

/-- The compact polynomial averages have finite-dimensional range with a common
polynomial bound in the degree of the weight. -/
def HasCompactPolynomialRankBound [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] (π : G →* (E →L[ℂ] E))
    (hπ : IsContinuousRepresentation π) : Prop :=
  ∃ C d : ℕ, ∀ p : MvPolynomial (Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) ℂ,
    let A := compactPolynomialAverage ν π hπ p
    FiniteDimensional ℂ A.toLinearMap.range ∧
      Module.finrank ℂ A.toLinearMap.range ≤ C * (p.totalDegree + 1) ^ d

/-- Every irreducible unitary representation of the archimedean general linear group
has polynomial rank bounds for averaging against polynomial weights on the standard
infinite compact subgroup. -/
def ArchimedeanCompactPolynomialRankStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] (n : ℕ)
    [MeasurableSpace (standardInfiniteCompact F n)] [BorelSpace (standardInfiniteCompact F n)]
    (ν : Measure (standardInfiniteCompact F n)) [ν.IsHaarMeasure]
    (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : InfiniteAdelicGL F n →* (E →L[ℂ] E))
    (hπ : IsIrreducibleUnitaryRepresentation π), HasCompactPolynomialRankBound ν π hπ.1.1

end Langlands.TraceFormula.ArchimedeanUnitary
