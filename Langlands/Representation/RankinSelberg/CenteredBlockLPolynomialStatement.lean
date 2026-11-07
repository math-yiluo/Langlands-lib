import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.SpectralRescaling
import Langlands.Representation.RankinSelberg.SegmentGammaTelescopingStatement

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear Whittaker HarmonicAnalysis SegmentGammaTelescoping

universe uF uV uW

/-- The positive half-step spectral scale `q^(-1/2)`. -/
def centeredHalfShiftUnit {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) : ℂˣ :=
  spectralShiftUnit F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one (1 / 2)

/-- A base pair's certified polynomials rescale to every pair of centered
blocks, with inverse shifts for their actual inverse-transpose pullbacks. -/
def CenteredBlockLPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b m n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W)
    (P PD : ℂ[X]),
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
    (letI := F.canonicalTopologicalData.topology;
      letI := F.canonicalTopologicalData.valuativeRel;
      letI := F.canonicalTopologicalData.localField;
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback π) (inverseTransposePullback σ) PD) →
    ∀ (i : Fin (m + 1)) (j : Fin (n + 1)),
      IsPadicSymmetricLPolynomial F ψ ν.val
        (centeredSegmentBlocks F m π i) (centeredSegmentBlocks F n σ j)
        (polynomialRescale (centeredHalfShiftUnit F ^ blockExponent m n i.val j.val) P) ∧
      (letI := F.canonicalTopologicalData.topology;
        letI := F.canonicalTopologicalData.valuativeRel;
        letI := F.canonicalTopologicalData.localField;
        IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
          (inverseTransposePullback (centeredSegmentBlocks F m π i))
          (inverseTransposePullback (centeredSegmentBlocks F n σ j))
          (polynomialRescale
            (centeredHalfShiftUnit F ^ (-blockExponent m n i.val j.val)) PD))

end Langlands.RankinSelberg
