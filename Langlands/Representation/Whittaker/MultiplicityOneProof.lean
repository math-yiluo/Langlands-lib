import Langlands.Representation.Whittaker.MultiplicityOneStatement
import Langlands.Representation.Whittaker.BundledDualTransport
import Langlands.Representation.Whittaker.CoefficientDistribution
import Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof
import Langlands.Representation.Whittaker.DistributionInvarianceProof
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.LocalField.Canonical
import Langlands.Group.GL.Nonarchimedean
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # Whittaker multiplicity one for irreducible admissible representations

The published distribution-invariance, contragredient and generalized-coefficient
kernel theorems give the exact scalar multiplicity-one statement.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory GeneralLinear HarmonicAnalysis

universe uF uV

private theorem weylTranspose_preserves_haar
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear (n + 1) F)]
    [BorelSpace (GeneralLinear (n + 1) F)] :
    MeasurePreserving (weylTransposeHomeomorph n F)
      (RankinSelberg.generalLinearHaar F n) (RankinSelberg.generalLinearHaar F n) := by
  have h := RankinSelberg.generalLinearHaarSymmetries F n
  exact (h.2.2.2 (weylLong (n + 1) F)).comp h.2.2.1

/-- Every nonzero standard Whittaker functional on an irreducible admissible
complex representation of a positive-rank p-adic general linear group spans
the functional space, with a unique scalar for each functional. -/
theorem multiplicityOne : MultiplicityOneStatement.{uF,uV} := by
  intro p hp F
  let := F.canonicalNormedField
  let := F.canonicalValuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  intro n V _ _ ψ ρ hAdm hIrr ℓ₁ ℓ₂ hℓ₁
  let G := GeneralLinear (n + 1) F.Carrier
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  let : NonarchimedeanGroup G := valuativeGeneralLinearNonarchimedean F.Carrier (n + 1)
  let μ := RankinSelberg.generalLinearHaar F.Carrier n
  let : μ.IsInvInvariant := (RankinSelberg.generalLinearHaarSymmetries F.Carrier n).1
  obtain ⟨E, hE⟩ := gelfandKazhdanContragredient p hp F n V ρ hAdm hIrr
  let η := smoothDualFunctionalTransport ψ ρ E hE ℓ₁
  have hη : η.val ≠ 0 := smoothDualFunctionalTransport_ne_zero ψ ρ E hE ℓ₁ hℓ₁
  apply generalizedCoefficientKernel G μ V ρ hAdm hIrr (weylTransposeHomeomorph n F.Carrier)
    (weylTransposeHomeomorph_involutive n F.Carrier)
    (weylTransposeHomeomorph_mul n F.Carrier)
    (weylTranspose_preserves_haar F.Carrier n) (glFunctionals ψ n ρ) η.val hη
    (fun ℓ => shalikaDistributionInvariance p hp F n (ψ.scale (-1))
      (generalizedCoefficient μ ρ hAdm.1 ℓ.val η.val)
      (generalizedCoefficient_isBiEquivariant ψ n μ ρ hAdm.1 ℓ η)) ℓ₁ ℓ₂ hℓ₁

end Langlands.Whittaker
