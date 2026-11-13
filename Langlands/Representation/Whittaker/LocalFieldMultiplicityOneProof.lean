import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneStatement
import Langlands.Representation.Whittaker.LocalFieldShalikaInvariance
import Langlands.Representation.Smooth.Contragredient.LocalFieldGelfandKazhdan
import Langlands.Representation.Whittaker.BundledDualTransport
import Langlands.Representation.Whittaker.CoefficientDistribution
import Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof

/-! # Whittaker multiplicity one over every nonarchimedean local field

The all-field Shalika invariance and Gelfand–Kazhdan contragredient theorems, with the
published generalized-coefficient kernel theorem, give
`LocalFieldMultiplicityOneStatement` along the route of the p-adic proof
`Langlands.Whittaker.multiplicityOne`.
-/

noncomputable section

namespace Langlands.Whittaker

open MeasureTheory GeneralLinear HarmonicAnalysis

universe uF uV

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.totallyDisconnectedSpace
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  LocalFieldTopology.generalLinear_nonarchimedean
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace

/-- Bernstein–Zelevinsky (1976), Theorem 5.16, over every nonarchimedean local field
(any characteristic): every nonzero standard Whittaker functional on an irreducible
admissible complex representation of `GL_(n+1)(F)` spans the functional space, with a
unique scalar for each functional. -/
theorem localFieldMultiplicityOne : LocalFieldMultiplicityOneStatement.{uF,uV} := by
  intro F _ _ _ _ n V _ _ ψ ρ hAdm hIrr ℓ₁ ℓ₂ hℓ₁
  let G := GeneralLinear (n + 1) F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := RankinSelberg.generalLinearHaar F n
  have hsym := RankinSelberg.generalLinearHaarSymmetries F n
  let : μ.IsInvInvariant := hsym.1
  have hτμ : MeasurePreserving (weylTransposeHomeomorph n F) μ μ :=
    (hsym.2.2.2 (weylLong (n + 1) F)).comp hsym.2.2.1
  obtain ⟨E, hE⟩ := LocalField.gelfandKazhdanContragredient F n V ρ hAdm hIrr
  let η := smoothDualFunctionalTransport ψ ρ E hE ℓ₁
  have hη : η.val ≠ 0 := smoothDualFunctionalTransport_ne_zero ψ ρ E hE ℓ₁ hℓ₁
  apply generalizedCoefficientKernel G μ V ρ hAdm hIrr (weylTransposeHomeomorph n F)
    (weylTransposeHomeomorph_involutive n F) (weylTransposeHomeomorph_mul n F) hτμ
    (glFunctionals ψ n ρ) η.val hη
    (fun ℓ => LocalField.shalikaDistributionInvariance F n (ψ.scale (-1))
      (generalizedCoefficient μ ρ hAdm.1 ℓ.val η.val)
      (generalizedCoefficient_isBiEquivariant ψ n μ ρ hAdm.1 ℓ η)) ℓ₁ ℓ₂ hℓ₁

end Langlands.Whittaker
