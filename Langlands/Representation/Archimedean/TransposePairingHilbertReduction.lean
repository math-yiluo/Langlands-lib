import Langlands.Representation.Archimedean.TransposePairingRestriction
import Langlands.Representation.Archimedean.HilbertGlobalizationStatement
import Langlands.Representation.Archimedean.SmoothHilbertTransposePairingStatement
import Langlands.Representation.Archimedean.TransposePairingStatement

/-! # Restriction of genuine smooth Hilbert pairings -/

noncomputable section
universe uV uH
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type) [RCLike F] (n : ℕ)
  {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (e : V ≃ₗ[ℂ] smoothHilbertKFinite F n R)

/-- The explicit bilinear form on the algebraic compact-finite realization,
obtained by restricting both smooth arguments. -/
def restrictSmoothHilbertPairing
    (B : DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ]
      DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ] ℂ) :
    V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  restrictRealizationPairing (smoothHilbertGlobalizationMap F n R e) B

/-- A genuine smooth Hilbert globalization supplies exactly the weak scalar
derivative, compact equivariance and density data used by restriction. -/
theorem isDenseWeakGLRealization_of_smoothHilbertGlobalization
    (h : IsSmoothHilbertGlobalization F n R ρ π e) :
    IsDenseWeakGLRealization F n ρ π
      (DerivativeSmoothVectors.representation (matrixModel F n) R)
      (smoothHilbertGlobalizationMap F n R e) := by
  refine ⟨?_, h.2.1, h.2.2.1, ?_⟩
  · intro v w hvw
    apply e.injective
    exact Subtype.ext hvw
  · intro X v ℓ hℓ
    have hd := h.2.2.2.2 X (smoothHilbertGlobalizationMap F n R e v) ⟨ℓ, hℓ⟩
    simpa only [ContinuousLinearMap.coe_mk', generalLinearRealExp, matrixExponentialGL,
      ← h.2.2.2.1 X v] using hd

/-- Restrict a nonzero separately continuous smooth Hilbert pairing to its
dense algebraic compact-finite realization. -/
theorem hasNonzeroTransposeGKPairing_of_smoothHilbertGlobalization
    (hg : IsSmoothHilbertGlobalization F n R ρ π e)
    (hp : HasNonzeroSmoothHilbertTransposePairing F n R) :
    HasNonzeroTransposeGKPairing F n ρ π := by
  obtain ⟨B, hB, hne⟩ := hp
  have hr := isDenseWeakGLRealization_of_smoothHilbertGlobalization F n R ρ π e hg
  refine ⟨restrictSmoothHilbertPairing F n R e B, ?_, ?_⟩
  · exact isTransposeInvariantGKPairing_restrict F n ρ π
      (DerivativeSmoothVectors.representation (matrixModel F n) R)
      (smoothHilbertGlobalizationMap F n R e) hr B hB.1 hB.2.1 hB.2.2
  · exact restrictRealizationPairing_ne_zero (smoothHilbertGlobalizationMap F n R e)
      hr.2.1 B hB.1 hB.2.1 hne

/-- The two real analytic existence inputs imply the exact real algebraic
inverse-transpose pairing statement. -/
theorem realTransposePairing_of_hilbert
    (hg : RealHilbertGlobalizationStatement.{uV})
    (hp : RealSmoothHilbertTransposePairingStatement.{uV}) :
    RealTransposePairingStatement.{uV} := by
  intro r V _ _ ρ π hGK hirr hadm
  obtain ⟨H, hnorm, hinner, hcomplete, R, e, he⟩ := hg r V ρ π hGK hirr hadm
  let := hnorm
  let := hinner
  let := hcomplete
  exact hasNonzeroTransposeGKPairing_of_smoothHilbertGlobalization ℝ (r + 1)
    R ρ π e he (hp r H R he.1)

/-- The two complex analytic existence inputs imply the exact complex
algebraic inverse-transpose pairing statement. -/
theorem complexTransposePairing_of_hilbert
    (hg : ComplexHilbertGlobalizationStatement.{uV})
    (hp : ComplexSmoothHilbertTransposePairingStatement.{uV}) :
    ComplexTransposePairingStatement.{uV} := by
  intro r V _ _ ρ π hGK hirr hadm
  obtain ⟨H, hnorm, hinner, hcomplete, R, e, he⟩ := hg r V ρ π hGK hirr hadm
  let := hnorm
  let := hinner
  let := hcomplete
  exact hasNonzeroTransposeGKPairing_of_smoothHilbertGlobalization ℂ (r + 1)
    R ρ π e he (hp r H R he.1)

/-- The two real/complex analytic conjunctions imply the unchanged algebraic
pairing conjunction, with the carrier universe free. -/
theorem archimedeanTransposePairing_of_hilbert
    (hg : ArchimedeanHilbertGlobalizationStatement.{uV})
    (hp : ArchimedeanSmoothHilbertTransposePairingStatement.{uV}) :
    ArchimedeanTransposePairingStatement.{uV} :=
  ⟨realTransposePairing_of_hilbert hg.1 hp.1,
    complexTransposePairing_of_hilbert hg.2 hp.2⟩

end Langlands.Archimedean
