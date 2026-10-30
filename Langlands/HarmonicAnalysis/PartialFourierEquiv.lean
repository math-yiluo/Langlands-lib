import Langlands.HarmonicAnalysis.PartialFourierCompatibilityProof

/-! The chosen last-column Fourier equivalence and the transported JPSS action. -/

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ)
  (hself : IsSelfDual ψ μ)

/-- The actual inverse-character last-column Fourier equivalence, chosen from
the published compatibility theorem for the supplied self-dual measure. -/
noncomputable def partialFourierEquiv :
    SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) :=
  Classical.choose (partialFourierCompatibility ψ μ n hself)

/-- The chosen forward map has the inverse-character integral formula. -/
@[simp] theorem partialFourierEquiv_apply
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    partialFourierEquiv ψ μ n hself Φ m = partialFourierIntegral ψ μ Φ m :=
  (Classical.choose_spec (partialFourierCompatibility ψ μ n hself)).1 Φ m

/-- The inverse of the chosen map has the plus-character integral formula. -/
@[simp] theorem partialFourierEquiv_symm_apply
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    (partialFourierEquiv ψ μ n hself).symm Φ m = partialFourierPlusIntegral ψ μ Φ m :=
  (Classical.choose_spec (partialFourierCompatibility ψ μ n hself)).2.1 Φ m

include hself in
/-- Convergence of the actual inverse-character last-column integrand. -/
theorem partialFourierEquiv_integrable
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    MeasureTheory.Integrable
      (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (-rowPairing (rectangularLastColumn m) u))
      (rowMeasure μ n) :=
  (Classical.choose_spec (partialFourierCompatibility ψ μ n hself)).2.2.1 Φ m

include hself in
/-- Convergence of the actual plus-character last-column integrand. -/
theorem partialFourierEquiv_plus_integrable
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (m : Matrix (Fin n) (Fin (n + 1)) K) :
    MeasureTheory.Integrable
      (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
        ψ.complex (rowPairing (rectangularLastColumn m) u))
      (rowMeasure μ n) :=
  (Classical.choose_spec (partialFourierCompatibility ψ μ n hself)).2.2.2 Φ m

@[simp] theorem partialFourierEquiv_symm_apply_apply
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    (partialFourierEquiv ψ μ n hself).symm (partialFourierEquiv ψ μ n hself Φ) = Φ :=
  (partialFourierEquiv ψ μ n hself).symm_apply_apply Φ

@[simp] theorem partialFourierEquiv_apply_symm_apply
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    partialFourierEquiv ψ μ n hself ((partialFourierEquiv ψ μ n hself).symm Φ) = Φ :=
  (partialFourierEquiv ψ μ n hself).apply_symm_apply Φ

/-- Pointwise forward evaluation determines the actual linear equivalence. -/
theorem partialFourierEquiv_unique
    (E : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (hE : ∀ (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
      (m : Matrix (Fin n) (Fin (n + 1)) K),
      E Φ m = partialFourierIntegral ψ μ Φ m) :
    E = partialFourierEquiv ψ μ n hself := by
  apply LinearEquiv.ext
  intro Φ
  ext m
  exact (hE Φ m).trans (partialFourierEquiv_apply ψ μ n hself Φ m).symm

/-- JPSS Section 6.1 formula (2): conjugate the actual right Schwartz action
through the chosen inverse-character partial Fourier equivalence. -/
noncomputable def rectangularRho0 :
    Representation ℂ (Langlands.GeneralLinear (n + 1) K)
      (SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) := by
  let T := partialFourierEquiv ψ μ n hself
  exact
    { toFun := fun g => T.toLinearMap.comp
        ((rectangularSchwartzRepresentation (K := K) (r := n) (s := n + 1) g).comp
          T.symm.toLinearMap)
      map_one' := by
        apply LinearMap.ext
        intro Φ
        change T (rectangularTranslate 1 (T.symm Φ)) = Φ
        rw [rectangularTranslate_one, T.apply_symm_apply]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro Φ
        change T (rectangularTranslate (g * h) (T.symm Φ)) =
          T (rectangularTranslate g
            (T.symm (T (rectangularTranslate h (T.symm Φ)))))
        rw [T.symm_apply_apply, rectangularTranslate_mul] }

/-- Evaluation of the conjugated action as an equality in the Schwartz space. -/
theorem rectangularRho0_apply
    (g : Langlands.GeneralLinear (n + 1) K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    rectangularRho0 ψ μ n hself g Φ =
      partialFourierEquiv ψ μ n hself
        (rectangularTranslate g ((partialFourierEquiv ψ μ n hself).symm Φ)) := rfl

@[simp] theorem rectangularRho0_one
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    rectangularRho0 ψ μ n hself 1 Φ = Φ := by
  rw [rectangularRho0_apply, rectangularTranslate_one, LinearEquiv.apply_symm_apply]

theorem rectangularRho0_mul
    (g h : Langlands.GeneralLinear (n + 1) K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    rectangularRho0 ψ μ n hself (g * h) Φ =
      rectangularRho0 ψ μ n hself g (rectangularRho0 ψ μ n hself h Φ) := by
  simp only [rectangularRho0_apply, rectangularTranslate_mul, LinearEquiv.symm_apply_apply]

/-- The source's defining relation `ρ₀(g)(Φ~) = (gΦ)~`. -/
theorem rectangularRho0_intertwine
    (g : Langlands.GeneralLinear (n + 1) K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    rectangularRho0 ψ μ n hself g (partialFourierEquiv ψ μ n hself Φ) =
      partialFourierEquiv ψ μ n hself (rectangularTranslate g Φ) := by
  rw [rectangularRho0_apply, LinearEquiv.symm_apply_apply]

end Langlands.HarmonicAnalysis
