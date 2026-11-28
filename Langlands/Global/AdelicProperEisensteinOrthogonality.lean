import Langlands.Analysis.Local.PolynomialZeroSet
import Langlands.Global.AdelicTruncatedEisensteinPairing

/-! # Orthogonality of Eisenstein series induced from a proper parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints AdelicSiegelFactors
  Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

/-- The orthogonality part of Delorme (4.6): an Eisenstein series with a proper inducing
parabolic and an imaginary parameter has zero absolutely convergent pairing with every
square-integrable test on every positive central slice. -/
def ProperEisensteinOrthogonalityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν),
    P ≠ fam.top →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p fam.bot) K)
      (hKP : IsIwasawaCompact (fam.p P) K),
    IsMaximalCompactSubgroup F G K →
    IsPositiveTorusCompatible F G fam.T fam.i fam.ν fam.T (𝟙 fam.T) K →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsClosedSubgroup rho →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p P) (fam.iU P) (fam.l P) φ →
    ∀ [IsClosedImmersion (fam.p P).hom.hom.left]
      (r : ParabolicRootPresentation (fam.p P) (fam.l P) (fam.a P))
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus (fam.A P).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
      (E : ComplexCharacterParameter F (fam.P P) → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F (fam.P P))),
    Set.range (imaginaryParameter F (fam.P P)) ⊆ D →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKP.eisensteinSeries φ lam) →
    ∀ x : RealCharacterParameter F (fam.P P),
      fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc fam.top
        (E (imaginaryParameter F (fam.P P) x))

private theorem eq_zero_of_polynomial_mul_eq_zero {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0)
    (h : ∀ s, (p.eval s : ℂ) * f s = 0) : f = 0 := by
  have hp' := Langlands.Analysis.ae_eval_ne_zero (volume : Measure ℝ) n p hp
  rw [← volume_pi] at hp'
  have he : f =ᵐ[volume] (fun _ : Fin n → ℝ => (0 : ℂ)) := by
    filter_upwards [hp'] with s hs
    exact (mul_eq_zero.mp (h s)).resolve_left (Complex.ofReal_ne_zero.mpr hs)
  exact Measure.eq_of_ae_eq he hf continuous_const

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The last step of (4.6) on the actual slice pairing: an integrable continuous family
of pairings that is annihilated by a nonzero spectral polynomial vanishes everywhere.
A different polynomial can be used for each test vector and slice. -/
theorem isSquareIntegrableOrthogonal_of_polynomial_pairing
    {Q : StandardIndex F G fam.i fam.ν} {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d n : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (E : (Fin n → ℝ) → AdelicGroupPoints F G → ℂ)
    (h : ∀ φ : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc (fam.p Q) (fam.iU Q) (fam.l Q) φ →
      ∀ x ∈ fam.positiveSplitComponent Q,
        let f (s : Fin n → ℝ) := fam.squareIntegrablePairingIntegrand K Q x φ (E s)
        let measure := fam.squareIntegrablePairingMeasure K hKc Q
        (∀ s, Integrable (f s) measure) ∧ Continuous (fun s => ∫ z, f s z ∂measure) ∧
          ∃ p : MvPolynomial (Fin n) ℝ, p ≠ 0 ∧ ∀ s, (p.eval s : ℂ) * (∫ z, f s z ∂measure) = 0) :
    ∀ s, fam.IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc Q (E s) := by
  intro s φ hφ x hx
  obtain ⟨hI, hc, p, hp, hmul⟩ := h φ hφ x hx
  refine ⟨hI s, ?_⟩
  exact congrFun (eq_zero_of_polynomial_mul_eq_zero hc p hp hmul) s

end StandardParabolicFamily

end Langlands.Global
