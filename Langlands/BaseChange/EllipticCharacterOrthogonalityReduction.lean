import Langlands.BaseChange.CharacterLocalValueConjugation
import Langlands.BaseChange.EllipticCharacterCentralProduct
import Langlands.BaseChange.EllipticCharacterOrthogonalityStatement
import Langlands.BaseChange.EllipticCoefficientTraceStatement
import Langlands.BaseChange.EllipticOrbitalCoefficientStatement
import Langlands.BaseChange.EllipticWeylIntegrationStatement

/-! # Elliptic character orthogonality from three analytic statements -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

section Conjugation

variable {F : Type*} [Field F] {n : ℕ}

/-- Regular ellipticity is invariant under conjugation. -/
theorem isRegularElliptic_mul_conj_inv_iff (a b : GeneralLinear n F) :
    IsRegularElliptic (a * b * a⁻¹) ↔ IsRegularElliptic b := by
  have h : ((a * b * a⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F).charpoly =
      (b : Matrix (Fin n) (Fin n) F).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj a b
  simp only [IsRegularElliptic, IsRegularSemisimple, h]

end Conjugation

/-- The orbital integral formula for elliptic coefficients, the elliptic Weyl integration
formula modulo the center and the elliptic part of the trace of a square-integrable coefficient
together imply elliptic character orthogonality. -/
def EllipticCharacterOrthogonalityReductionStatement.{u, uV} : Prop :=
  EllipticOrbitalCoefficientStatement.{u, uV} → EllipticWeylIntegrationStatement.{u} →
    EllipticCoefficientTraceStatement.{u, uV} → EllipticCharacterOrthogonalityStatement.{u, uV}

theorem ellipticCharacterOrthogonalityReduction.{u, uV} :
    EllipticCharacterOrthogonalityReductionStatement.{u, uV} := by
  classical
  intro hE hW hS F _ _ _ _ _ n hn
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let G := GeneralLinear n F
  let Z := Subgroup.center G
  let : MeasurableSpace (G ⧸ Z) := centralQuotientMeasurableSpace F n
  have : BorelSpace (G ⧸ Z) := centralQuotientBorelSpace F n
  let E : Set (G ⧸ Z) := QuotientGroup.mk '' {g : G | IsRegularElliptic g}
  obtain ⟨ν, -, hν⟩ := hW F n hn
  refine ⟨ν, ?_⟩
  intro V W _ _ _ _ ρ π hρ hπ hirρ hirπ cρ cπ hc Θρ Θπ hΘρ hΘπ
  let μ : Measure (G ⧸ Z) := Measure.haar
  obtain ⟨d, hd⟩ := exists_isCentralFormalDegree F n μ π hπ hirπ
  have hdpos : 0 < d := hd.1
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
  have : Nontrivial W := by
    have := hirπ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨ℓ, hℓ⟩ := HarishChandraSchwartz.exists_smoothDual_eq_one
    (LevelZero.compactOpen_cofinal (F := F) n) hπ.isAdmissible.1 hv
  obtain ⟨Φ, hΦ, hΦint, hΦval⟩ :=
    hS F n hn μ ρ π hρ hπ hirρ hirπ cρ cπ hc d hd Θρ hΘρ v ℓ
  let p : G ⧸ Z → ℂ := ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ
  have hpmk : ∀ g : G, p (QuotientGroup.mk g) =
      if h : IsRegularElliptic g then Θρ ⟨g, h⟩ * star (Θπ ⟨g, h⟩) else 0 :=
    ellipticCharacterProduct_mk cρ cπ hc Θρ Θπ hΘρ hΘπ
  -- The orbital integrals of `Φ` at regular elliptic points.
  have horbit : ∀ (b : G) (hb : IsRegularElliptic b), ∃ o : G ⧸ Z → ℂ,
      Integrable o μ ∧ (Θπ ⟨b, hb⟩ = d * ∫ q, o q ∂μ) ∧
      (fun g : G ⧸ Z => Φ (g * QuotientGroup.mk b * g⁻¹)) =
        fun g => Θρ ⟨b, hb⟩ * star (o g) := by
    intro b hb
    obtain ⟨o, ho, hoint, hoval⟩ :=
      hE F n hn μ π hπ hirπ d hd b hb (Θπ ⟨b, hb⟩) (hΘπ ⟨b, hb⟩) v ℓ
    refine ⟨o, hoint, ?_, ?_⟩
    · rw [hoval, hℓ, mul_one, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    · funext g
      induction g using QuotientGroup.induction_on with
      | H a =>
        have hab : IsRegularElliptic (a * b * a⁻¹) := (isRegularElliptic_mul_conj_inv_iff a b).2 hb
        have hval : Θρ ⟨a * b * a⁻¹, hab⟩ = Θρ ⟨b, hb⟩ :=
          (hΘρ ⟨_, hab⟩).unique (by simpa using (hΘρ ⟨b, hb⟩).conjugate a⁻¹)
        change Φ (QuotientGroup.mk (a * b * a⁻¹)) = _
        rw [hΦ, dite_eq_left hab, hval, ho]
  -- `p` is `d` times the orbital integral of `Φ`.
  have hpoint : ∀ x : G ⧸ Z, p x = d * ∫ g, Φ (g * x * g⁻¹) ∂μ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H b =>
      by_cases hb : IsRegularElliptic b
      · obtain ⟨o, -, hΘ, hfun⟩ := horbit b hb
        have hconj : ∫ g, star (o g) ∂μ = star (∫ g, o g ∂μ) := integral_conj
        have hs : star (d : ℂ) = d := Complex.conj_ofReal d
        rw [hpmk, dite_eq_left hb, hfun, integral_const_mul, hconj, hΘ, star_mul', hs]
        ring
      · have hzero : (fun g : G ⧸ Z => Φ (g * QuotientGroup.mk b * g⁻¹)) = fun _ => 0 := by
          funext g
          induction g using QuotientGroup.induction_on with
          | H a =>
            have hab : ¬ IsRegularElliptic (a * b * a⁻¹) :=
              fun h => hb ((isRegularElliptic_mul_conj_inv_iff a b).1 h)
            change Φ (QuotientGroup.mk (a * b * a⁻¹)) = 0
            rw [hΦ, dite_eq_right hab]
        rw [hpmk, dite_eq_right hb, hzero, integral_zero, mul_zero]
  -- `Φ` vanishes off the regular elliptic set.
  have hΦE : ∀ q ∉ E, Φ q = 0 := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hg : ¬ IsRegularElliptic g := fun h => hq ⟨g, h, rfl⟩
      rw [hΦ, dite_eq_right hg]
  obtain ⟨-, -, hIval⟩ := hν μ Φ hΦint.integrableOn
  -- Integrability of `p` from the Weyl formula applied to `‖Φ‖`.
  let Ψ : G ⧸ Z → ℂ := fun q => ((‖Φ q‖ : ℝ) : ℂ)
  have hΨint : Integrable Ψ μ := hΦint.norm.ofReal
  obtain ⟨-, hBint, -⟩ := hν μ Ψ hΨint.integrableOn
  have hbound : ∀ x : G ⧸ Z, ‖p x‖ ≤ d * ‖∫ g, Ψ (g * x * g⁻¹) ∂μ‖ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H b =>
      by_cases hb : IsRegularElliptic b
      · obtain ⟨o, -, hΘ, hfun⟩ := horbit b hb
        have hΨfun : (fun g : G ⧸ Z => Ψ (g * QuotientGroup.mk b * g⁻¹)) =
            fun g => ((‖Θρ ⟨b, hb⟩‖ * ‖o g‖ : ℝ) : ℂ) := by
          funext g
          change ((‖Φ (g * QuotientGroup.mk b * g⁻¹)‖ : ℝ) : ℂ) = _
          rw [show Φ (g * QuotientGroup.mk b * g⁻¹) = Θρ ⟨b, hb⟩ * star (o g) from
            congrFun hfun g, norm_mul, norm_star]
        have hle := norm_integral_le_integral_norm (μ := μ) o
        have hnn : 0 ≤ ∫ g, ‖o g‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
        rw [hΨfun, integral_complex_ofReal, integral_const_mul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hnn), hpmk, dite_eq_left hb,
          norm_mul, norm_star, hΘ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hdpos.le]
        calc ‖Θρ ⟨b, hb⟩‖ * (d * ‖∫ g, o g ∂μ‖)
            = (d * ‖Θρ ⟨b, hb⟩‖) * ‖∫ g, o g ∂μ‖ := by ring
          _ ≤ (d * ‖Θρ ⟨b, hb⟩‖) * ∫ g, ‖o g‖ ∂μ :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg hdpos.le (norm_nonneg _))
          _ = d * (‖Θρ ⟨b, hb⟩‖ * ∫ g, ‖o g‖ ∂μ) := by ring
      · rw [hpmk, dite_eq_right hb, norm_zero]
        exact mul_nonneg hdpos.le (norm_nonneg _)
  have hpmeas : Measurable p := measurable_ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ
  have hpint : Integrable p ν :=
    (hBint.norm.const_mul d).mono' hpmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine ⟨p, hpmk, hpint, ?_⟩
  have hpfun : p = fun x => (d : ℂ) * ∫ g, Φ (g * x * g⁻¹) ∂μ := funext hpoint
  rw [hpfun, integral_const_mul, ← hIval,
    setIntegral_eq_integral_of_forall_compl_eq_zero hΦE, hΦval, hℓ]
  split_ifs <;> simp [hd0]

end Langlands.BaseChange
