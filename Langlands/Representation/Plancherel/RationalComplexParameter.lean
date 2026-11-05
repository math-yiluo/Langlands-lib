import Langlands.Representation.Plancherel.RationalComplexParameterStatement

/-! # The period kernel of the actual complex-character exponential -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

private theorem log_cardinality_ne_zero :
    (Real.log (LocalField.residueCardinality F : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.log_pos (by
    exact_mod_cast LocalField.residueCardinality_gt_one F)).ne'

private theorem complex_period_ne_zero :
    rationalImageComplexPeriod (F := F) ≠ 0 :=
  div_ne_zero Complex.two_pi_I_ne_zero (log_cardinality_ne_zero (F := F))

private theorem scalar_exponential_kernel (z : ℂ) :
    Complex.exp (-z * (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)) = 1 ↔
      ∃ n : ℤ, z = rationalImageComplexPeriod (F := F) * (n : ℂ) := by
  let L : ℂ := (Real.log (LocalField.residueCardinality F : ℝ) : ℂ)
  have hL : L ≠ 0 := log_cardinality_ne_zero (F := F)
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨-n, ?_⟩
    change z = (2 * Real.pi * Complex.I / L) * ((-n : ℤ) : ℂ)
    calc
      z = -(-z * L) / L := by
        rw [neg_mul, neg_neg, mul_div_cancel_right₀ _ hL]
      _ = -((n : ℂ) * (2 * Real.pi * Complex.I)) / L := by rw [hn]
      _ = (2 * Real.pi * Complex.I / L) * ((-n : ℤ) : ℂ) := by
        rw [Int.cast_neg]
        ring
  · rintro ⟨n, rfl⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-n, ?_⟩
    change -((2 * Real.pi * Complex.I / L) * (n : ℂ)) * L =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
    rw [Int.cast_neg]
    field_simp

/-- The scalar periods assemble into exactly the actual integer-dual range. -/
theorem rationalImageComplexCharacter_eq_one_iff
    (lam : rationalImageComplexFunctionals G) :
    rationalImageComplexCharacter G lam = 1 ↔ lam ∈ rationalImagePeriodLattice G := by
  classical
  constructor
  · intro h
    have hex (a : Additive (rationalDiscreteValuationImage G)) :
        ∃ n : ℤ, lam a = rationalImageComplexPeriod (F := F) * (n : ℂ) := by
      apply (scalar_exponential_kernel (F := F) (lam a)).mp
      have ha := congrArg (fun chi : rationalImageCharacters G => (chi a.toMul : ℂ)) h
      exact ha
    choose n hn using hex
    have hinj : Function.Injective (fun m : ℤ =>
        rationalImageComplexPeriod (F := F) * (m : ℂ)) := by
      intro m k hmk
      exact_mod_cast mul_left_cancel₀ (complex_period_ne_zero (F := F)) hmk
    let f : Additive (rationalDiscreteValuationImage G) →+ ℤ :=
      { toFun := n
        map_zero' := by
          apply hinj
          change rationalImageComplexPeriod (F := F) * (n 0 : ℂ) =
            rationalImageComplexPeriod (F := F) * ((0 : ℤ) : ℂ)
          rw [Int.cast_zero, mul_zero, ← hn 0, map_zero]
        map_add' a b := by
          apply hinj
          change rationalImageComplexPeriod (F := F) * (n (a + b) : ℂ) =
            rationalImageComplexPeriod (F := F) * ((n a + n b : ℤ) : ℂ)
          rw [Int.cast_add, mul_add, ← hn (a + b), ← hn a, ← hn b, map_add] }
    change lam ∈ (rationalImagePeriodEmbedding G).range
    refine ⟨f, ?_⟩
    apply AddMonoidHom.ext
    intro a
    exact (hn a).symm
  · rintro ⟨n, rfl⟩
    apply ContinuousMonoidHom.ext
    intro a
    apply Units.ext
    exact (scalar_exponential_kernel (F := F) _).mpr ⟨n (Additive.ofMul a), rfl⟩

/-- Equality of exponentials is equality modulo the actual period subgroup. -/
theorem rationalImageComplexCharacter_eq_iff
    (lam mu : rationalImageComplexFunctionals G) :
    rationalImageComplexCharacter G lam = rationalImageComplexCharacter G mu ↔
      lam - mu ∈ rationalImagePeriodLattice G := by
  have hdiv := map_div (rationalImageComplexExponential G)
    (Multiplicative.ofAdd lam) (Multiplicative.ofAdd mu)
  change rationalImageComplexCharacter G (lam - mu) =
    rationalImageComplexCharacter G lam / rationalImageComplexCharacter G mu at hdiv
  rw [← rationalImageComplexCharacter_eq_one_iff G, hdiv, div_eq_one]

/-- An arbitrary lift has the already defined normalized real part. -/
theorem rationalImageParameterRealPart_of_lift
    (chi : rationalImageCharacters G) (lam : rationalImageComplexFunctionals G)
    (h : rationalImageComplexCharacter G lam = chi) :
    rationalImageParameterRealPart G lam = rationalImageRealPart G chi := by
  rw [← h, rationalImageRealPart_complexCharacter]

/-- The unitary characters are exactly the exponentials of zero-real-part parameters. -/
theorem rationalImageComplexCharacter_unitary_iff
    (lam : rationalImageComplexFunctionals G) :
    rationalImageComplexCharacter G lam ∈
        unitaryCharacters (rationalDiscreteValuationImage G) ↔
      rationalImageParameterRealPart G lam = 0 := by
  rw [← rationalImageRealPart_eq_zero_iff G, rationalImageRealPart_complexCharacter]

/-- Every actual image character has the constructed basis-value lift. -/
theorem rationalImageComplexCharacter_surjective
    (hG : GroupScheme.IsConnectedReductive G) :
    Function.Surjective (rationalImageComplexCharacter G) :=
  fun chi => ⟨rationalImageComplexLift G hG chi, rationalImageComplexCharacter_lift G hG chi⟩

/-- The unitary image is precisely the exponential of imaginary real functionals. -/
theorem rationalImageUnitary_iff_imaginary_exponential
    (hG : GroupScheme.IsConnectedReductive G) (chi : rationalImageCharacters G) :
    chi ∈ unitaryCharacters (rationalDiscreteValuationImage G) ↔
      ∃ phi : rationalImageRealFunctionals G,
        rationalImageComplexCharacter G (Complex.I • rationalImageParameterOfReal G phi) =
          chi := by
  constructor
  · intro hchi
    obtain ⟨lam, hlam⟩ := rationalImageComplexCharacter_surjective G hG chi
    have hre := (rationalImageComplexCharacter_unitary_iff G lam).mp (hlam ▸ hchi)
    let phi : rationalImageRealFunctionals G :=
      { toFun := fun a => (lam a).im
        map_zero' := by simp
        map_add' a b := by simp }
    refine ⟨phi, ?_⟩
    have heq : Complex.I • rationalImageParameterOfReal G phi = lam := by
      apply AddMonoidHom.ext
      intro a
      have ha := DFunLike.congr_fun hre a
      apply Complex.ext
      · simpa [rationalImageParameterRealPart, rationalImageParameterOfReal] using ha.symm
      · simp [rationalImageParameterOfReal, phi]
    rw [heq, hlam]
  · rintro ⟨phi, rfl⟩
    apply (rationalImageComplexCharacter_unitary_iff G _).mpr
    apply AddMonoidHom.ext
    intro a
    simp [rationalImageParameterRealPart, rationalImageParameterOfReal]

/-- All eight actual-image and canonical actual-point assertions. -/
theorem rationalComplexParameter : RationalComplexParameterStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  refine ⟨rationalImageComplexCharacter_surjective G hG,
    rationalImageComplexCharacter_eq_one_iff G, rationalImageComplexCharacter_eq_iff G,
    rationalImageParameterRealPart_of_lift G, rationalImageComplexCharacter_unitary_iff G,
    rationalImageUnitary_iff_imaginary_exponential G hG, ?_, ?_⟩
  · intro chi
    obtain ⟨lam, hlam⟩ := rationalImageComplexCharacter_surjective G hG
      ((rationalCanonicalImageUnramifiedContinuousEquiv G).symm chi)
    refine ⟨Multiplicative.ofAdd lam, ?_⟩
    change rationalCanonicalImageUnramifiedContinuousEquiv G
      (rationalImageComplexCharacter G lam) = chi
    rw [hlam, (rationalCanonicalImageUnramifiedContinuousEquiv G).apply_symm_apply]
  · intro lam mu
    change rationalCanonicalImageUnramifiedContinuousEquiv G
      (rationalImageComplexCharacter G lam) =
        rationalCanonicalImageUnramifiedContinuousEquiv G
          (rationalImageComplexCharacter G mu) ↔ _
    rw [(rationalCanonicalImageUnramifiedContinuousEquiv G).injective.eq_iff,
      rationalImageComplexCharacter_eq_iff]

end Langlands.Plancherel
