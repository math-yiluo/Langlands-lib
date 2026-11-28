import Langlands.Correspondence.HenniartLaumonNumericalReductionStatement
import Langlands.Galois.CoefficientIdentification

/-!
# Proof of the reduction of Laumon's numerical statement E1b

A bijection of ℓ-adic Swan strata that commutes with every unramified ℓ-adic twist matches
the refined ℓ-adic strata of the two ranks; the ℓ-adic/Weil orbit comparison then carries
both onto the refined Weil strata. This proves `LaumonNumericalReductionStatement`; it does
not prove either of its two premises.
-/

noncomputable section

universe uK uΩ uW

namespace Langlands.Henniart.LocalNumerical

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime]

/-- Two rank-`k + 1` ℓ-adic classes have the same unramified-twist orbit exactly when the
first is an unramified twist of the second. -/
theorem ladicUnramifiedOrbitClass_eq_iff (k : ℕ)
    (ρ ρ' : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) :
    ladicUnramifiedOrbitClass K Ω ℓ k ρ = ladicUnramifiedOrbitClass K Ω ℓ k ρ' ↔
      ∃ χ : ladicUnramifiedCharacters K Ω ℓ, ladicUnramifiedTwist K Ω ℓ k χ ρ' = ρ := by
  let := ladicUnramifiedTwistAction.{uK, uΩ, uW} K Ω ℓ
  unfold ladicUnramifiedOrbitClass
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, sigma_mk_injective
      (β := fun j : ℕ => IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ j.succPNat) (i := k) hχ⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, congrArg (Sigma.mk k) hχ⟩

/-- A bijection between the ℓ-adic classes of Swan exponent `s` in ranks `k + 1` and
`k' + 1` that commutes with every unramified ℓ-adic twist matches the refined ℓ-adic strata
of the two ranks at every torsion number: they have the same extended cardinality. -/
theorem ladicRefinedStratum_encard_eq_of_twistEquiv (ι : PadicAlgCl ℓ →+* ℂ) {k k' s : ℕ}
    (Φ : {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat //
        LadicHasSwan K Ω ℓ ι ρ s} ≃
      {ρ' : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k'.succPNat //
        LadicHasSwan K Ω ℓ ι ρ' s})
    (hΦ : ∀ (χ : ladicUnramifiedCharacters K Ω ℓ)
      (ρ : {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat //
        LadicHasSwan K Ω ℓ ι ρ s}),
      ∃ h : LadicHasSwan K Ω ℓ ι (ladicUnramifiedTwist K Ω ℓ k χ ρ.1) s,
        (Φ ⟨ladicUnramifiedTwist K Ω ℓ k χ ρ.1, h⟩).1 =
          ladicUnramifiedTwist K Ω ℓ k' χ (Φ ρ).1)
    (f : ℕ) :
    (ladicRefinedStratum.{uK, uΩ, uW} K Ω ℓ ι k s f).encard =
      (ladicRefinedStratum.{uK, uΩ, uW} K Ω ℓ ι k' s f).encard := by
  classical
  -- `Φ` relates twists in both directions.
  have htw : ∀ (χ : ladicUnramifiedCharacters K Ω ℓ)
      (ρ₁ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) (h₁ : LadicHasSwan K Ω ℓ ι ρ₁ s)
      (ρ₂ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) (h₂ : LadicHasSwan K Ω ℓ ι ρ₂ s),
      ladicUnramifiedTwist K Ω ℓ k χ ρ₁ = ρ₂ ↔
        ladicUnramifiedTwist K Ω ℓ k' χ (Φ ⟨ρ₁, h₁⟩).1 = (Φ ⟨ρ₂, h₂⟩).1 := by
    intro χ ρ₁ h₁ ρ₂ h₂
    obtain ⟨h, hh⟩ := hΦ χ ⟨ρ₁, h₁⟩
    rw [← hh]
    constructor
    · intro e
      exact congrArg (fun x => (Φ x).1) (Subtype.ext e)
    · intro e
      exact congrArg Subtype.val (Φ.injective (Subtype.ext e))
  -- `Φ` preserves the torsion number.
  have htors : ∀ (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
      (hρ : LadicHasSwan K Ω ℓ ι ρ s),
      ladicTorsionNumber K Ω ℓ (Φ ⟨ρ, hρ⟩).1 = ladicTorsionNumber K Ω ℓ ρ := by
    intro ρ hρ
    unfold ladicTorsionNumber
    exact Nat.card_congr (Equiv.subtypeEquivRight fun χ => (htw χ ρ hρ ρ hρ).symm)
  -- `Φ` preserves and reflects equality of unramified-twist orbits.
  have horb : ∀ (ρ₁ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
      (h₁ : LadicHasSwan K Ω ℓ ι ρ₁ s)
      (ρ₂ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat) (h₂ : LadicHasSwan K Ω ℓ ι ρ₂ s),
      ladicUnramifiedOrbitClass K Ω ℓ k ρ₁ = ladicUnramifiedOrbitClass K Ω ℓ k ρ₂ ↔
        ladicUnramifiedOrbitClass K Ω ℓ k' (Φ ⟨ρ₁, h₁⟩).1 =
          ladicUnramifiedOrbitClass K Ω ℓ k' (Φ ⟨ρ₂, h₂⟩).1 := by
    intro ρ₁ h₁ ρ₂ h₂
    rw [ladicUnramifiedOrbitClass_eq_iff, ladicUnramifiedOrbitClass_eq_iff]
    exact exists_congr fun χ => htw χ ρ₂ h₂ ρ₁ h₁
  -- The induced map of orbits, extended by the identity off the orbits of Swan exponent `s`.
  let F : LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ →
      LadicUnramifiedOrbitClasses.{uK, uΩ, uW} K Ω ℓ := fun c =>
    if h : ∃ ρ : {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat //
        LadicHasSwan K Ω ℓ ι ρ s}, ladicUnramifiedOrbitClass K Ω ℓ k ρ.1 = c then
      ladicUnramifiedOrbitClass K Ω ℓ k' (Φ h.choose).1
    else c
  have hF : ∀ (ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat)
      (hρ : LadicHasSwan K Ω ℓ ι ρ s),
      F (ladicUnramifiedOrbitClass K Ω ℓ k ρ) =
        ladicUnramifiedOrbitClass K Ω ℓ k' (Φ ⟨ρ, hρ⟩).1 := by
    intro ρ hρ
    have h : ∃ ρ' : {ρ : IrreducibleLadicClass.{uK, uΩ, uW} K Ω ℓ k.succPNat //
        LadicHasSwan K Ω ℓ ι ρ s},
        ladicUnramifiedOrbitClass K Ω ℓ k ρ'.1 = ladicUnramifiedOrbitClass K Ω ℓ k ρ :=
      ⟨⟨ρ, hρ⟩, rfl⟩
    dsimp only [F]
    rw [dite_eq_left h]
    exact (horb _ h.choose.2 ρ hρ).mp h.choose_spec
  have hinj : Set.InjOn F (ladicRefinedStratum K Ω ℓ ι k s f) := by
    rintro _ ⟨ρ₁, rfl, h₁, -⟩ _ ⟨ρ₂, rfl, h₂, -⟩ e
    rw [hF ρ₁ h₁, hF ρ₂ h₂] at e
    exact (horb ρ₁ h₁ ρ₂ h₂).mpr e
  have himage : F '' ladicRefinedStratum K Ω ℓ ι k s f = ladicRefinedStratum K Ω ℓ ι k' s f := by
    ext c
    constructor
    · rintro ⟨_, ⟨ρ, rfl, hρ, hf⟩, rfl⟩
      exact ⟨(Φ ⟨ρ, hρ⟩).1, (hF ρ hρ).symm, (Φ ⟨ρ, hρ⟩).2, (htors ρ hρ).trans hf⟩
    · rintro ⟨ρ', rfl, hρ', hf⟩
      obtain ⟨⟨ρ, hρ⟩, hΦρ⟩ := Φ.surjective ⟨ρ', hρ'⟩
      refine ⟨ladicUnramifiedOrbitClass K Ω ℓ k ρ, ⟨ρ, rfl, hρ, ?_⟩, ?_⟩
      · rw [← htors ρ hρ, hΦρ]
        exact hf
      · rw [hF ρ hρ, hΦρ]
  rw [← himage, hinj.encard_image]

end Langlands.Henniart.LocalNumerical

namespace Langlands.Henniart

open LocalNumerical ValuativeRel

/-- **Reduction of E1b.** The orbit comparison `LadicWeilOrbitComparisonStatement` and
Laumon's twist-equivariant bijection `LaumonLadicTwistBijectionStatement` imply Laumon's
numerical statement `LaumonNumericalStatement`. -/
theorem laumonNumericalReduction : LaumonNumericalReductionStatement.{uK, uW} := by
  intro hcomp hlaumon k _ _ d s f X Ω hs _
  let : ValuativeRel X := LocalField.Laurent.valuativeRel k
  -- A prime different from the characteristic of `k`: `2` or `3`.
  obtain ⟨ℓ, hℓp, hℓ⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : k) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : k) = 0
    · refine ⟨3, Nat.prime_three, ?_⟩
      have h3 : ((3 : ℕ) : k) = ((2 : ℕ) : k) + 1 := by push_cast; ring
      rw [h3, h2, zero_add]
      exact one_ne_zero
    · exact ⟨2, Nat.prime_two, h2⟩
  have : Fact ℓ.Prime := ⟨hℓp⟩
  -- A ring embedding of the ℓ-adic coefficients into `ℂ`.
  let ι : PadicAlgCl ℓ →+* ℂ := (GaloisRepresentation.padicAlgClComplexEquiv ℓ).toRingHom
  -- The residue field of `X` is `k`, so `ℓ` is nonzero there.
  have hres : ((ℓ : ℕ) : 𝓀[X]) ≠ 0 := by
    intro h
    apply hℓ
    have h' := congrArg (LocalField.Laurent.residueEquiv k) h
    rwa [map_natCast, map_zero] at h'
  obtain ⟨Φ, hΦ⟩ := hlaumon k ℓ hℓ ι d s hs
  obtain ⟨e, -, he⟩ := hcomp X Ω ℓ hres ι
  rw [← he d s f, ← he (d + s) s f, e.injective.encard_image, e.injective.encard_image]
  exact ladicRefinedStratum_encard_eq_of_twistEquiv X Ω ℓ ι Φ hΦ f

end Langlands.Henniart
