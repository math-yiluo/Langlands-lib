import Langlands.Representation.Compact.SchurPhaseSupport

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Langlands.Renard.CompactRepresentation

open Langlands.HarishChandraSchwartz Langlands.Plancherel

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- The unitary central character of a twist fixes the modulus of its twist
on the center, once the original central character is specified. -/
theorem twist_norm_on_center (π : SmoothRep.{0, u, v} ℂ G) (hi : π.IsIrreducible)
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ (z : Subgroup.center G) (x : π), π.representation z x = (χ z : ℂ) • x)
    (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
    (c : UnitaryCentralCharacter (π.twist ω hω).representation) (z : Subgroup.center G) :
    ‖(ω z : ℂ)‖ * ‖(χ z : ℂ)‖ = 1 := by
  have hnt : Nontrivial π := by
    have := hi
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  have he : (ω z : ℂ) * (χ z : ℂ) = (c.character z : ℂ) := by
    apply smul_left_injective ℂ hx
    change ((ω z : ℂ) * (χ z : ℂ)) • x = (c.character z : ℂ) • x
    rw [mul_smul, ← hχ]
    exact c.acts z x
  have hn := congrArg norm he
  simpa only [norm_mul, c.norm_eq_one] using hn

section Mixed

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hcof in
/-- Independent essentially square-integrable twists still give integrable
mixed Schur products when the original central characters agree. -/
theorem integrable_essentiallySquareIntegrable_mixed
    (π₁ π₂ : SmoothRep.{0, u, v} ℂ G) (hi₁ : π₁.IsIrreducible)
    (ω₁ ω₂ : G →* ℂˣ) (hω₁ : IsOpen (ω₁.ker : Set G)) (hω₂ : IsOpen (ω₂.ker : Set G))
    (hsq₁ : IsSquareIntegrableModCenter (π₁.twist ω₁ hω₁).representation μ)
    (hsq₂ : IsSquareIntegrableModCenter (π₂.twist ω₂ hω₂).representation μ)
    (b₁ : InvariantPositiveForm (π₁.twist ω₁ hω₁).representation)
    (b₂ : InvariantPositiveForm (π₂.twist ω₂ hω₂).representation)
    (χ : Subgroup.center G →* ℂˣ)
    (h₁ : ∀ (z : Subgroup.center G) (x : π₁), π₁.representation z x = (χ z : ℂ) • x)
    (h₂ : ∀ (z : Subgroup.center G) (x : π₂), π₂.representation z x = (χ z : ℂ) • x)
    (hηZ : ∀ z : Subgroup.center G, ‖((ω₂ / ω₁) z : ℂ)‖ = 1)
    (x₁ : π₁) (ℓ₁ : SmoothDual π₁.representation)
    (x₂ : π₂) (ℓ₂ : SmoothDual π₂.representation) :
    Integrable (orthogonalityIntegrand (Subgroup.center G) h₁ h₂ x₁ ℓ₁.val x₂ ℓ₂.val) μ := by
  let ρ₁ := (π₁.twist ω₁ hω₁).representation
  let ρ₂ := (π₂.twist ω₂ hω₂).representation
  let ℓ₁t : SmoothDual ρ₁ :=
    (smoothContragredientTwistEquiv ω₁ π₁.representation hω₁).symm ℓ₁
  let ℓ₂t : SmoothDual ρ₂ :=
    (smoothContragredientTwistEquiv ω₂ π₂.representation hω₂).symm ℓ₂
  let η := ω₂ / ω₁
  have hη : IsOpen (η.ker : Set G) := by
    apply Subgroup.isOpen_mono (H₁ := ω₁.ker ⊓ ω₂.ker) ?_ (hω₁.inter hω₂)
    intro g hg
    change η g = 1
    have he₁ : ω₁ g = 1 := hg.1
    have he₂ : ω₂ g = 1 := hg.2
    simp [η, he₁, he₂]
  have hit : ρ₁.IsIrreducible := (π₁.isIrreducible_twist_iff ω₁ hω₁).mpr hi₁
  obtain ⟨C, hC, hbound⟩ := character_norm_bounded_on_coefficient_support μ hcof
    hsq₁ hit b₁ η hη hηZ x₁ ℓ₁t
  obtain ⟨z, hz⟩ := b₂.toSmoothDual_surjective hcof hsq₂.1 ℓ₂t
  obtain ⟨c₁, hc₁⟩ := hsq₁.2
  obtain ⟨c₂, hc₂⟩ := hsq₂.2
  let m := b₂.toSmoothDual hsq₂.1.1 x₂
  have hb (g : G) : ℓ₂t.val (ρ₂ g⁻¹ x₂) = conj (m.val (ρ₂ g z)) := by
    rw [← hz]
    change b₂.inner z (ρ₂ g⁻¹ x₂) = conj (b₂.inner x₂ (ρ₂ g z))
    rw [← b₂.invariant g z (ρ₂ g⁻¹ x₂), Representation.self_inv_apply]
    exact (b₂.conj_inner_symm _ _).symm
  have hint := ((hc₁ ℓ₁t x₁).integrable_mul (hc₂ m z)).const_mul C
  refine hint.mono'
    (continuous_orthogonalityIntegrand (Subgroup.center G) h₁ h₂ π₁.isSmooth π₂.isSmooth
      x₁ ℓ₁.val x₂ ℓ₂.val).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have he :
      ℓ₁.val (π₁.representation g x₁) * ℓ₂.val (π₂.representation g⁻¹ x₂) =
        (η g : ℂ) * (ℓ₁t.val (ρ₁ g x₁) * ℓ₂t.val (ρ₂ g⁻¹ x₂)) := by
    dsimp only [η, MonoidHom.div_apply]
    rw [Units.val_div_eq_div_val]
    change _ = ((ω₂ g : ℂ) / (ω₁ g : ℂ)) *
      (ℓ₁.val ((ω₁ g : ℂ) • π₁.representation g x₁) *
        ℓ₂.val ((ω₂ g⁻¹ : ℂ) • π₂.representation g⁻¹ x₂))
    simp only [map_smul, smul_eq_mul, map_inv, Units.val_inv_eq_inv_val]
    field_simp
  change ‖ℓ₁.val (π₁.representation g x₁) * ℓ₂.val (π₂.representation g⁻¹ x₂)‖ ≤
    C * (c₁.coefficientNorm ℓ₁t x₁ (QuotientGroup.mk g) *
      c₂.coefficientNorm m z (QuotientGroup.mk g))
  rw [he, norm_mul, norm_mul, hb, Complex.norm_conj]
  change ‖(η g : ℂ)‖ * (‖ℓ₁t.val (ρ₁ g x₁)‖ * ‖m.val (ρ₂ g z)‖) ≤
    C * (‖ℓ₁t.val (ρ₁ g x₁)‖ * ‖m.val (ρ₂ g z)‖)
  by_cases hf : ℓ₁t.val (ρ₁ g x₁) = 0
  · simp [hf]
  · exact mul_le_mul_of_nonneg_right (hbound g hf) (by positivity)

end Mixed

/-- Renard IV.3.3, with the exact published hypotheses, both integrability
conclusions, and the positive real formal degree. -/
theorem schurOrthogonality : SchurOrthogonalityStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _
  have hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 K K.mem_nhds_one
  constructor
  · intro π hi ⟨ω, hω, c, hc⟩
    exact schurOrthogonality_self μ π hi ω hω c hc
  · intro π₁ π₂ hi₁ hi₂ ⟨ω₁, hω₁, c₁, hc₁⟩ ⟨ω₂, hω₂, c₂, hc₂⟩ hne ⟨χ, hχ⟩
    have h₁ : ∀ (z : Subgroup.center G) (x : π₁),
        π₁.representation z x = (χ z : ℂ) • x := fun z x => (hχ z x 0).1
    have h₂ : ∀ (z : Subgroup.center G) (x : π₂),
        π₂.representation z x = (χ z : ℂ) • x := fun z x => (hχ z 0 x).2
    have hadm₁ := essentiallySquareIntegrableAdmissible G μ π₁ hi₁ ω₁ hω₁ ⟨c₁, hc₁⟩
    have hadm₂ := essentiallySquareIntegrableAdmissible G μ π₂ hi₂ ω₂ hω₂ ⟨c₂, hc₂⟩
    have hsq₁ : IsSquareIntegrableModCenter (π₁.twist ω₁ hω₁).representation μ :=
      ⟨(π₁.isAdmissible_twist_iff ω₁ hω₁).mpr hadm₁, c₁, hc₁⟩
    have hsq₂ : IsSquareIntegrableModCenter (π₂.twist ω₂ hω₂).representation μ :=
      ⟨(π₂.isAdmissible_twist_iff ω₂ hω₂).mpr hadm₂, c₂, hc₂⟩
    obtain ⟨b₁⟩ := (squareIntegrableUnitarySemisimple G μ (π₁.twist ω₁ hω₁) hsq₁).1
    obtain ⟨b₂⟩ := (squareIntegrableUnitarySemisimple G μ (π₂.twist ω₂ hω₂) hsq₂).1
    have hηZ (z : Subgroup.center G) : ‖((ω₂ / ω₁) z : ℂ)‖ = 1 := by
      have he₁ := twist_norm_on_center π₁ hi₁ χ h₁ ω₁ hω₁ c₁ z
      have he₂ := twist_norm_on_center π₂ hi₂ χ h₂ ω₂ hω₂ c₂ z
      have he : ‖(ω₂ z : ℂ)‖ = ‖(ω₁ z : ℂ)‖ :=
        mul_right_cancel₀ (norm_ne_zero_iff.mpr (Units.ne_zero (χ z))) (he₂.trans he₁.symm)
      simp only [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, he,
        div_self (norm_ne_zero_iff.mpr (Units.ne_zero (ω₁ z)))]
    have hint := integrable_essentiallySquareIntegrable_mixed μ hcof π₁ π₂ hi₁
      ω₁ ω₂ hω₁ hω₂ hsq₁ hsq₂ b₁ b₂ χ h₁ h₂ hηZ
    intro x₁ x₂ ℓ₁ ℓ₂ F hF
    have he : F = orthogonalityIntegrand (Subgroup.center G) h₁ h₂ x₁ ℓ₁.val x₂ ℓ₂.val := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact hF g
    refine ⟨he ▸ hint x₁ ℓ₁ x₂ ℓ₂, ?_⟩
    rw [he]
    change orthogonalityIntegral (Subgroup.center G) μ h₁ h₂ x₁ ℓ₁ x₂ ℓ₂ = 0
    obtain ⟨T, hT⟩ := exists_leftSchurIntertwiner_rightInvariant (Subgroup.center G)
      μ h₁ h₂ hcof hint hadm₁ hadm₂ ℓ₁ x₂
    have : IsEmpty (π₁.representation.Equiv π₂.representation) :=
      ⟨fun e => hne.false (SmoothRep.mkIso e)⟩
    have := hi₁
    have := hi₂
    have hT0 : T = 0 := Subsingleton.elim _ _
    rw [← hT, hT0]
    exact map_zero _

end Langlands.Renard.CompactRepresentation
