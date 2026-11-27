import Langlands.Representation.Conductor.SphericalLFactorGenerationAssembly
import Langlands.Representation.Conductor.PadicSphericalLFactorGenerationStatement
import Langlands.Representation.Conductor.OrderedUnramifiedGenerationFromPremises

/-!
# The spherical L-factor generation facts, one field at a time

`SphericalLFactorGenerationStatement` and its p-adic form are the field-by-field
proposition `SphericalLFactorGenerationAt F` for every nonarchimedean local field, and for
the canonical structures of every p-adic field. Over one field `F`, Jacquet's Lemma 3 at
`F` gives `SphericalLFactorGenerationAt F`, by the published reduction of
`SphericalLFactorGenerationReduction` and the published proofs of its other inputs, which
hold over every field.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV

/-- `SphericalLFactorGenerationStatement` for one nonarchimedean local field `F`, given by
its instances. -/
def SphericalLFactorGenerationAt (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Prop :=
  ∀ (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
    IsGeneric ψ (n + 1) π →
    ∀ ℓ : glFunctionals ψ (n + 1) π, ℓ.val ≠ 0 →
    ∃ P : ℂ[X], IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P ∧
      (∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
      (∀ (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ),
        ∃ (a : ℝ) (N : ℤ) (Q : ℂ[X]), ∀ s : ℂ, a < s.re →
          corankOneIntegral ψ abv μ w.val
              (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
          spectralPoint q s ^ N * Q.eval (spectralPoint q s)) ∧
      ∀ x : Fin (n + 1) → ℂˣ,
        ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ) (a : ℝ),
          ∀ s : ℂ, a < s.re →
            (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
                (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
              (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1

theorem sphericalLFactorGenerationStatement_iff :
    SphericalLFactorGenerationStatement.{uF, uV} ↔
      ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F], SphericalLFactorGenerationAt.{uF, uV} F :=
  Iff.rfl

theorem padicSphericalLFactorGenerationStatement_iff :
    PadicSphericalLFactorGenerationStatement.{uF, uV} ↔
      ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
        letI := K.canonicalTopologicalData.topology
        letI := K.canonicalTopologicalData.valuativeRel
        letI := K.canonicalTopologicalData.localField
        SphericalLFactorGenerationAt.{uF, uV} K.Carrier :=
  Iff.rfl

section Field

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V}
  {ℓ : glFunctionals ψ (n + 1) π}

omit [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)] in
/-- Clause 3 of the target for norm-ordered parameters, from Jacquet's Lemma 3 at the
field of `π`. -/
theorem generation_of_orderedAt (h : IsJacquetNormalization q ψ abv ϖ μ) {P : ℂ[X]}
    (x : Fin (n + 1) → ℂˣ) (hx : Monotone (fun i => ‖(x i : ℂ)‖))
    (hgen : ∀ ℓ' : glInverseFunctionals ψ n
        (principalSeries h.uniformizer n h.residueCardinality x), ℓ'.val ≠ 0 →
      ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule)
        (W' : Fin k → (coefficientModel
          (principalSeries h.uniformizer n h.residueCardinality x) ℓ').toSubmodule) (a : ℝ),
        ∀ s : ℂ, a < s.re →
          (∑ j, corankOneIntegral ψ abv μ (W j).val (W' j).val s) *
            (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1)
    (hconv : ∀ (w : (coefficientModel π ℓ).toSubmodule), ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) :
    ∃ (k : ℕ) (W : Fin k → (coefficientModel π ℓ).toSubmodule) (e : Fin k → ℤ) (a : ℝ),
      ∀ s : ℂ, a < s.re →
        (∑ j, spectralPoint q s ^ e j * corankOneIntegral ψ abv μ (W j).val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) *
          (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) = 1 := by
  obtain ⟨ℓ', hℓ'0, -, hsph⟩ :=
    orderedUnramifiedWhittakerRealization F ϖ h.uniformizer n q h.residueCardinality x hx ψ
      h.conductor
  have hcyc' := orderedUnramifiedSphericalCyclicity F ϖ h.uniformizer n q
    h.residueCardinality x hx
  obtain ⟨k, W, W', a, hsum⟩ := hgen ℓ' hℓ'0
  have hspan := IsSphericalIntegralSpan.finset_sum (q := q) (X₀ :=
      inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) Finset.univ
    (R := fun j s => corankOneIntegral ψ abv μ (W j).val (W' j).val s)
    fun j _ => isSphericalIntegralSpan_of_model h x hconv ℓ' hcyc' hsph (W j) (W' j)
  obtain ⟨k₂, W₂, e₂, a₂, h₂⟩ := hspan
  refine ⟨k₂, W₂, e₂, max a a₂, fun s hs => ?_⟩
  rw [← h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)]
  exact hsum s (lt_of_le_of_lt (le_max_left _ _) hs)

end Field

/-- The spherical L-factor generation facts over one field `F`, from Jacquet's Lemma 3 at
`F`. -/
theorem sphericalLFactorGenerationAt_of_generationAt (F : Type uF) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hgen : OrderedUnramifiedCorankOneGenerationAt.{uF, uV} F) :
    SphericalLFactorGenerationAt.{uF, uV} F := by
  intro n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ hℓ
  obtain ⟨P, hP, hc⟩ := sphericalCorankOneConvergence F n q ψ abv ϖ μ h π hπ ℓ hℓ
  refine ⟨P, hP, hc, fun w x => ?_, fun x => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_monotone_norm x
    obtain ⟨a, N, Q, hQ⟩ := laurent_of_ordered h hπ hℓ hP unramifiedCorankOneLaurent
      orderedUnramifiedWhittakerRealization (x ∘ σ) hσ w (by
        rw [inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ]
        exact hc w x)
    refine ⟨a, N, Q, fun s hs => ?_⟩
    rw [← inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ,
      ← prod_comp_perm P x σ]
    exact hQ s hs
  · obtain ⟨σ, hσ⟩ := exists_perm_monotone_norm x
    obtain ⟨k, W, e, a, hW⟩ := generation_of_orderedAt h (x ∘ σ) hσ
      (hgen n q ψ abv ϖ μ h π hπ ℓ hℓ P hP (x ∘ σ) hσ)
      (fun w => by
        rw [inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ]
        exact hc w x)
    refine ⟨k, W, e, a, fun s hs => ?_⟩
    rw [← inverseSphericalWhittaker_comp_perm h.conductor.1 h.uniformizer q x σ,
      ← prod_comp_perm P x σ]
    exact hW s hs

/-- The spherical L-factor generation facts over every nonarchimedean local field, from
Jacquet's Lemma 3 at every field. -/
theorem sphericalLFactorGeneration_of_generationAt
    (hgen : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F], OrderedUnramifiedCorankOneGenerationAt.{uF, uV} F) :
    SphericalLFactorGenerationStatement.{uF, uV} :=
  fun F _ _ _ _ => sphericalLFactorGenerationAt_of_generationAt F (hgen F)

end Langlands.Conductor
