import Langlands.Representation.RankinSelberg.FieldTransport.Integrals
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.RankinSelberg.PairLFactor

/-!
# JPSS L-polynomials and epsilon factors along an isomorphism of topological fields

Let `σ : F ≃+* E` be a field isomorphism that is a homeomorphism and let
`T = fieldEquiv n σ` act entrywise on general linear groups. For
representations `π`, `τ` of general linear groups over `E`, this file compares
the JPSS data of `(π, τ)` over `E` with the data of the pulled-back pair
`(π ∘ T, τ ∘ T)` over `F`.

The additive characters, absolute values, scalar Haar measures and quotient
measures on the two sides are related by `σ` (the `E`-side quotient measure is
the pushforward along the quotient homeomorphism induced by `T`). Under these
hypotheses the Whittaker sets, zeta-value sets and rational-value sets
correspond, so the L-polynomial relation `IsPairLPolynomial` holds over `E`
exactly when it holds over `F`. For nonarchimedean local fields the epsilon
relation `IsPairEpsilonFactor` transfers as well, provided the normalized Haar
measures of `GL_(n+1)` and of its upper unipotent subgroup over `E` are the
pushforwards of those over `F`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Polynomial

universe uF uE uV uW

namespace Langlands.RankinSelberg.FieldTransport

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Models

variable {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  (hψ : ∀ x, ψ' (σ x) = ψ x) (n : ℕ)

/-- Whittaker functions correspond by `W ↦ W ∘ T⁻¹`. -/
def whittakerEquiv : WhittakerFunctions ψ n ≃ₗ[ℂ] WhittakerFunctions ψ' n :=
  equivariantEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (standardCharacter_unipotentEquiv σ hσ hσs hψ n)

/-- Inverse-character Whittaker functions correspond by `W ↦ W ∘ T⁻¹`. -/
def inverseWhittakerEquiv :
    InverseWhittakerFunctions ψ n ≃ₗ[ℂ] InverseWhittakerFunctions ψ' n :=
  equivariantEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (inverseStandardCharacter_unipotentEquiv σ hσ hσs hψ n)

/-- The standard Whittaker functionals of the pulled-back representation are
those of the original representation. -/
def glFunctionalEquiv (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V) :
    glFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ≃
      glFunctionals ψ' n π :=
  functionalTransportEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (standardCharacter_unipotentEquiv σ hσ hσs hψ n) π

/-- The inverse-character version of `glFunctionalEquiv`. -/
def glInverseFunctionalEquiv (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V) :
    glInverseFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ≃
      glInverseFunctionals ψ' n π :=
  functionalTransportEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (inverseStandardCharacter_unipotentEquiv σ hσ hσs hψ n) π

/-- Coefficient models of a pulled-back standard functional correspond by
`f ↦ f ∘ T⁻¹`. -/
def glModelEquiv (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (ℓ : glFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)) :
    (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule ≃
      (coefficientModel π (glFunctionalEquiv σ hσ hσs hψ n π ℓ)).toSubmodule :=
  compModelEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (standardCharacter_unipotentEquiv σ hσ hσs hψ n) π ℓ

/-- The inverse-character version of `glModelEquiv`. -/
def glInverseModelEquiv (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (ℓ : glInverseFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)) :
    (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule ≃
      (coefficientModel π (glInverseFunctionalEquiv σ hσ hσs hψ n π ℓ)).toSubmodule :=
  compModelEquiv (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    (inverseStandardCharacter_unipotentEquiv σ hσ hσs hψ n) π ℓ

variable {n}

theorem whittakerEquiv_apply_fieldEquiv (f : WhittakerFunctions ψ n)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (whittakerEquiv σ hσ hσs hψ n f).val (fieldEquiv (n + 1) σ hσ hσs g) = f.val g := by
  change f.val ((fieldEquiv (n + 1) σ hσ hσs).toMulEquiv.symm
    ((fieldEquiv (n + 1) σ hσ hσs).toMulEquiv g)) = f.val g
  rw [MulEquiv.symm_apply_apply]

theorem inverseWhittakerEquiv_apply_fieldEquiv (f : InverseWhittakerFunctions ψ n)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (inverseWhittakerEquiv σ hσ hσs hψ n f).val (fieldEquiv (n + 1) σ hσ hσs g) =
      f.val g := by
  change f.val ((fieldEquiv (n + 1) σ hσ hσs).toMulEquiv.symm
    ((fieldEquiv (n + 1) σ hσ hσs).toMulEquiv g)) = f.val g
  rw [MulEquiv.symm_apply_apply]

theorem glModelEquiv_apply_fieldEquiv
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (ℓ : glFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))
    (f : (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (glModelEquiv σ hσ hσs hψ n π ℓ f).val.val (fieldEquiv (n + 1) σ hσ hσs g) =
      f.val.val g :=
  compModelEquiv_apply_apply _ _ _ π ℓ f g

theorem glInverseModelEquiv_apply_fieldEquiv
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (ℓ : glInverseFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))
    (f : (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (glInverseModelEquiv σ hσ hσs hψ n π ℓ f).val.val (fieldEquiv (n + 1) σ hσ hσs g) =
      f.val.val g :=
  compModelEquiv_apply_apply _ _ _ π ℓ f g

/-- Whittaker sets correspond under `whittakerEquiv`. -/
theorem whittakerEquiv_mem_whittakerSet_iff
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V) (f : WhittakerFunctions ψ n) :
    whittakerEquiv σ hσ hσs hψ n f ∈ whittakerSet ψ' n π ↔
      f ∈ whittakerSet ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) := by
  constructor
  · rintro ⟨ℓ₂, h⟩
    exact ⟨(glFunctionalEquiv σ hσ hσs hψ n π).symm ℓ₂,
      (mem_coefficientModel_comp_iff (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
        (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
        (standardCharacter_unipotentEquiv σ hσ hσs hψ n) π _ f).2 h⟩
  · rintro ⟨ℓ, h⟩
    exact ⟨glFunctionalEquiv σ hσ hσs hψ n π ℓ,
      (mem_coefficientModel_comp_iff (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
        (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
        (standardCharacter_unipotentEquiv σ hσ hσs hψ n) π ℓ f).1 h⟩

/-- Inverse Whittaker sets correspond under `inverseWhittakerEquiv`. -/
theorem inverseWhittakerEquiv_mem_inverseWhittakerSet_iff
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (f : InverseWhittakerFunctions ψ n) :
    inverseWhittakerEquiv σ hσ hσs hψ n f ∈ inverseWhittakerSet ψ' n π ↔
      f ∈ inverseWhittakerSet ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) := by
  constructor
  · rintro ⟨ℓ₂, h⟩
    exact ⟨(glInverseFunctionalEquiv σ hσ hσs hψ n π).symm ℓ₂,
      (mem_coefficientModel_comp_iff (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
        (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
        (inverseStandardCharacter_unipotentEquiv σ hσ hσs hψ n) π _ f).2 h⟩
  · rintro ⟨ℓ, h⟩
    exact ⟨glInverseFunctionalEquiv σ hσ hσs hψ n π ℓ,
      (mem_coefficientModel_comp_iff (fieldEquiv (n + 1) σ hσ hσs).toMulEquiv
        (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
        (inverseStandardCharacter_unipotentEquiv σ hσ hσs hψ n) π ℓ f).1 h⟩

/-- The scalar action of `-1` on a coefficient model is the same for the
pulled-back representation. -/
theorem hasModelMinusOneScalar_glInverseFunctionalEquiv_iff
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W)
    (ℓ' : glInverseFunctionals ψ n (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))
    (ζ : ℂˣ) :
    HasModelMinusOneScalar τ (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ') ζ ↔
      HasModelMinusOneScalar (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ' ζ := by
  constructor
  · intro h f g
    have h1 := h (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f) (fieldEquiv (n + 1) σ hσ hσs g)
    rw [← fieldEquiv_neg_one (n := n + 1) σ hσ hσs, ← map_mul,
      glInverseModelEquiv_apply_fieldEquiv, glInverseModelEquiv_apply_fieldEquiv] at h1
    exact h1
  · intro h f₂ g₂
    obtain ⟨f, rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂
    obtain ⟨g, rfl⟩ := (fieldEquiv (n + 1) σ hσ hσs).surjective g₂
    rw [← fieldEquiv_neg_one (n := n + 1) σ hσ hσs, ← map_mul,
      glInverseModelEquiv_apply_fieldEquiv, glInverseModelEquiv_apply_fieldEquiv]
    exact h f g

end Models

section ZetaValues

variable [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)
  {abv : AbsoluteValue F ℝ} {abv' : AbsoluteValue E ℝ} (habv : ∀ x, abv' (σ x) = abv x)
  (q : ℕ) {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)]

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include habv in
/-- Equal-rank rational value sets of corresponding function sets agree. -/
theorem equalRankValuesOf_map (μ : Measure (LeftUnipotentQuotient n F))
    {S : Set (WhittakerFunctions ψ n)} {S' : Set (InverseWhittakerFunctions ψ n)}
    {S₂ : Set (WhittakerFunctions ψ' n)} {S₂' : Set (InverseWhittakerFunctions ψ' n)}
    (hS : ∀ f, whittakerEquiv σ hσ hσs hψ n f ∈ S₂ ↔ f ∈ S)
    (hS' : ∀ f, inverseWhittakerEquiv σ hσ hσs hψ n f ∈ S₂' ↔ f ∈ S') :
    equalRankValuesOf q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) S₂ S₂' =
      equalRankValuesOf q ψ abv μ S S' := by
  have key : ∀ (f : WhittakerFunctions ψ n) (f' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      (∀ s, EqualRankConverges ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (whittakerEquiv σ hσ hσs hψ n f) (inverseWhittakerEquiv σ hσ hσs hψ n f')
        (rowTestEquiv σ hσ hσs (n + 1) Φ) s ↔ EqualRankConverges ψ abv μ f f' Φ s) ∧
      equalRankIntegral ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (whittakerEquiv σ hσ hσs hψ n f) (inverseWhittakerEquiv σ hσ hσs hψ n f')
        (rowTestEquiv σ hσ hσs (n + 1) Φ) = equalRankIntegral ψ abv μ f f' Φ := by
    intro f f' Φ
    have hW := whittakerEquiv_apply_fieldEquiv σ hσ hσs hψ f
    have hW' := inverseWhittakerEquiv_apply_fieldEquiv σ hσ hσs hψ f'
    have hΦ := rowTestEquiv_apply_map σ hσ hσs Φ
    exact ⟨fun s => equalRankConverges_map_iff σ hσ hσs habv μ hW hW' hΦ s,
      funext fun s => equalRankIntegral_map σ hσ hσs habv μ hW hW' hΦ s⟩
  ext R
  constructor
  · rintro ⟨W₂, hW₂, W₂', hW₂', Φ₂, ⟨a, hconv⟩, hR⟩
    obtain ⟨f, rfl⟩ := (whittakerEquiv σ hσ hσs hψ n).surjective W₂
    obtain ⟨f', rfl⟩ := (inverseWhittakerEquiv σ hσ hσs hψ n).surjective W₂'
    obtain ⟨Φ, rfl⟩ := (rowTestEquiv σ hσ hσs (n + 1)).surjective Φ₂
    obtain ⟨hc, hi⟩ := key f f' Φ
    refine ⟨f, (hS f).1 hW₂, f', (hS' f').1 hW₂', Φ,
      ⟨a, fun s hs => (hc s).1 (hconv s hs)⟩, ?_⟩
    rwa [hi] at hR
  · rintro ⟨f, hf, f', hf', Φ, ⟨a, hconv⟩, hR⟩
    obtain ⟨hc, hi⟩ := key f f' Φ
    refine ⟨whittakerEquiv σ hσ hσs hψ n f, (hS f).2 hf,
      inverseWhittakerEquiv σ hσ hσs hψ n f', (hS' f').2 hf',
      rowTestEquiv σ hσ hσs (n + 1) Φ, ⟨a, fun s hs => (hc s).2 (hconv s hs)⟩, ?_⟩
    rwa [hi]

include habv in
/-- Unequal-rank rational value sets of corresponding function sets agree. -/
theorem unequalRankValuesOf_map (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν.measure]
    [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ) (j k : ℕ)
    {S : Set (WhittakerFunctions ψ (n + (j + k + 1)))}
    {S' : Set (InverseWhittakerFunctions ψ n)}
    {S₂ : Set (WhittakerFunctions ψ' (n + (j + k + 1)))}
    {S₂' : Set (InverseWhittakerFunctions ψ' n)}
    (hS : ∀ f, whittakerEquiv σ hσ hσs hψ (n + (j + k + 1)) f ∈ S₂ ↔ f ∈ S)
    (hS' : ∀ f, inverseWhittakerEquiv σ hσ hσs hψ n f ∈ S₂' ↔ f ∈ S') :
    unequalRankValuesOf q ψ' abv' j k (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) S₂ S₂' =
      unequalRankValuesOf q ψ abv j k μ (rectangularMeasure ν j (n + 1)) S S' := by
  have key : ∀ (f : WhittakerFunctions ψ (n + (j + k + 1)))
      (f' : InverseWhittakerFunctions ψ n),
      (∀ s, UnequalRankConverges ψ' abv' j k (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) (whittakerEquiv σ hσ hσs hψ _ f)
        (inverseWhittakerEquiv σ hσ hσs hψ n f') s ↔
        UnequalRankConverges ψ abv j k μ (rectangularMeasure ν j (n + 1)) f f' s) ∧
      unequalRankIntegral ψ' abv' j k (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) (whittakerEquiv σ hσ hσs hψ _ f)
        (inverseWhittakerEquiv σ hσ hσs hψ n f') =
        unequalRankIntegral ψ abv j k μ (rectangularMeasure ν j (n + 1)) f f' := by
    intro f f'
    have hW := whittakerEquiv_apply_fieldEquiv σ hσ hσs hψ f
    have hW' := inverseWhittakerEquiv_apply_fieldEquiv σ hσ hσs hψ f'
    exact ⟨fun s => unequalRankConverges_map_iff σ hσ hσs habv μ ν ν' hν j k hW hW' s,
      funext fun s => unequalRankIntegral_map σ hσ hσs habv μ ν ν' hν j k hW hW' s⟩
  ext R
  constructor
  · rintro ⟨W₂, hW₂, W₂', hW₂', ⟨a, hconv⟩, hR⟩
    obtain ⟨f, rfl⟩ := (whittakerEquiv σ hσ hσs hψ _).surjective W₂
    obtain ⟨f', rfl⟩ := (inverseWhittakerEquiv σ hσ hσs hψ n).surjective W₂'
    obtain ⟨hc, hi⟩ := key f f'
    refine ⟨f, (hS f).1 hW₂, f', (hS' f').1 hW₂', ⟨a, fun s hs => (hc s).1 (hconv s hs)⟩, ?_⟩
    rwa [hi] at hR
  · rintro ⟨f, hf, f', hf', ⟨a, hconv⟩, hR⟩
    obtain ⟨hc, hi⟩ := key f f'
    refine ⟨whittakerEquiv σ hσ hσs hψ _ f, (hS f).2 hf,
      inverseWhittakerEquiv σ hσ hσs hψ n f', (hS' f').2 hf',
      ⟨a, fun s hs => (hc s).2 (hconv s hs)⟩, ?_⟩
    rwa [hi]

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include hψ habv in
/-- The equal-rank zeta values of `(π, τ)` over `E` are those of the pulled-back
pair over `F`. -/
theorem equalRankZetaValues_map (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) :
    equalRankZetaValues q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) π τ =
      equalRankZetaValues q ψ abv μ (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) :=
  equalRankValuesOf_map σ hσ hσs hψ habv q μ
    (whittakerEquiv_mem_whittakerSet_iff σ hσ hσs hψ π)
    (inverseWhittakerEquiv_mem_inverseWhittakerSet_iff σ hσ hσs hψ τ)

include hψ habv in
/-- The unequal-rank zeta values at a fixed large rank correspond. -/
theorem unequalRankZetaValuesAt_map {r : ℕ} (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν.measure]
    [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ) (j k : ℕ)
    (hr : r = n + (j + k + 1))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) :
    unequalRankZetaValuesAt j k hr q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) π τ =
      unequalRankZetaValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) := by
  subst hr
  exact unequalRankValuesOf_map σ hσ hσs hψ habv q μ ν ν' hν j k
    (whittakerEquiv_mem_whittakerSet_iff σ hσ hσs hψ π)
    (inverseWhittakerEquiv_mem_inverseWhittakerSet_iff σ hσ hσs hψ τ)

include hψ habv in
/-- **L-polynomials along a field isomorphism.** `P` is the JPSS L-polynomial of
`(π, τ)` over `E` exactly when it is the L-polynomial of the pulled-back pair
over `F`, for corresponding characters, absolute values and measures. -/
theorem isPairLPolynomial_comp_iff {r : ℕ} (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν.measure]
    [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (P : ℂ[X]) :
    IsPairLPolynomial q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) ν' π τ P ↔
      IsPairLPolynomial q ψ abv μ ν (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) P := by
  rcases lt_trichotomy n r with h | rfl | h
  · rw [isPairLPolynomial_of_lt h, isPairLPolynomial_of_lt h]
    refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_
    rw [unequalRankZetaValuesAt_map σ hσ hσs hψ habv q μ ν ν' hν j k hr]
  · rw [isPairLPolynomial_self, isPairLPolynomial_self, IsEqualRankLPolynomial,
      IsEqualRankLPolynomial, equalRankZetaValues_map σ hσ hσs hψ habv q μ]
  · exact iff_of_false (not_isPairLPolynomial_of_lt h) (not_isPairLPolynomial_of_lt h)

end ZetaValues

section EpsilonEquations

variable [IsTopologicalRing F] [IsTopologicalRing E]
  [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)
  {abv : AbsoluteValue F ℝ} {abv' : AbsoluteValue E ℝ} (habv : ∀ x, abv' (σ x) = abv x)
  (q : ℕ) {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)]
  (μ : Measure (LeftUnipotentQuotient n F))

section EqualRank

variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
  (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W)
  (ℓ : glFunctionals ψ n (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))
  (ℓ' : glInverseFunctionals ψ n (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))

omit [IsTopologicalRing F] [IsTopologicalRing E]
  [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include habv in
theorem equalRankModelIntegral_map
    (f : (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (f' : (coefficientModel (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankModelIntegral ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) π τ
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        (glModelEquiv σ hσ hσs hψ n π ℓ f) (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f')
        (rowTestEquiv σ hσ hσs (n + 1) Φ) =
      equalRankModelIntegral ψ abv μ (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' f f' Φ :=
  funext fun s => equalRankIntegral_map σ hσ hσs habv μ
    (glModelEquiv_apply_fieldEquiv σ hσ hσs hψ π ℓ f)
    (glInverseModelEquiv_apply_fieldEquiv σ hσ hσs hψ τ ℓ' f')
    (rowTestEquiv_apply_map σ hσ hσs Φ) s

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include habv in
theorem dualEqualRankModelIntegral_map
    (f : (coefficientModel (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (f' : (coefficientModel (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    dualEqualRankModelIntegral ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) π τ
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        (glModelEquiv σ hσ hσs hψ n π ℓ f) (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f')
        (rowTestEquiv σ hσ hσs (n + 1) Φ) =
      dualEqualRankModelIntegral ψ abv μ (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' f f' Φ :=
  funext fun s => equalRankIntegral_map σ hσ hσs habv μ
    (firstDualFunction_fieldEquiv σ hσ hσs (glModelEquiv_apply_fieldEquiv σ hσ hσs hψ π ℓ f))
    (secondDualFunction_fieldEquiv σ hσ hσs
      (glInverseModelEquiv_apply_fieldEquiv σ hσ hσs hψ τ ℓ' f'))
    (rowTestEquiv_apply_map σ hσ hσs Φ) s

omit [IsTopologicalRing F] [IsTopologicalRing E]
  [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include habv in
theorem equalRankRationalValues_map :
    equalRankRationalValues q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) π τ
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ') =
      equalRankRationalValues q ψ abv μ (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' := by
  ext R
  constructor
  · rintro ⟨f₂, f₂', Φ₂, hR⟩
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ n π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    obtain ⟨Φ, rfl⟩ := (rowTestEquiv σ hσ hσs (n + 1)).surjective Φ₂
    refine ⟨f, f', Φ, ?_⟩
    rwa [equalRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ] at hR
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨glModelEquiv σ hσ hσs hψ n π ℓ f, glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f',
      rowTestEquiv σ hσ hσs (n + 1) Φ, ?_⟩
    rwa [equalRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ]

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include habv in
theorem dualEqualRankRationalValues_map :
    dualEqualRankRationalValues q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) π τ
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ') =
      dualEqualRankRationalValues q ψ abv μ (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' := by
  ext R
  constructor
  · rintro ⟨f₂, f₂', Φ₂, hR⟩
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ n π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    obtain ⟨Φ, rfl⟩ := (rowTestEquiv σ hσ hσs (n + 1)).surjective Φ₂
    refine ⟨f, f', Φ, ?_⟩
    rwa [dualEqualRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ] at hR
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨glModelEquiv σ hσ hσs hψ n π ℓ f, glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f',
      rowTestEquiv σ hσ hσs (n + 1) Φ, ?_⟩
    rwa [dualEqualRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ]

include habv in
/-- The fixed-monomial equal-rank functional equation transfers. -/
theorem equalRankEpsilonEquation_map_iff (ν : AdditiveHaarMeasure F)
    (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ)
    (c : ℂˣ) (m : ℤ) :
    EqualRankEpsilonEquation q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) ν' π τ
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        c m ↔
      EqualRankEpsilonEquation q ψ abv μ ν (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' c m := by
  unfold EqualRankEpsilonEquation
  rw [equalRankRationalValues_map σ hσ hσs hψ habv q μ π τ ℓ ℓ',
    dualEqualRankRationalValues_map σ hσ hσs hψ habv q μ π τ ℓ ℓ']
  refine exists_congr fun ζ => exists_congr fun P => exists_congr fun Pdual =>
    and_congr (hasModelMinusOneScalar_glInverseFunctionalEquiv_iff σ hσ hσs hψ τ ℓ' ζ)
      (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h f f' Φ
    obtain ⟨Φhat₂, R, Rdual, h0, h1, h2, h3⟩ := h (glModelEquiv σ hσ hσs hψ n π ℓ f)
      (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f') (rowTestEquiv σ hσ hσs (n + 1) Φ)
    obtain ⟨Φhat, rfl⟩ := (rowTestEquiv σ hσ hσs (n + 1)).surjective Φhat₂
    refine ⟨Φhat, R, Rdual, (isRowFourierPair_map_iff σ hσ hσs hψ ν ν' hν
      (rowTestEquiv_apply_map σ hσ hσs Φ) (rowTestEquiv_apply_map σ hσ hσs Φhat)).1 h0,
      ?_, ?_, h3⟩
    · rwa [equalRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ] at h1
    · rwa [dualEqualRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φhat] at h2
  · intro h f₂ f₂' Φ₂
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ n π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    obtain ⟨Φ, rfl⟩ := (rowTestEquiv σ hσ hσs (n + 1)).surjective Φ₂
    obtain ⟨Φhat, R, Rdual, h0, h1, h2, h3⟩ := h f f' Φ
    refine ⟨rowTestEquiv σ hσ hσs (n + 1) Φhat, R, Rdual,
      (isRowFourierPair_map_iff σ hσ hσs hψ ν ν' hν
        (rowTestEquiv_apply_map σ hσ hσs Φ) (rowTestEquiv_apply_map σ hσ hσs Φhat)).2 h0,
      ?_, ?_, h3⟩
    · rwa [equalRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φ]
    · rwa [dualEqualRankModelIntegral_map σ hσ hσs hψ habv μ π τ ℓ ℓ' f f' Φhat]

end EqualRank

section UnequalRank

variable {r : ℕ} (hnr : n < r) (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E)
  [SigmaFinite ν'.measure] (hν : ν'.measure = ν.measure.map σ)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
  (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W)
  (ℓ : glFunctionals ψ r (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom))
  (ℓ' : glInverseFunctionals ψ n (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom))

omit [IsTopologicalRing F] [IsTopologicalRing E] in
include habv hν in
theorem unequalRankIntegralAt_model_map (j k : ℕ) (hr : r = n + (j + k + 1))
    (f : (coefficientModel (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (f' : (coefficientModel (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ').toSubmodule) :
    unequalRankIntegralAt j k hr ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) (glModelEquiv σ hσ hσs hψ r π ℓ f).val
        (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f').val =
      unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) f.val f'.val :=
  unequalRankIntegralAt_map σ hσ hσs habv μ ν ν' hν j k hr
    (glModelEquiv_apply_fieldEquiv σ hσ hσs hψ π ℓ f)
    (glInverseModelEquiv_apply_fieldEquiv σ hσ hσs hψ τ ℓ' f')

include habv hν in
theorem dualUnequalRankModelIntegralAt_map (j k : ℕ) (hr : r = n + (j + k + 1))
    (f : (coefficientModel (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom) ℓ).toSubmodule)
    (f' : (coefficientModel (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ').toSubmodule) :
    dualUnequalRankModelIntegralAt hnr j k hr ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        ν' π τ (glFunctionalEquiv σ hσ hσs hψ r π ℓ)
        (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        (glModelEquiv σ hσ hσs hψ r π ℓ f) (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f') =
      dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' f f' := by
  unfold dualUnequalRankModelIntegralAt
  refine unequalRankIntegralAt_map σ hσ hσs habv μ ν ν' hν k j _ (fun g => ?_)
    (secondDualFunction_fieldEquiv σ hσ hσs
      (glInverseModelEquiv_apply_fieldEquiv σ hσ hσs hψ τ ℓ' f'))
  rw [← fieldEquiv_blockWeylAt σ hσ hσs hnr]
  exact translateWhittaker_fieldEquiv σ hσ hσs
    (firstDualFunction_fieldEquiv σ hσ hσs (glModelEquiv_apply_fieldEquiv σ hσ hσs hψ π ℓ f))
    _ g

omit [IsTopologicalRing F] [IsTopologicalRing E] in
include habv hν in
theorem unequalRankValuesAt_map (j k : ℕ) (hr : r = n + (j + k + 1)) :
    unequalRankValuesAt j k hr q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n))
        (rectangularMeasure ν' j (n + 1)) π τ (glFunctionalEquiv σ hσ hσs hψ r π ℓ)
        (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ') =
      unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' := by
  rw [unequalRankValuesAt_eq, unequalRankValuesAt_eq]
  ext R
  constructor
  · rintro ⟨f₂, f₂', hR⟩
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ r π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    refine ⟨f, f', ?_⟩
    rwa [unequalRankIntegralAt_model_map σ hσ hσs hψ habv μ ν ν' hν π τ ℓ ℓ' j k hr] at hR
  · rintro ⟨f, f', hR⟩
    refine ⟨glModelEquiv σ hσ hσs hψ r π ℓ f, glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f', ?_⟩
    rwa [unequalRankIntegralAt_model_map σ hσ hσs hψ habv μ ν ν' hν π τ ℓ ℓ' j k hr]

include habv hν in
theorem dualUnequalRankRationalValuesAt_map (j k : ℕ) (hr : r = n + (j + k + 1)) :
    dualUnequalRankRationalValuesAt hnr j k hr q ψ' abv'
        (μ.map (quotientHomeomorph σ hσ hσs n)) ν' π τ (glFunctionalEquiv σ hσ hσs hψ r π ℓ)
        (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ') =
      dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' := by
  ext R
  constructor
  · rintro ⟨f₂, f₂', hR⟩
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ r π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    refine ⟨f, f', ?_⟩
    rwa [dualUnequalRankModelIntegralAt_map σ hσ hσs hψ habv μ hnr ν ν' hν π τ ℓ ℓ' j k hr]
      at hR
  · rintro ⟨f, f', hR⟩
    refine ⟨glModelEquiv σ hσ hσs hψ r π ℓ f, glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f', ?_⟩
    rwa [dualUnequalRankModelIntegralAt_map σ hσ hσs hψ habv μ hnr ν ν' hν π τ ℓ ℓ' j k hr]

include habv hν in
/-- The fixed-monomial unequal-rank functional equation transfers. -/
theorem unequalRankEpsilonEquation_map_iff (c : ℂˣ) (m : ℤ) :
    UnequalRankEpsilonEquation hnr q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) ν' π τ
        (glFunctionalEquiv σ hσ hσs hψ r π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        c m ↔
      UnequalRankEpsilonEquation hnr q ψ abv μ ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) ℓ ℓ' c m := by
  unfold UnequalRankEpsilonEquation
  refine exists_congr fun ζ => exists_congr fun P => exists_congr fun Pdual =>
    and_congr (hasModelMinusOneScalar_glInverseFunctionalEquiv_iff σ hσ hσs hψ τ ℓ' ζ)
      (forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_)
  rw [unequalRankValuesAt_map σ hσ hσs hψ habv q μ ν ν' hν π τ ℓ ℓ' j k hr,
    dualUnequalRankRationalValuesAt_map σ hσ hσs hψ habv q μ hnr ν ν' hν π τ ℓ ℓ' j k hr]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h f f'
    obtain ⟨R, Rdual, h1, h2, h3⟩ := h (glModelEquiv σ hσ hσs hψ r π ℓ f)
      (glInverseModelEquiv σ hσ hσs hψ n τ ℓ' f')
    refine ⟨R, Rdual, ?_, ?_, h3⟩
    · rwa [unequalRankIntegralAt_model_map σ hσ hσs hψ habv μ ν ν' hν π τ ℓ ℓ' j k hr] at h1
    · rwa [dualUnequalRankModelIntegralAt_map σ hσ hσs hψ habv μ hnr ν ν' hν π τ ℓ ℓ' j k hr]
        at h2
  · intro h f₂ f₂'
    obtain ⟨f, rfl⟩ := (glModelEquiv σ hσ hσs hψ r π ℓ).surjective f₂
    obtain ⟨f', rfl⟩ := (glInverseModelEquiv σ hσ hσs hψ n τ ℓ').surjective f₂'
    obtain ⟨R, Rdual, h1, h2, h3⟩ := h f f'
    refine ⟨R, Rdual, ?_, ?_, h3⟩
    · rwa [unequalRankIntegralAt_model_map σ hσ hσs hψ habv μ ν ν' hν π τ ℓ ℓ' j k hr]
    · rwa [dualUnequalRankModelIntegralAt_map σ hσ hσs hψ habv μ hnr ν ν' hν π τ ℓ ℓ' j k hr]

end UnequalRank

end EpsilonEquations

section EpsilonFactors

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]
  {ψ : UnitaryAdditiveCharacter F} {ψ' : UnitaryAdditiveCharacter E}
  (hψ : ∀ x, ψ' (σ x) = ψ x)
  {abv : AbsoluteValue F ℝ} {abv' : AbsoluteValue E ℝ} (habv : ∀ x, abv' (σ x) = abv x)
  (q : ℕ) {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) E)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) E)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) E)] [BorelSpace (upperUnipotent (n + 1) E)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)]
  (ν : AdditiveHaarMeasure F) (ν' : AdditiveHaarMeasure E) [SigmaFinite ν'.measure]
  (hν : ν'.measure = ν.measure.map σ)
  (hG : generalLinearHaar E n = (generalLinearHaar F n).map (fieldEquiv (n + 1) σ hσ hσs))
  (hU : unipotentHaar E n = (unipotentHaar F n).map (unipotentEquiv σ hσ hσs (n + 1)))

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) E)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) E)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient n E)] [BorelSpace (LeftUnipotentQuotient n E)] in
include hU in
theorem isMulRightInvariant_unipotentHaar_iff :
    IsMulRightInvariant (unipotentHaar E n) ↔ IsMulRightInvariant (unipotentHaar F n) := by
  rw [hU]
  exact isMulRightInvariant_map_iff _ _

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include hG hU in
theorem isCompatible_unipotentHaar_map_iff [IsMulRightInvariant (unipotentHaar F n)]
    [IsMulRightInvariant (unipotentHaar E n)] (μ : Measure (LeftUnipotentQuotient n F)) :
    IsCompatible (upperUnipotent (n + 1) E) (generalLinearHaar E n) (unipotentHaar E n)
        (μ.map (quotientHomeomorph σ hσ hσs n)) ↔
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ :=
  isCompatible_map_iff (fieldEquiv (n + 1) σ hσ hσs) (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs)
    _ _ _ _ hG hU μ

omit [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E] in
include hG hU in
theorem compatibleMeasureExists_unipotentHaar_iff [IsMulRightInvariant (unipotentHaar F n)]
    [IsMulRightInvariant (unipotentHaar E n)] :
    CompatibleMeasureExists (upperUnipotent (n + 1) E) (generalLinearHaar E n)
        (unipotentHaar E n) ↔
      CompatibleMeasureExists (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) :=
  compatibleMeasureExists_iff (fieldEquiv (n + 1) σ hσ hσs)
    (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs) _ _ _ _ hG hU

include hψ habv hν hG hU in
/-- The equal-rank epsilon relation transfers along a field isomorphism carrying
the normalized Haar measures onto each other. -/
theorem isEqualRankEpsilonFactor_comp_iff
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (e : ℂˣ × ℤ) :
    IsEqualRankEpsilonFactor q ψ' abv' ν' π τ e ↔
      IsEqualRankEpsilonFactor q ψ abv ν (π.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) e := by
  have hinv := isMulRightInvariant_unipotentHaar_iff σ hσ hσs hU
  constructor
  · rintro ⟨⟨hE, hcE⟩, ⟨ℓ₂, hℓ₂⟩, ⟨ℓ₂', hℓ₂'⟩, hall⟩
    have hF := hinv.1 hE
    refine ⟨⟨hF, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).1 hcE⟩,
      ⟨(glFunctionalEquiv σ hσ hσs hψ n π).symm ℓ₂, hℓ₂⟩,
      ⟨(glInverseFunctionalEquiv σ hσ hσs hψ n τ).symm ℓ₂', hℓ₂'⟩, ?_⟩
    intro _ μ hμ ℓ ℓ' hℓ hℓ'
    exact (equalRankEpsilonEquation_map_iff σ hσ hσs hψ habv q μ π τ ℓ ℓ' ν ν' hν
      e.1 e.2).1 (hall (μ.map (quotientHomeomorph σ hσ hσs n))
        ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).2 hμ)
        (glFunctionalEquiv σ hσ hσs hψ n π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        hℓ hℓ')
  · rintro ⟨⟨hF, hcF⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    have hE := hinv.2 hF
    refine ⟨⟨hE, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).2 hcF⟩,
      ⟨glFunctionalEquiv σ hσ hσs hψ n π ℓ, hℓ⟩,
      ⟨glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ', hℓ'⟩, ?_⟩
    intro _ μ₂ hμ₂ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
    obtain ⟨μ, rfl⟩ := exists_map_eq (fieldEquiv (n + 1) σ hσ hσs)
      (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs) μ₂
    exact (equalRankEpsilonEquation_map_iff σ hσ hσs hψ habv q μ π τ
      ((glFunctionalEquiv σ hσ hσs hψ n π).symm ℓ₂)
      ((glInverseFunctionalEquiv σ hσ hσs hψ n τ).symm ℓ₂') ν ν' hν e.1 e.2).2
      (hall μ ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).1 hμ₂) _ _ hℓ₂ hℓ₂')

include hψ habv hν hG hU in
/-- The unequal-rank epsilon relation transfers along a field isomorphism
carrying the normalized Haar measures onto each other. -/
theorem isUnequalRankEpsilonFactor_comp_iff {r : ℕ} (hnr : n < r)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (e : ℂˣ × ℤ) :
    IsUnequalRankEpsilonFactor hnr q ψ' abv' ν' π τ e ↔
      IsUnequalRankEpsilonFactor hnr q ψ abv ν
        (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) e := by
  have hinv := isMulRightInvariant_unipotentHaar_iff σ hσ hσs hU
  constructor
  · rintro ⟨⟨hE, hcE⟩, ⟨ℓ₂, hℓ₂⟩, ⟨ℓ₂', hℓ₂'⟩, hall⟩
    have hF := hinv.1 hE
    refine ⟨⟨hF, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).1 hcE⟩,
      ⟨(glFunctionalEquiv σ hσ hσs hψ r π).symm ℓ₂, hℓ₂⟩,
      ⟨(glInverseFunctionalEquiv σ hσ hσs hψ n τ).symm ℓ₂', hℓ₂'⟩, ?_⟩
    intro _ μ hμ ℓ ℓ' hℓ hℓ'
    exact (unequalRankEpsilonEquation_map_iff σ hσ hσs hψ habv q μ hnr ν ν' hν π τ ℓ ℓ'
      e.1 e.2).1 (hall (μ.map (quotientHomeomorph σ hσ hσs n))
        ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).2 hμ)
        (glFunctionalEquiv σ hσ hσs hψ r π ℓ) (glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ')
        hℓ hℓ')
  · rintro ⟨⟨hF, hcF⟩, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    have hE := hinv.2 hF
    refine ⟨⟨hE, (compatibleMeasureExists_unipotentHaar_iff σ hσ hσs hG hU).2 hcF⟩,
      ⟨glFunctionalEquiv σ hσ hσs hψ r π ℓ, hℓ⟩,
      ⟨glInverseFunctionalEquiv σ hσ hσs hψ n τ ℓ', hℓ'⟩, ?_⟩
    intro _ μ₂ hμ₂ ℓ₂ ℓ₂' hℓ₂ hℓ₂'
    obtain ⟨μ, rfl⟩ := exists_map_eq (fieldEquiv (n + 1) σ hσ hσs)
      (fieldEquiv_mem_upperUnipotent_iff σ hσ hσs) μ₂
    exact (unequalRankEpsilonEquation_map_iff σ hσ hσs hψ habv q μ hnr ν ν' hν π τ
      ((glFunctionalEquiv σ hσ hσs hψ r π).symm ℓ₂)
      ((glInverseFunctionalEquiv σ hσ hσs hψ n τ).symm ℓ₂') e.1 e.2).2
      (hall μ ((isCompatible_unipotentHaar_map_iff σ hσ hσs hG hU μ).1 hμ₂) _ _ hℓ₂ hℓ₂')

include hψ habv hν hG hU in
/-- **Epsilon factors along a field isomorphism.** `e` is the JPSS epsilon factor
of `(π, τ)` over `E` exactly when it is the epsilon factor of the pulled-back
pair over `F`, for corresponding characters, absolute values and additive Haar
measures, when the normalized Haar measures of `GL_(n+1)` and of its upper
unipotent subgroup correspond. -/
theorem isPairEpsilonFactor_comp_iff {r : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) E) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) E) W) (e : ℂˣ × ℤ) :
    IsPairEpsilonFactor q ψ' abv' ν' π τ e ↔
      IsPairEpsilonFactor q ψ abv ν (π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom)
        (τ.comp (fieldEquiv (n + 1) σ hσ hσs).toMonoidHom) e := by
  rcases lt_trichotomy n r with h | rfl | h
  · rw [isPairEpsilonFactor_of_lt h, isPairEpsilonFactor_of_lt h]
    exact isUnequalRankEpsilonFactor_comp_iff σ hσ hσs hψ habv q ν ν' hν hG hU h π τ e
  · rw [isPairEpsilonFactor_self, isPairEpsilonFactor_self]
    exact isEqualRankEpsilonFactor_comp_iff σ hσ hσs hψ habv q ν ν' hν hG hU π τ e
  · exact iff_of_false (not_isPairEpsilonFactor_of_lt h) (not_isPairEpsilonFactor_of_lt h)

end EpsilonFactors

end Langlands.RankinSelberg.FieldTransport
