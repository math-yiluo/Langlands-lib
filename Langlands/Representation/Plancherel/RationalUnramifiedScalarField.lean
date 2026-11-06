import Langlands.Representation.Plancherel.RationalUnramifiedScalarContinuation
import Langlands.Representation.Plancherel.RationalUnramifiedFunctionField

/-! # Extracted scalar coefficients in the actual unramified function field -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI uV

namespace UnramifiedOperatorFamily

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {Ω : Set (unramifiedCharacters ν)}

/-- A regular numerator and a denominator nonvanishing on the given region,
representing the supplied scalar function by cross-multiplication. -/
structure ScalarPresentation (Ω : Set (unramifiedCharacters ν)) (f : Ω → ℂ) where
  numerator : unramifiedRegularFunctions ν
  denominator : unramifiedRegularFunctions ν
  denominator_nonzero : ∀ χ : Ω, denominator.val χ.val ≠ 0
  clears : ∀ χ : Ω, denominator.val χ.val * f χ = numerator.val χ.val

namespace ScalarPresentation

variable {f : Ω → ℂ} (p : ScalarPresentation Ω f)

/-- A nonempty regular region excludes the zero regular denominator. -/
theorem denominator_ne_zero (hΩ : Ω.Nonempty) : p.denominator ≠ 0 := by
  obtain ⟨χ, hχ⟩ := hΩ
  intro hb
  apply p.denominator_nonzero ⟨χ, hχ⟩
  rw [hb]
  rfl

/-- This formula evaluates only on the supplied region of regular values. -/
theorem value_eq_div (χ : Ω) :
    f χ = p.numerator.val χ.val / p.denominator.val χ.val := by
  apply (eq_div_iff (p.denominator_nonzero χ)).mpr
  simpa only [mul_comm] using p.clears χ

end ScalarPresentation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Select a numerator presentation obtained from the given rational operator,
without postulating a scalar or choosing a different operator family. -/
def scalarCoefficientPresentation
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    ScalarPresentation Ω (fun χ => endomorphismScalarCoefficient v ℓ (A χ)) :=
  Classical.choice (by
    obtain ⟨a, b, hb, he⟩ := scalarCoefficient_numerator v ℓ A hA
    exact ⟨⟨a, b, hb, he⟩⟩)

end UnramifiedOperatorFamily

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

open UnramifiedOperatorFamily

namespace UnramifiedOperatorFamily.ScalarPresentation

variable
  {Ω Λ D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {f : Ω → ℂ} {g : Λ → ℂ}

/-- A presentation on a nonempty region gives a fraction with a verified
nonzero denominator in the existing actual function field. -/
def toFunctionField (p : ScalarPresentation Ω f) (hΩ : Ω.Nonempty) :
    rationalUnramifiedFunctionField G hp hG := by
  letI := rationalUnramifiedRegularFunctions_isDomain G hp hG
  exact IsLocalization.mk' (rationalUnramifiedFunctionField G hp hG) p.numerator
    ⟨p.denominator, mem_nonZeroDivisors_iff_ne_zero.mpr (p.denominator_ne_zero hΩ)⟩

theorem toFunctionField_eq_div (p : ScalarPresentation Ω f) (hΩ : Ω.Nonempty) :
    p.toFunctionField G hp hG hΩ =
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) p.numerator /
      algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
        (rationalUnramifiedFunctionField G hp hG) p.denominator := by
  let := rationalUnramifiedRegularFunctions_isDomain G hp hG
  exact IsFractionRing.mk'_eq_div _

include hp hG

/-- Agreement of the represented values on a nonempty ambient open set
forces equality of the original regular cross-products globally. -/
theorem cross_eq_of_eqOn_isOpen
    (p : ScalarPresentation Ω f) (q : ScalarPresentation Λ g)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) (hDΛ : D ⊆ Λ)
    (he : ∀ χ (hχ : χ ∈ D), f ⟨χ, hDΩ hχ⟩ = g ⟨χ, hDΛ hχ⟩) :
    p.numerator * q.denominator = q.numerator * p.denominator := by
  apply sub_eq_zero.mp
  apply rationalUnramifiedRegular_eq_zero_of_isOpen G hp hG _ hD hne
  intro χ hχ
  change p.numerator.val χ * q.denominator.val χ -
    q.numerator.val χ * p.denominator.val χ = 0
  rw [← p.clears ⟨χ, hDΩ hχ⟩, ← q.clears ⟨χ, hDΛ hχ⟩, he χ hχ]
  apply sub_eq_zero.mpr
  ac_rfl

/-- Fractions are independent of presentations and regular parameter
regions whenever their represented values agree on one common nonempty
ambient open subset. No global evaluation map at poles is asserted. -/
theorem toFunctionField_eq_of_eqOn_isOpen
    (p : ScalarPresentation Ω f) (q : ScalarPresentation Λ g)
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) (hDΛ : D ⊆ Λ)
    (he : ∀ χ (hχ : χ ∈ D), f ⟨χ, hDΩ hχ⟩ = g ⟨χ, hDΛ hχ⟩) :
    p.toFunctionField G hp hG hΩ = q.toFunctionField G hp hG hΛ := by
  let := rationalUnramifiedRegularFunctions_isDomain G hp hG
  apply IsLocalization.mk'_eq_of_eq'
  exact (p.cross_eq_of_eqOn_isOpen G hp hG q hD hne hDΩ hDΛ he).symm

end UnramifiedOperatorFamily.ScalarPresentation

variable
  {Ω D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The rational scalar is constructed from the given operator's coefficient
presentation, rather than supplied as normalization data. -/
def rationalUnramifiedOperatorScalar
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hΩ : Ω.Nonempty) :
    rationalUnramifiedFunctionField G hp hG :=
  (scalarCoefficientPresentation A hA v ℓ).toFunctionField G hp hG hΩ

include hp hG

/-- Every presentation of this operator coefficient gives the same function
field element, independently of the selected rationality witnesses. -/
theorem rationalUnramifiedOperatorScalar_eq_presentation
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (p : ScalarPresentation Ω (fun χ => endomorphismScalarCoefficient v ℓ (A χ)))
    (hΩ : Ω.Nonempty)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) :
    rationalUnramifiedOperatorScalar G hp hG A hA v ℓ hΩ =
      p.toFunctionField G hp hG hΩ := by
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen G hp hG
    _ _ hΩ hΩ hD hne hDΩ hDΩ
  intro χ hχ
  rfl

/-- The extracted fraction has an original regular numerator and denominator
that reproduce every coefficient value throughout the supplied region. -/
theorem rationalUnramifiedOperatorScalar_spec
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hΩ : Ω.Nonempty) :
    ∃ a b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul),
      b ≠ 0 ∧ (∀ χ : Ω, b.val χ.val ≠ 0) ∧
      rationalUnramifiedOperatorScalar G hp hG A hA v ℓ hΩ =
        algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
          (rationalUnramifiedFunctionField G hp hG) a /
        algebraMap (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
          (rationalUnramifiedFunctionField G hp hG) b ∧
      ∀ χ : Ω, endomorphismScalarCoefficient v ℓ (A χ) =
        a.val χ.val / b.val χ.val := by
  let p := scalarCoefficientPresentation A hA v ℓ
  exact ⟨p.numerator, p.denominator, p.denominator_ne_zero hΩ,
    p.denominator_nonzero, p.toFunctionField_eq_div G hp hG hΩ, p.value_eq_div⟩

/-- With generic scalarity, the function field element is independent of
both normalized extraction pairs and the rationality proof used to present
the same given family. -/
theorem rationalUnramifiedOperatorScalar_independent
    (A : Ω → Module.End ℂ V) (hA hA' : IsRationalOperatorOn Ω A)
    (v w : V) (ℓ m : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) (hm : m w = 1)
    (hΩ : Ω.Nonempty)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hscalar : ∀ χ (hχ : χ ∈ D), ∃ c : ℂ,
      A ⟨χ, hDΩ hχ⟩ = c • LinearMap.id) :
    rationalUnramifiedOperatorScalar G hp hG A hA v ℓ hΩ =
      rationalUnramifiedOperatorScalar G hp hG A hA' w m hΩ := by
  apply ScalarPresentation.toFunctionField_eq_of_eqOn_isOpen G hp hG
    _ _ hΩ hΩ hD hne hDΩ hDΩ
  intro χ hχ
  obtain ⟨c, hc⟩ := hscalar χ hχ
  rw [hc, endomorphismScalarCoefficient_smul_id v ℓ hℓ,
    endomorphismScalarCoefficient_smul_id w m hm]

end ActualCharacters

end Langlands.Plancherel
