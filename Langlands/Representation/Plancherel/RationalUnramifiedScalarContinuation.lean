import Langlands.Representation.Plancherel.RationalUnramifiedVectorCancellation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar extraction and continuation for actual unramified families -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI uV uW

namespace UnramifiedOperatorFamily

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)}

/-- A fixed matrix coefficient of an endomorphism, with no scalarity
assumption. Normalization of the vector and functional is a separate premise. -/
def endomorphismScalarCoefficient (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    Module.End ℂ V →ₗ[ℂ] ℂ where
  toFun T := ℓ (T v)
  map_add' T S := by simp
  map_smul' c T := by simp

@[simp]
theorem endomorphismScalarCoefficient_smul_id
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) (c : ℂ) :
    endomorphismScalarCoefficient v ℓ (c • LinearMap.id) = c := by
  simp [endomorphismScalarCoefficient, hℓ]

/-- A normalized coefficient recovers every scalar endomorphism. -/
theorem eq_scalarCoefficient_smul_id
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (T : Module.End ℂ V) (hT : ∃ c : ℂ, T = c • LinearMap.id) :
    T = endomorphismScalarCoefficient v ℓ T • LinearMap.id := by
  obtain ⟨c, rfl⟩ := hT
  rw [endomorphismScalarCoefficient_smul_id v ℓ hℓ]

/-- Every nonzero vector admits the normalization used for scalar extraction;
this is algebraic and needs no topology on the carrier. -/
theorem exists_normalized_scalar_functional (v : V) (hv : v ≠ 0) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ v = 1 :=
  Module.Projective.exists_dual_eq_one ℂ hv

theorem IsPolynomialOn.sub {f g : Ω → W}
    (hf : IsPolynomialOn Ω f) (hg : IsPolynomialOn Ω g) :
    IsPolynomialOn Ω (fun χ => f χ - g χ) := by
  simpa only [LinearMap.neg_apply, LinearMap.id_apply, sub_eq_add_neg] using
    hf.add (hg.linearMap (-LinearMap.id))

/-- The original operator denominator clears its extracted scalar coefficient.
The numerator is a single element of the actual evaluation-generated algebra. -/
theorem scalarCoefficient_numerator
    (v : V) (ℓ : V →ₗ[ℂ] ℂ)
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A) :
    ∃ a b : unramifiedRegularFunctions ν,
      (∀ χ : Ω, b.val χ.val ≠ 0) ∧
      ∀ χ : Ω, b.val χ.val * endomorphismScalarCoefficient v ℓ (A χ) =
        a.val χ.val := by
  obtain ⟨b, hb, hA⟩ := hA
  obtain ⟨a, ha⟩ := (isPolynomialOn_scalar_iff _).mp ((hA v).linearMap ℓ)
  refine ⟨a, b, hb, ?_⟩
  intro χ
  change b.val χ.val * ℓ ((A χ) v) = a.val χ.val
  simpa only [LinearMap.smul_apply, map_smul, smul_eq_mul] using ha χ

/-- A scalar coefficient defines a scalar endomorphism family with the same
whole-operator denominator. -/
theorem IsRationalOperatorOn.scalar_part
    {A : Ω → Module.End ℂ V} (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    IsRationalOperatorOn Ω
      (fun χ => endomorphismScalarCoefficient v ℓ (A χ) •
        (LinearMap.id : Module.End ℂ V)) := by
  obtain ⟨b, hb, hA⟩ := hA
  refine ⟨b, hb, fun w => ?_⟩
  change IsPolynomialOn Ω (fun χ => b.val χ.val • (ℓ ((A χ) v) • w))
  simpa only [LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    map_smul, smul_smul, smul_eq_mul] using
    ((hA v).linearMap ℓ).linearMap (LinearMap.toSpanSingleton ℂ V w)

end UnramifiedOperatorFamily

section ActualContinuation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)

open UnramifiedOperatorFamily

include hp hG hD hne

/-- Polynomial vector families are determined by any nonempty ambient open
subset of their parameter region. Neither the carrier nor the region needs a
topology beyond the actual character topology used for that open subset. -/
theorem rationalUnramifiedPolynomial_eq_zero_of_isOpen
    (f : Ω → W) (hf : IsPolynomialOn Ω f)
    (hz : ∀ χ (hχ : χ ∈ D), f ⟨χ, hDΩ hχ⟩ = 0) :
    ∀ χ : Ω, f χ = 0 := by
  intro χ
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (f χ)).mp
  intro ℓ
  obtain ⟨a, ha⟩ := (isPolynomialOn_scalar_iff _).mp (hf.linearMap ℓ)
  have ha0 : a = 0 := by
    apply rationalUnramifiedRegular_eq_zero_of_isOpen G hp hG a hD hne
    intro ψ hψ
    rw [← ha ⟨ψ, hDΩ hψ⟩, hz ψ hψ, map_zero]
  simpa only [ha0, Subalgebra.coe_zero, Pi.zero_apply] using ha χ

/-- Rational operator families on the same region agree everywhere if they
agree on a nonempty ambient open subset. Cross-multiplication uses their
original denominators; no vector-space topology or divisibility premise enters. -/
theorem rationalUnramifiedOperator_eq_of_eqOn_isOpen
    (A B : Ω → V →ₗ[ℂ] W)
    (hA : IsRationalOperatorOn Ω A) (hB : IsRationalOperatorOn Ω B)
    (he : ∀ χ (hχ : χ ∈ D), A ⟨χ, hDΩ hχ⟩ = B ⟨χ, hDΩ hχ⟩) :
    ∀ χ : Ω, A χ = B χ := by
  obtain ⟨b, hb, hA⟩ := hA
  obtain ⟨a, ha, hB⟩ := hB
  intro χ
  apply LinearMap.ext
  intro w
  have hpoly := ((hA w).regular_smul a).sub ((hB w).regular_smul b)
  have hz := rationalUnramifiedPolynomial_eq_zero_of_isOpen G hp hG hD hne hDΩ
    _ hpoly (by
      intro ψ hψ
      simp only [LinearMap.smul_apply, he ψ hψ, smul_smul]
      rw [mul_comm]
      exact sub_self _)
  have hzχ : (a.val χ.val * b.val χ.val) • (A χ w - B χ w) = 0 := by
    simpa only [LinearMap.smul_apply, smul_smul, smul_sub,
      mul_comm (b.val χ.val) (a.val χ.val)] using hz χ
  exact sub_eq_zero.mp
    ((smul_eq_zero.mp hzχ).resolve_left (mul_ne_zero (ha χ) (hb χ)))

/-- Generic scalarity of an actual rational endomorphism family extends to
its whole region of regular values. The scalar is extracted from the given
operators, not supplied independently. -/
theorem rationalUnramifiedScalarContinuation
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v : V) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1)
    (hscalar : ∀ χ (hχ : χ ∈ D), ∃ c : ℂ,
      A ⟨χ, hDΩ hχ⟩ = c • LinearMap.id) :
    ∀ χ : Ω, A χ = endomorphismScalarCoefficient v ℓ (A χ) • LinearMap.id := by
  apply rationalUnramifiedOperator_eq_of_eqOn_isOpen G hp hG hD hne hDΩ
    A _ hA (hA.scalar_part v ℓ)
  intro χ hχ
  exact eq_scalarCoefficient_smul_id v ℓ hℓ _ (hscalar χ hχ)

/-- The continued scalar is independent of both normalized extraction choices. -/
theorem rationalUnramifiedScalarCoefficient_independent
    (A : Ω → Module.End ℂ V) (hA : IsRationalOperatorOn Ω A)
    (v w : V) (ℓ m : V →ₗ[ℂ] ℂ) (hℓ : ℓ v = 1) (hm : m w = 1)
    (hscalar : ∀ χ (hχ : χ ∈ D), ∃ c : ℂ,
      A ⟨χ, hDΩ hχ⟩ = c • LinearMap.id) :
    ∀ χ : Ω,
      endomorphismScalarCoefficient v ℓ (A χ) =
        endomorphismScalarCoefficient w m (A χ) := by
  intro χ
  have he := congrArg (endomorphismScalarCoefficient w m)
    (rationalUnramifiedScalarContinuation G hp hG hD hne hDΩ
      A hA v ℓ hℓ hscalar χ)
  exact (he.trans (endomorphismScalarCoefficient_smul_id w m hm _)).symm

end ActualContinuation

end Langlands.Plancherel
