import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Langlands.Representation.Plancherel.CompactIntertwiningComposition

/-! # Equivariance of continued rational operator families -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uH uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)
  {Ω D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

open UnramifiedOperatorFamily

include hp hG

/-- A polynomial intertwining equation for the original family propagates
to its global polynomial numerator, including zeros of the denominator. -/
theorem rationalOperatorContinuation_numerator_commutes
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (p : RationalOperatorContinuationData Ω A)
    (R : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
      Module.End ℂ V)
    (S : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
      Module.End ℂ W)
    (hR : IsPolynomialOperatorOn Set.univ (fun χ => R χ.val))
    (hS : IsPolynomialOperatorOn Set.univ (fun χ => S χ.val))
    (hcomm : ∀ χ : Ω, (A χ).comp (R χ.val) = (S χ.val).comp (A χ)) :
    ∀ χ, (p.numerator χ).comp (R χ) = (S χ).comp (p.numerator χ) := by
  intro χ
  apply LinearMap.ext
  intro v
  have hz := rationalUnramifiedPolynomial_eq_zero_of_isOpen G hp hG hD hne
    (show D ⊆ Set.univ from fun _ _ => Set.mem_univ _)
    (fun ψ => (p.numerator ψ.val).comp (R ψ.val) v -
      (S ψ.val).comp (p.numerator ψ.val) v)
    (((p.polynomial.comp hR) v).sub ((hS.comp p.polynomial) v)) (by
      intro ψ hψ
      rw [p.clears ⟨ψ, hDΩ hψ⟩]
      have he := congrArg (fun T : V →ₗ[ℂ] W => T v)
        (hcomm ⟨ψ, hDΩ hψ⟩)
      simp only [LinearMap.comp_apply] at he
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, he, sub_self])
  exact sub_eq_zero.mp (hz ⟨χ, Set.mem_univ χ⟩)

/-- Division by the selected denominator preserves the continued
intertwining equation at every point of its full nonzero locus. -/
theorem rationalOperatorContinuation_commutes
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (p : RationalOperatorContinuationData Ω A)
    (R : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
      Module.End ℂ V)
    (S : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
      Module.End ℂ W)
    (hR : IsPolynomialOperatorOn Set.univ (fun χ => R χ.val))
    (hS : IsPolynomialOperatorOn Set.univ (fun χ => S χ.val))
    (hcomm : ∀ χ : Ω, (A χ).comp (R χ.val) = (S χ.val).comp (A χ)) :
    ∀ χ : p.regularRegion,
      (p.continuedOperator χ).comp (R χ.val) =
        (S χ.val).comp (p.continuedOperator χ) := by
  intro χ
  apply LinearMap.ext
  intro v
  have he := congrArg (fun T : V →ₗ[ℂ] W => T v)
    (rationalOperatorContinuation_numerator_commutes G hp hG hD hne hDΩ
      A p R S hR hS hcomm χ.val)
  simpa only [RationalOperatorContinuationData.continuedOperator,
    LinearMap.comp_apply, LinearMap.smul_apply, map_smul] using
    congrArg (fun w => (p.denominator.val χ.val)⁻¹ • w) he

variable {H : Type uH} [Monoid H]
  (ρ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
    Representation ℂ H V)
  (σ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul) →
    Representation ℂ H W)
  (hρ : ∀ g, IsPolynomialOperatorOn Set.univ (fun χ => ρ χ.val g))
  (hσ : ∀ g, IsPolynomialOperatorOn Set.univ (fun χ => σ χ.val g))
  (J : ∀ χ : Ω, (ρ χ.val).IntertwiningMap (σ χ.val))
  (p : RationalOperatorContinuationData Ω (fun χ => (J χ).toLinearMap))
  (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)

/-- The constructed linear continuation is an actual intertwiner for each
parameter-dependent representation action on the regular region. -/
def continuedIntertwiner (χ : p.regularRegion) :
    (ρ χ.val).IntertwiningMap (σ χ.val) where
  toLinearMap := p.continuedOperator χ
  isIntertwining' g :=
    rationalOperatorContinuation_commutes G hp hG hD hne hDΩ
      (fun ψ => (J ψ).toLinearMap) p (fun ψ => ρ ψ g) (fun ψ => σ ψ g)
      (hρ g) (hσ g) (fun ψ => (J ψ).isIntertwining' g) χ

@[simp]
theorem continuedIntertwiner_toLinearMap (χ : p.regularRegion) :
    (continuedIntertwiner G hp hG ρ σ hρ hσ J p hD hne hDΩ χ).toLinearMap =
      p.continuedOperator χ := rfl

/-- Bundling equivariance leaves the already proved rationality unchanged. -/
theorem continuedIntertwiner_rational :
    IsRationalOperatorOn p.regularRegion
      (fun χ => (continuedIntertwiner G hp hG ρ σ hρ hσ J p hD hne hDΩ χ).toLinearMap) :=
  p.continuedOperator_rational

/-- The continued equivariant maps recover the original intertwiners,
including their original parameter-dependent actions. -/
theorem continuedIntertwiner_agrees (χ : Ω) :
    continuedIntertwiner G hp hG ρ σ hρ hσ J p hD hne hDΩ
      ⟨χ.val, p.subset_regularRegion χ.property⟩ = J χ := by
  apply Representation.IntertwiningMap.ext
  exact p.continuedOperator_agrees χ

/-- Different continuation choices give the same equivariant maps on their
common regular region. No equality of chosen denominators is required. -/
theorem continuedIntertwiner_unique
    (q : RationalOperatorContinuationData Ω (fun χ => (J χ).toLinearMap))
    (χ : ↥(p.regularRegion ∩ q.regularRegion)) :
    continuedIntertwiner G hp hG ρ σ hρ hσ J p hD hne hDΩ
        ⟨χ.val, χ.property.1⟩ =
      continuedIntertwiner G hp hG ρ σ hρ hσ J q hD hne hDΩ
        ⟨χ.val, χ.property.2⟩ := by
  apply Representation.IntertwiningMap.ext
  exact rationalOperatorContinuationData_unique G hp hG
    (fun ψ => (J ψ).toLinearMap) p q hD hne hDΩ χ

end Langlands.Plancherel
