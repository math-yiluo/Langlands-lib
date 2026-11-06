import Langlands.Representation.Plancherel.RationalUnramifiedScalarContinuation

/-! # Continuation of supplied rational linear operator families -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

universe u uG uI uV uW

namespace UnramifiedOperatorFamily

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω : Set (unramifiedCharacters ν)}

/-- A global finite regular expansion extending a supplied local vector
family. Uniqueness requires an actual-character open-set hypothesis. -/
structure PolynomialExtensionData (Ω : Set (unramifiedCharacters ν)) (f : Ω → W) where
  values : unramifiedCharacters ν → W
  polynomial : IsPolynomialOn Set.univ (fun χ => values χ.val)
  agrees : ∀ χ : Ω, values χ.val = f χ

/-- A local finite expansion supplies a global one with exactly the same
regular coefficients and fixed vectors. -/
def polynomialExtension {f : Ω → W} (hf : IsPolynomialOn Ω f) :
    PolynomialExtensionData Ω f :=
  Classical.choice (by
    obtain ⟨n, b, w, hf⟩ := hf
    exact ⟨{
      values := fun χ => ∑ i, (b i).val χ • w i
      polynomial := ⟨n, b, w, fun _ => rfl⟩
      agrees := fun χ => (hf χ).symm
    }⟩)

/-- One global polynomial numerator and the original regular denominator
for a supplied operator family. This records linear operators, without an
equivariance assertion for any representation action. -/
structure RationalOperatorContinuationData
    (Ω : Set (unramifiedCharacters ν)) (A : Ω → V →ₗ[ℂ] W) where
  denominator : unramifiedRegularFunctions ν
  denominator_nonzero : ∀ χ : Ω, denominator.val χ.val ≠ 0
  numerator : unramifiedCharacters ν → V →ₗ[ℂ] W
  polynomial : IsPolynomialOperatorOn Set.univ (fun χ => numerator χ.val)
  clears : ∀ χ : Ω, numerator χ.val = denominator.val χ.val • A χ

namespace RationalOperatorContinuationData

variable {A : Ω → V →ₗ[ℂ] W} (p : RationalOperatorContinuationData Ω A)

/-- Continue only where the selected denominator is nonzero. -/
def regularRegion : Set (unramifiedCharacters ν) :=
  {χ | p.denominator.val χ ≠ 0}

theorem subset_regularRegion : Ω ⊆ p.regularRegion :=
  fun χ hχ => p.denominator_nonzero ⟨χ, hχ⟩

/-- Division of the constructed polynomial numerator on its regular region. -/
def continuedOperator (χ : p.regularRegion) : V →ₗ[ℂ] W :=
  (p.denominator.val χ.val)⁻¹ • p.numerator χ.val

/-- The constructed family is rational on the entire selected regular region. -/
theorem continuedOperator_rational :
    IsRationalOperatorOn p.regularRegion p.continuedOperator := by
  refine ⟨p.denominator, fun χ => χ.property, fun v => ?_⟩
  have hp := (p.polynomial v).restrict
    (show p.regularRegion ⊆ Set.univ from fun _ _ => Set.mem_univ _)
  convert hp using 1
  funext χ
  change p.denominator.val χ.val •
    ((p.denominator.val χ.val)⁻¹ • p.numerator χ.val v) = p.numerator χ.val v
  rw [smul_smul, mul_inv_cancel₀ χ.property, one_smul]

/-- Restriction of the continued family recovers each original linear map. -/
theorem continuedOperator_agrees (χ : Ω) :
    p.continuedOperator ⟨χ.val, p.subset_regularRegion χ.property⟩ = A χ := by
  unfold continuedOperator
  rw [p.clears χ, smul_smul, inv_mul_cancel₀ (p.denominator_nonzero χ), one_smul]

end RationalOperatorContinuationData

end UnramifiedOperatorFamily

section ActualCharacters

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

/-- Two global polynomial extensions of the same local vector family agree
when the original region contains a nonempty ambient open subset. -/
theorem polynomialExtensionData_unique
    {f : Ω → W} (p q : PolynomialExtensionData Ω f)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) :
    p.values = q.values := by
  funext χ
  have hz := rationalUnramifiedPolynomial_eq_zero_of_isOpen G hp hG hD hne
    (show D ⊆ Set.univ from fun _ _ => Set.mem_univ _)
    (fun ψ => p.values ψ.val - q.values ψ.val)
    (p.polynomial.sub q.polynomial) (by
      intro ψ hψ
      rw [p.agrees ⟨ψ, hDΩ hψ⟩, q.agrees ⟨ψ, hDΩ hψ⟩, sub_self])
  exact sub_eq_zero.mp (hz ⟨χ, Set.mem_univ χ⟩)

/-- Extend each fixed-vector polynomial numerator and use uniqueness to prove
that the resulting global operators remain linear in the input vector. -/
def polynomialOperatorExtension
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (hA : IsPolynomialOperatorOn Ω A)
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    V →ₗ[ℂ] W where
  toFun v := (polynomialExtension (hA v)).values χ
  map_add' v w := by
    let q : PolynomialExtensionData Ω (fun ψ => A ψ (v + w)) := {
      values := fun ψ => (polynomialExtension (hA v)).values ψ +
        (polynomialExtension (hA w)).values ψ
      polynomial := (polynomialExtension (hA v)).polynomial.add
        (polynomialExtension (hA w)).polynomial
      agrees := by
        intro ψ
        rw [(polynomialExtension (hA v)).agrees ψ,
          (polynomialExtension (hA w)).agrees ψ, map_add]
    }
    exact congrFun
      (polynomialExtensionData_unique G hp hG (polynomialExtension (hA (v + w))) q
        hD hne hDΩ) χ
  map_smul' c v := by
    let q : PolynomialExtensionData Ω (fun ψ => A ψ (c • v)) := {
      values := fun ψ => c • (polynomialExtension (hA v)).values ψ
      polynomial := by
        simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
          (polynomialExtension (hA v)).polynomial.linearMap
            (c • (LinearMap.id : Module.End ℂ W))
      agrees := by
        intro ψ
        rw [(polynomialExtension (hA v)).agrees ψ, map_smul]
    }
    exact congrFun
      (polynomialExtensionData_unique G hp hG (polynomialExtension (hA (c • v))) q
        hD hne hDΩ) χ

theorem polynomialOperatorExtension_polynomial
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (hA : IsPolynomialOperatorOn Ω A) :
    IsPolynomialOperatorOn Set.univ
      (fun χ => polynomialOperatorExtension G hp hG hD hne hDΩ A hA χ.val) :=
  fun v => (polynomialExtension (hA v)).polynomial

theorem polynomialOperatorExtension_agrees
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (hA : IsPolynomialOperatorOn Ω A) (χ : Ω) :
    polynomialOperatorExtension G hp hG hD hne hDΩ A hA χ.val = A χ := by
  apply LinearMap.ext
  intro v
  exact (polynomialExtension (hA v)).agrees χ

/-- A rationality witness on the original region constructs a global
polynomial numerator with that witness's denominator. No operator value
at a zero of that denominator is defined by division. -/
def rationalOperatorContinuation
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (A : Ω → V →ₗ[ℂ] W) (hA : IsRationalOperatorOn Ω A) :
    RationalOperatorContinuationData Ω A :=
  Classical.choice (by
    obtain ⟨b, hb, hpoly⟩ := hA
    exact ⟨{
      denominator := b
      denominator_nonzero := hb
      numerator := polynomialOperatorExtension G hp hG hD hne hDΩ
        (fun χ => b.val χ.val • A χ) hpoly
      polynomial := polynomialOperatorExtension_polynomial G hp hG hD hne hDΩ
        (fun χ => b.val χ.val • A χ) hpoly
      clears := polynomialOperatorExtension_agrees G hp hG hD hne hDΩ
        (fun χ => b.val χ.val • A χ) hpoly
    }⟩)

/-- All constructions from the same original family agree at every common
regular value, even when their selected denominators and numerators differ. -/
theorem rationalOperatorContinuationData_unique
    (A : Ω → V →ₗ[ℂ] W)
    (p q : RationalOperatorContinuationData Ω A)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω) :
    ∀ χ : ↥(p.regularRegion ∩ q.regularRegion),
      p.continuedOperator ⟨χ.val, χ.property.1⟩ =
        q.continuedOperator ⟨χ.val, χ.property.2⟩ := by
  apply rationalUnramifiedOperator_eq_of_eqOn_isOpen G hp hG hD hne
    (show D ⊆ p.regularRegion ∩ q.regularRegion from fun χ hχ =>
      ⟨p.subset_regularRegion (hDΩ hχ), q.subset_regularRegion (hDΩ hχ)⟩)
    _ _
    (p.continuedOperator_rational.restrict Set.inter_subset_left)
    (q.continuedOperator_rational.restrict Set.inter_subset_right)
  intro χ hχ
  exact (p.continuedOperator_agrees ⟨χ, hDΩ hχ⟩).trans
    (q.continuedOperator_agrees ⟨χ, hDΩ hχ⟩).symm

end ActualCharacters

end Langlands.Plancherel
