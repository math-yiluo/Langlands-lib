import Langlands.Representation.Plancherel.RationalOperatorPoleAlgebra
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # Tensor products and density scaling of whole-operator continuations -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Plancherel

universe u uI uV uW uV' uW'

open UnramifiedOperatorFamily

section Operators

variable {G : Type u} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {D E : Set (unramifiedCharacters ν)} {A : D → V →ₗ[ℂ] W}

namespace UnramifiedOperatorFamily.RationalOperatorContinuationData

/-- A restriction retains the same global numerator and denominator. -/
def restrict (p : RationalOperatorContinuationData D A) (he : E ⊆ D) :
    RationalOperatorContinuationData E (fun z => A ⟨z.val, he z.property⟩) where
  denominator := p.denominator
  denominator_nonzero z := p.denominator_nonzero ⟨z.val, he z.property⟩
  numerator := p.numerator
  polynomial := p.polynomial
  clears z := p.clears ⟨z.val, he z.property⟩

/-- The inverse parameter carries both parts of the same continuation. -/
def inversion (p : RationalOperatorContinuationData D A) :
    RationalOperatorContinuationData (Inv.inv ⁻¹' D) (fun z => A ⟨z.val⁻¹, z.property⟩) where
  denominator := unramifiedRegularInversion ν p.denominator
  denominator_nonzero z := p.denominator_nonzero ⟨z.val⁻¹, z.property⟩
  numerator z := p.numerator z⁻¹
  polynomial v := by simpa only [Set.preimage_univ] using (p.polynomial v).inversion
  clears z := p.clears ⟨z.val⁻¹, z.property⟩

/-- Fixed linear maps on the source and target preserve clearing and polynomiality. -/
def fixedMaps (p : RationalOperatorContinuationData D A) (e : V' →ₗ[ℂ] V) (f : W →ₗ[ℂ] W') :
    RationalOperatorContinuationData D (fun z => f ∘ₗ A z ∘ₗ e) where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator z := f ∘ₗ p.numerator z ∘ₗ e
  polynomial := (p.polynomial.precomp e).postcomp f
  clears z := by rw [p.clears z, LinearMap.smul_comp, LinearMap.comp_smul]

/-- A polynomial source map and a fixed target map preserve the continuation denominator. -/
def composePolynomial (p : RationalOperatorContinuationData D A)
    (e : unramifiedCharacters ν → V' →ₗ[ℂ] V) (f : W →ₗ[ℂ] W')
    (he : IsPolynomialOperatorOn Set.univ (fun z => e z.val)) :
    RationalOperatorContinuationData D (fun z => f ∘ₗ A z ∘ₗ e z.val) where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator z := f ∘ₗ p.numerator z ∘ₗ e z
  polynomial := (p.polynomial.comp he).postcomp f
  clears z := by rw [p.clears z, LinearMap.smul_comp, LinearMap.comp_smul]

/-- Equal operator families have the same clearing data. -/
def ofFamilyEq {B : D → V →ₗ[ℂ] W} (p : RationalOperatorContinuationData D A)
    (h : ∀ z, A z = B z) : RationalOperatorContinuationData D B where
  denominator := p.denominator
  denominator_nonzero := p.denominator_nonzero
  numerator := p.numerator
  polynomial := p.polynomial
  clears z := (p.clears z).trans (congrArg (p.denominator.val z.val • ·) (h z))

private theorem mul_div_clears (a b c : ℂ) (hb : b ≠ 0) : a * c = (c * b) * (a / b) := by
  field_simp

/-- Scale a continuation by a regular-function fraction on its entire domain. -/
def regularRatio (p : RationalOperatorContinuationData D A)
    (a b : unramifiedRegularFunctions ν) (hb : ∀ z : D, b.val z.val ≠ 0) :
    RationalOperatorContinuationData D (fun z => (a.val z.val / b.val z.val) • A z) where
  denominator := p.denominator * b
  denominator_nonzero z := mul_ne_zero (p.denominator_nonzero z) (hb z)
  numerator z := a.val z • p.numerator z
  polynomial := p.polynomial.regular_smul a
  clears z := by
    rw [p.clears z, smul_smul, smul_smul]
    exact congrArg (fun c : ℂ => c • A z) (mul_div_clears _ _ _ (hb z))

end UnramifiedOperatorFamily.RationalOperatorContinuationData
end Operators

namespace RationalOperatorPolePresentation

open ValuationKernelCoordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

local instance operatorContinuationPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

set_option hygiene false in
local notation "ν" => fun a => (rationalNormCharacters G a).toMul
local notation "R" => unramifiedRegularFunctions ν
local notation "X" => unramifiedCharacters ν

/-- Precompose and postcompose both presentations by fixed linear maps. -/
def fixedMaps {c : R} {N : X → V →ₗ[ℂ] W} (q : RationalOperatorPolePresentation G c N)
    (e : V' →ₗ[ℂ] V) (f : W →ₗ[ℂ] W') :
    RationalOperatorPolePresentation G c (fun z => f ∘ₗ N z ∘ₗ e) where
  denominator := q.denominator
  factors := q.factors
  numerator z := f ∘ₗ q.numerator z ∘ₗ e
  polynomial := (q.polynomial.precomp e).postcomp f
  cross z := by
    have h := congrArg (fun Q => f ∘ₗ Q ∘ₗ e) (q.cross z)
    simpa only [LinearMap.smul_comp, LinearMap.comp_smul] using h

/-- Apply a polynomial source map and a fixed target map to both presentations. -/
def composePolynomial {c : R} {N : X → V →ₗ[ℂ] W}
    (q : RationalOperatorPolePresentation G c N)
    (e : X → V' →ₗ[ℂ] V) (f : W →ₗ[ℂ] W')
    (he : IsPolynomialOperatorOn Set.univ (fun z => e z.val)) :
    RationalOperatorPolePresentation G c (fun z => f ∘ₗ N z ∘ₗ e z) where
  denominator := q.denominator
  factors := q.factors
  numerator z := f ∘ₗ q.numerator z ∘ₗ e z
  polynomial := (q.polynomial.comp he).postcomp f
  cross z := by
    have h := congrArg (fun Q => f ∘ₗ Q ∘ₗ e z) (q.cross z)
    simpa only [LinearMap.smul_comp, LinearMap.comp_smul] using h

/-- Multiply an operator pole presentation and a scalar pole presentation. -/
def regularRatio {c a b : R} {N : X → V →ₗ[ℂ] W} (q : RationalOperatorPolePresentation G c N)
    (r : RankOneScalarPolePresentation G a b) :
    RationalOperatorPolePresentation G (c * b) (fun z => a.val z • N z) where
  denominator := q.denominator * r.denominator
  factors := q.factors.mul G r.factors
  numerator z := r.numerator.val z • q.numerator z
  polynomial := q.polynomial.regular_smul r.numerator
  cross z := by
    have hrs : b.val z * r.numerator.val z = r.denominator.val z * a.val z :=
      congrArg (fun d : R => d.val z) r.cross
    let d := c.val z
    let e := q.denominator.val z
    let a₀ := a.val z
    let b₀ := b.val z
    let a₁ := r.numerator.val z
    let b₁ := r.denominator.val z
    change (d * b₀) • (a₁ • q.numerator z) = (e * b₁) • (a₀ • N z)
    calc
      _ = (b₀ * a₁) • (d • q.numerator z) := by
        simp only [smul_smul]
        congr 1
        ring
      _ = (b₁ * a₀) • (e • N z) := congrArg₂ (· • ·) hrs (q.cross z)
      _ = _ := by
        simp only [smul_smul]
        congr 1
        ring

end RationalOperatorPolePresentation
end Langlands.Plancherel
