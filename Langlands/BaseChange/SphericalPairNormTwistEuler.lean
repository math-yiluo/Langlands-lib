import Langlands.BaseChange.PadicCharacterNormFactors
import Langlands.Correspondence.SphericalPairTwistLPolynomial
import Langlands.LocalFactor.Abelian.UnramifiedTwist

/-! # Euler comparison at spherical pairs under norm pullback -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.BaseChange

open Correspondence LocalClassField Unramified
open Global.CuspidalPairFunctionalEquation (pairEulerPolynomial_ofTuple)
open LocalFactor.PadicAbelian (lPolynomial)
open _root_.Polynomial
open scoped BigOperators

section SphericalPolynomial

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology

private theorem sphericalPairPolynomial_eq_characterProduct {r t : ℕ}
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν)
    (A A' : AutomorphicObject.{u,u} K r.succPNat) (B : AutomorphicObject.{u,u} K t.succPNat)
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ)
    (ha : HasSphericalSpectrum K A (Eigenvalues.ofTuple a))
    (hb : HasSphericalSpectrum K B (Eigenvalues.ofTuple b))
    (μ : QuasiCharacter K) (hμ : IsCharacterTwist K μ (automorphicClassOf K A) (automorphicClassOf K A'))
    (Q : Polynomial ℂ)
    (hQ : IsAutomorphicPairLPolynomial K ψ ν (automorphicClassOf K A') (automorphicClassOf K B) Q) :
    Q = ∏ i, ∏ j, lPolynomial K.canonicalTopologicalData (μ * character K (a i * b j)) := by
  classical
  let T := K.canonicalTopologicalData
  have hcond (z : ℂˣ) : K.canonicalTopologicalData.multiplicativeConductor (μ * character K z) =
      K.canonicalTopologicalData.multiplicativeConductor μ :=
    T.multiplicativeConductor_mul_unramified μ _ ((T.multiplicativeConductor_eq_zero_iff _).mp
      (multiplicativeConductor_character K z))
  have h := sphericalPairTwistLPolynomial p K ψ ν hν A A' B _ _ ha hb μ hμ Q hQ
  rw [h]
  by_cases hzero : K.canonicalTopologicalData.multiplicativeConductor μ = 0
  · simp only [hzero, ite_true, pairEulerPolynomial_ofTuple, prod_comp]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    rw [lPolynomial, hcond, ite_eq_left hzero]
    simp only [ContinuousMonoidHom.mul_apply, character_uniformizer, Units.val_mul,
      sub_comp, one_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_comm ((a i : ℂ) * (b j : ℂ))]
  · simp [hzero, lPolynomial, hcond]

end SphericalPolynomial

/-- For two spherical actions in each field with both spectra related by
residue-degree powers, twisting one upper action by the norm pullback of a
quasicharacter corresponds to the product over all norm-character twists of
that quasicharacter on the first lower action. -/
def SphericalPairNormTwistEulerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := E.canonicalTopologicalData.valuativeRel
    ∀ (f r t : ℕ), IsResidueDegree F.Carrier E.Carrier f →
    ∀ (ψF : NontrivialAdditiveCharacter F) (ψE : NontrivialAdditiveCharacter E)
      (νF : LocalAdditiveHaarMeasure F) (νE : LocalAdditiveHaarMeasure E),
      IsSelfDualMeasure F ψF νF → IsSelfDualMeasure E ψE νE →
    ∀ (X : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ X ↔ IsNormTrivial E.Carrier κ) →
    ∀ (μ : QuasiCharacter F) (ω : X → QuasiCharacter F),
      (∀ κ, (ω κ).toMonoidHom = κ.val) →
    ∀ (A : AutomorphicObject.{u,u} F r.succPNat) (B : AutomorphicObject.{u,u} F t.succPNat)
      (C C' : AutomorphicObject.{v,v} E r.succPNat) (D : AutomorphicObject.{v,v} E t.succPNat)
      (A' : X → AutomorphicObject.{u,u} F r.succPNat)
      (a : Eigenvalues (r + 1)) (b : Eigenvalues (t + 1)),
      HasSphericalSpectrum F A a → HasSphericalSpectrum F B b →
      HasSphericalSpectrum E C (a.power f) → HasSphericalSpectrum E D (b.power f) →
      (∀ κ, IsCharacterTwist F (ω κ * μ) (automorphicClassOf F A) (automorphicClassOf F (A' κ))) →
      IsCharacterTwist E (μ.comp (localNorm F.canonicalTopologicalData E.canonicalTopologicalData))
        (automorphicClassOf E C) (automorphicClassOf E C') →
    ∀ (PF : X → Polynomial ℂ) (PE : Polynomial ℂ),
      (∀ κ, IsAutomorphicPairLPolynomial F ψF νF
        (automorphicClassOf F (A' κ)) (automorphicClassOf F B) (PF κ)) →
      IsAutomorphicPairLPolynomial E ψE νE (automorphicClassOf E C') (automorphicClassOf E D) PE →
      (∏ κ : X, PF κ) = PE.comp (Polynomial.X ^ f)

/-- Regroup the product over norm characters into one abelian norm comparison
for each pair of Satake eigenvalues. -/
theorem sphericalPairNormTwistEuler : SphericalPairNormTwistEulerStatement.{u,v} := by
  classical
  intro p _ F E _ _ _
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  intro f r t hf ψF ψE νF νE hνF hνE X hX μ ω hω A B C C' D A' a b ha hb hc hd htw hnorm PF PE hPF hPE
  obtain ⟨a, rfl⟩ := Eigenvalues.ofTuple_surjective (r + 1) a
  obtain ⟨b, rfl⟩ := Eigenvalues.ofTuple_surjective (t + 1) b
  let N := localNorm T S
  let η := μ.comp N
  let α (i : Fin (r + 1)) (j : Fin (t + 1)) := μ * character F (a i * b j)
  let β (i : Fin (r + 1)) (j : Fin (t + 1)) := η * character E ((a i * b j) ^ f)
  let ξ (i : Fin (r + 1)) (j : Fin (t + 1)) (κ : X) := (ω κ * μ) * character F (a i * b j)
  have hξ (i) (j) (κ : X) : (ξ i j κ).toMonoidHom = κ.val * (α i j).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change (ω κ).toMonoidHom x * μ x * character F (a i * b j) x =
      κ.val x * (μ x * character F (a i * b j) x)
    rw [hω κ, mul_assoc]
  have hα (i) (j) : (α i j).comp N = β i j := by
    apply ContinuousMonoidHom.ext
    intro x
    change μ (N x) * character F (a i * b j) (N x) =
      μ (N x) * character E ((a i * b j) ^ f) x
    rw [character_apply, character_apply, ord_localNorm_eq_residueDegree_mul T S hf,
      zpow_mul, zpow_natCast]
  have hfactors (κ : X) : PF κ = ∏ i, ∏ j, lPolynomial T (ξ i j κ) :=
    sphericalPairPolynomial_eq_characterProduct F ψF νF hνF A (A' κ) B a b ha hb _ (htw κ) _ (hPF κ)
  simp only [Eigenvalues.power_ofTuple] at hc hd
  have hupper : PE = ∏ i, ∏ j, lPolynomial S (β i j) := by
    simpa only [β, mul_pow] using sphericalPairPolynomial_eq_characterProduct E ψE νE hνE C C' D
      (fun i => a i ^ f) (fun j => b j ^ f) hc hd η hnorm PE hPE
  have habel (i) (j) : (∏ κ : X, lPolynomial T (ξ i j κ)) =
      expand ℂ f (lPolynomial S (β i j)) := by
    have h := prod_lPolynomial_normTwists T S hf (α i j) X hX (ξ i j) (hξ i j)
    rwa [hα i j] at h
  calc
    (∏ κ : X, PF κ) = ∏ κ : X, ∏ i, ∏ j, lPolynomial T (ξ i j κ) := by simp_rw [hfactors]
    _ = ∏ i, ∏ κ : X, ∏ j, lPolynomial T (ξ i j κ) := Finset.prod_comm
    _ = ∏ i, ∏ j, ∏ κ : X, lPolynomial T (ξ i j κ) :=
      Finset.prod_congr rfl fun _ _ => Finset.prod_comm
    _ = expand ℂ f PE := by simp only [habel, hupper, map_prod]
    _ = _ := expand_eq_comp_X_pow f

end Langlands.BaseChange
