import Langlands.BaseChange.PadicNormTwistFactorComparison
import Langlands.Correspondence.SphericalStandardTwistFactors
import Langlands.Representation.Twist.AlgebraProof

/-! # Auxiliary standard factors for spherical norm base change -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis LocalClassField RankinSelberg Unramified
open _root_.Polynomial
open LocalFactor.PadicAbelian (epsilonExponent lPolynomial)

universe u v uA

section RankOne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]

local notation "TF" => F.canonicalTopologicalData
local notation "TE" => E.canonicalTopologicalData

local instance : TopologicalSpace F.Carrier := (TF).topology
local instance : TopologicalSpace E.Carrier := (TE).topology
local instance : ValuativeRel F.Carrier := (TF).valuativeRel
local instance : ValuativeRel E.Carrier := (TE).valuativeRel

private theorem unramifiedCharacter_comp_localNorm {f : ℕ}
    (hf : IsResidueDegree F.Carrier E.Carrier f) (a : ℂˣ) :
    (character F a).comp (localNorm TF TE) = character E (a ^ f) := by
  apply ContinuousMonoidHom.ext
  intro x
  change character F a (localNorm TF TE x) = character E (a ^ f) x
  rw [character_apply, character_apply, ord_localNorm_eq_residueDegree_mul TF TE hf,
    zpow_mul, zpow_natCast]

variable [IsModuleTopology F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]

private theorem rankOne_normTwistFactors {f d : ℕ}
    (hf : IsResidueDegree F.Carrier E.Carrier f) (hd : IsDifferentExponent F.Carrier E.Carrier d)
    (ψF : NontrivialAdditiveCharacter F) (ψE : NontrivialAdditiveCharacter E)
    (htrace : ∀ x : E.Carrier, ψE x = ψF (Algebra.trace F.Carrier E.Carrier x))
    (A : Finset (F.Carrierˣ →* ℂˣ)) (hA : ∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ)
    (ω : A → QuasiCharacter F) (hω : ∀ κ : A, (ω κ).toMonoidHom = κ.val) (a : ℂˣ) :
    (∏ κ : A, lPolynomial TF (character F a * ω κ)) =
      expand ℂ f (lPolynomial TE (character E (a ^ f))) ∧
    (∑ κ : A, epsilonExponent TF (character F a * ω κ) ψF) =
      (f : ℤ) * epsilonExponent TE (character E (a ^ f)) ψE := by
  obtain ⟨ξ, hξ, -, he⟩ := padicNormTwistFactorComparison p F E TF TE f d hf hd ψF ψE htrace
    (character F a) (character_isUnramified F a) A hA
  have hξeq (κ : A) : ξ κ = character F a * ω κ := by
    apply ContinuousMonoidHom.toMonoidHom_injective
    change (ξ κ).toMonoidHom = (character F a).toMonoidHom * (ω κ).toMonoidHom
    rw [hξ κ, hω κ]
    exact MonoidHom.ext fun _ => mul_comm _ _
  have hP := prod_lPolynomial_unramifiedNormTwists TF TE hf (character F a)
    (character_isUnramified F a) A hA ξ hξ
  rw [unramifiedCharacter_comp_localNorm F E hf a] at hP he
  exact ⟨by simpa only [hξeq] using hP, by simpa only [hξeq] using he⟩

end RankOne

section Spherical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

private theorem classStandardFactors_of_sphericalTwist {r : ℕ}
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖) (ω : QuasiCharacter F)
    (J Jω : AutomorphicObject.{u, max u uA} F r.succPNat) (J₁ : AutomorphicObject.{u, max u uA} F 1)
    (hJ : (unramifiedDatum.{u, max u uA} F z hz).IsLanglandsQuotient J.obj)
    (e : Nonempty ((Langlands.twist (determinantQuasiCharacter F r.succPNat ω)
        J.obj.representation).Equiv Jω.obj.representation))
    (e₁ : Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.obj.representation))
    {P : ℂ[X]} {b : ℂˣ × ℤ}
    (hP : IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F Jω) (automorphicClassOf F J₁) P)
    (hb : IsAutomorphicPairEpsilonFactor F ψ ν (automorphicClassOf F Jω) (automorphicClassOf F J₁) b) :
    P = (∏ i, lPolynomial F.canonicalTopologicalData (character F (z i) * ω)) ∧
      b.2 = ∑ i, epsilonExponent F.canonicalTopologicalData (character F (z i) * ω) ψ := by
  let a := Representation.Equiv.refl Jω.obj.representation
  let a₁ := Representation.Equiv.refl J₁.obj.representation
  exact sphericalStandardTwistFactors.{u, max u uA, max u uA} p F r ψ ν hν z hz ω J.obj Jω.obj J₁.obj hJ e e₁
    P b ((isAutomorphicPairLPolynomial_iff F Jω J₁ Jω.obj J₁.obj a a₁).mp hP)
    ((isAutomorphicPairEpsilonFactor_iff F Jω J₁ Jω.obj J₁.obj a a₁).mp hb)

private theorem classStandardFactors_of_unramifiedDatum {r : ℕ}
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F ψ ν)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖)
    (J : AutomorphicObject.{u, max u uA} F r.succPNat) (J₁ : AutomorphicObject.{u, max u uA} F 1)
    (hJ : (unramifiedDatum.{u, max u uA} F z hz).IsLanglandsQuotient J.obj)
    (e₁ : Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.obj.representation))
    {P : ℂ[X]} {b : ℂˣ × ℤ}
    (hP : IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F J) (automorphicClassOf F J₁) P)
    (hb : IsAutomorphicPairEpsilonFactor F ψ ν (automorphicClassOf F J) (automorphicClassOf F J₁) b) :
    P = Eigenvalues.eulerPolynomial (Eigenvalues.ofTuple z) ∧
      b.2 = ∑ _ : Fin (r + 1), F.canonicalTopologicalData.additiveConductor ψ := by
  have hdet : determinantQuasiCharacter F r.succPNat 1 = 1 := MonoidHom.ext fun _ => rfl
  have ht : Langlands.twist (determinantQuasiCharacter F r.succPNat 1) J.obj.representation =
      J.obj.representation := by rw [hdet, Langlands.twist_one]
  have h := classStandardFactors_of_sphericalTwist F ψ ν hν z hz 1 J J J₁ hJ
    ⟨equivOfRepresentationEq ht⟩ e₁ hP hb
  have hmul (i : Fin (r + 1)) : character F (z i) * (1 : QuasiCharacter F) = character F (z i) :=
    ContinuousMonoidHom.ext fun x => mul_one (character F (z i) x)
  simpa only [hmul, lPolynomial_character, Eigenvalues.eulerPolynomial_ofTuple, epsilonExponent,
    multiplicativeConductor_character, Nat.cast_zero, zero_add] using h

end Spherical

/-- With the spherical spectra related by residue-degree powers, the actual
standard Euler denominators and epsilon exponents at a field place match the
product over all norm-trivial determinant twists of the base component. -/
def SphericalNormTwistFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := E.canonicalTopologicalData.valuativeRel
    ∀ [IsModuleTopology F.Carrier E.Carrier] (f d r : ℕ),
      IsResidueDegree F.Carrier E.Carrier f → IsDifferentExponent F.Carrier E.Carrier d →
    ∀ (ψF : NontrivialAdditiveCharacter F) (ψE : NontrivialAdditiveCharacter E),
      (∀ x : E.Carrier, ψE x = ψF (Algebra.trace F.Carrier E.Carrier x)) →
    ∀ (νF : LocalAdditiveHaarMeasure F) (νE : LocalAdditiveHaarMeasure E),
      IsSelfDualMeasure F ψF νF → IsSelfDualMeasure E ψE νE →
    ∀ (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (ω : A → QuasiCharacter F), (∀ κ : A, (ω κ).toMonoidHom = κ.val) →
    ∀ (JF : AutomorphicObject.{u, max u uA} F r.succPNat) (JE : AutomorphicObject.{v, max v uA} E r.succPNat)
      (s : Eigenvalues (r + 1)),
      HasSphericalSpectrum F JF s → HasSphericalSpectrum E JE (s.power f) →
    ∀ (Jω : A → AutomorphicObject.{u, max u uA} F r.succPNat),
      (∀ κ, Nonempty ((Langlands.twist (determinantQuasiCharacter F r.succPNat (ω κ))
        JF.obj.representation).Equiv (Jω κ).obj.representation)) →
    ∀ (J₁F : AutomorphicObject.{u, max u uA} F 1) (J₁E : AutomorphicObject.{v, max v uA} E 1),
      Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁F.obj.representation) →
      Nonempty ((rankOneCharacter (1 : E.Carrierˣ →* ℂˣ)).Equiv J₁E.obj.representation) →
    ∀ (PF : A → ℂ[X]) (PE : ℂ[X]) (bF : A → ℂˣ × ℤ) (bE : ℂˣ × ℤ),
      (∀ κ, IsAutomorphicPairLPolynomial F ψF νF (automorphicClassOf F (Jω κ))
        (automorphicClassOf F J₁F) (PF κ)) →
      IsAutomorphicPairLPolynomial E ψE νE (automorphicClassOf E JE) (automorphicClassOf E J₁E) PE →
      (∀ κ, IsAutomorphicPairEpsilonFactor F ψF νF (automorphicClassOf F (Jω κ))
        (automorphicClassOf F J₁F) (bF κ)) →
      IsAutomorphicPairEpsilonFactor E ψE νE (automorphicClassOf E JE) (automorphicClassOf E J₁E) bE →
      (∏ κ : A, PF κ) = expand ℂ f PE ∧ (∑ κ : A, (bF κ).2) = (f : ℤ) * bE.2

set_option maxHeartbeats 1200000 in
/-- Multiply the rank-one norm comparisons over the spherical inducing data. -/
theorem sphericalNormTwistFactors : SphericalNormTwistFactorsStatement.{u, v, uA} := by
  intro p _ F E _ _ _ _
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TE.topology
  let := TF.valuativeRel
  let := TE.valuativeRel
  intro _ f d r hf hd ψF ψE htrace νF νE hνF hνE A hA ω hω JF JE s hsF hsE Jω ht
    J₁F J₁E h₁F h₁E PF PE bF bE hPF hPE hbF hbE
  obtain ⟨zF, hzF, hzFs, hJF⟩ := exists_unramifiedDatum_isLanglandsQuotient.{u, max u uA}
    F JF JF.obj (Representation.Equiv.refl _) s hsF
  obtain ⟨zE, hzE, hzEs, hJE⟩ := exists_unramifiedDatum_isLanglandsQuotient.{v, max v uA}
    E JE JE.obj (Representation.Equiv.refl _) (s.power f) hsE
  have hF (κ : A) := classStandardFactors_of_sphericalTwist F ψF νF hνF zF hzF (ω κ)
    JF (Jω κ) J₁F hJF (ht κ) h₁F (hPF κ) (hbF κ)
  obtain ⟨hE, heE⟩ := classStandardFactors_of_unramifiedDatum E ψE νE hνE zE hzE JE J₁E
    hJE h₁E hPE hbE
  have h₀ (i : Fin (r + 1)) := rankOne_normTwistFactors F E hf hd ψF ψE htrace A hA ω hω (zF i)
  have hPE' : (∏ i, lPolynomial TE (character E (zF i ^ f))) = PE := by
    change (∏ i, lPolynomial E.canonicalTopologicalData (character E (zF i ^ f))) = PE
    rw [hE, hzEs, ← hzFs, Eigenvalues.power_ofTuple, Eigenvalues.eulerPolynomial_ofTuple]
    simp only [lPolynomial_character]
  have hbE' : (∑ i, epsilonExponent TE (character E (zF i ^ f)) ψE) = bE.2 := by
    change (∑ i, epsilonExponent E.canonicalTopologicalData (character E (zF i ^ f)) ψE) = bE.2
    simp only [epsilonExponent, multiplicativeConductor_character, Nat.cast_zero, zero_add, heE]
  constructor
  · calc
      _ = ∏ i, ∏ κ : A, lPolynomial TF (character F (zF i) * ω κ) := by
        simp_rw [fun κ => (hF κ).1]
        exact Finset.prod_comm
      _ = ∏ i, expand ℂ f (lPolynomial TE (character E (zF i ^ f))) :=
        Finset.prod_congr rfl fun i _ => (h₀ i).1
      _ = _ := by rw [← map_prod, hPE']
  · calc
      _ = ∑ i, ∑ κ : A, epsilonExponent TF (character F (zF i) * ω κ) ψF := by
        simp_rw [fun κ => (hF κ).2]
        exact Finset.sum_comm
      _ = ∑ i, (f : ℤ) * epsilonExponent TE (character E (zF i ^ f)) ψE :=
        Finset.sum_congr rfl fun i _ => (h₀ i).2
      _ = _ := by rw [← Finset.mul_sum, hbE']

end Langlands.BaseChange
