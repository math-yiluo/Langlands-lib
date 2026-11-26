import Langlands.BaseChange.PadicCharacterNormFactors
import Langlands.Correspondence.SphericalStandardTwistFactors

/-! # Spherical standard factors after a common norm twist -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis LocalClassField RankinSelberg Unramified
open LocalFactor.PadicAbelian (epsilonExponent lPolynomial)
open _root_.Polynomial
open scoped BigOperators

universe u v uA

local instance sphericalNormTwistTopology {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

private theorem classFactors_of_sphericalTwist {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) {r : ℕ} (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖) (ω : QuasiCharacter F)
    (J Jω : AutomorphicObject.{u, max u uA} F r.succPNat) (J₁ : AutomorphicObject.{u, max u uA} F 1)
    (hJ : (unramifiedDatum.{u, max u uA} F z hz).IsLanglandsQuotient J.obj)
    (e : Nonempty ((twist (determinantQuasiCharacter F r.succPNat ω)
        J.obj.representation).Equiv Jω.obj.representation))
    (e₁ : Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁.obj.representation))
    {P : ℂ[X]} {b : ℂˣ × ℤ}
    (hP : IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F Jω) (automorphicClassOf F J₁) P)
    (hb : IsAutomorphicPairEpsilonFactor F ψ ν (automorphicClassOf F Jω) (automorphicClassOf F J₁) b) :
    letI := F.canonicalTopologicalData.topology
    P = (∏ i, lPolynomial F.canonicalTopologicalData (character F (z i) * ω)) ∧
      b.2 = ∑ i, epsilonExponent F.canonicalTopologicalData (character F (z i) * ω) ψ := by
  let a := Representation.Equiv.refl Jω.obj.representation
  let a₁ := Representation.Equiv.refl J₁.obj.representation
  exact sphericalStandardTwistFactors.{u, max u uA, max u uA} p F r ψ ν hν z hz ω J.obj Jω.obj J₁.obj hJ e e₁
    P b ((isAutomorphicPairLPolynomial_iff F Jω J₁ Jω.obj J₁.obj a a₁).mp hP)
    ((isAutomorphicPairEpsilonFactor_iff F Jω J₁ Jω.obj J₁.obj a a₁).mp hb)

private theorem prod_eq_ofTuple_eq {r : ℕ} {M : Type*} [CommMonoid M]
    {a b : Fin r → ℂˣ} (h : Eigenvalues.ofTuple a = Eigenvalues.ofTuple b) (g : ℂˣ → M) :
    (∏ i, g (a i)) = ∏ i, g (b i) := by
  have hp := congrArg (fun s : Eigenvalues r => ((s : Multiset ℂˣ).map g).prod) h
  simpa [Eigenvalues.ofTuple, List.map_ofFn, Function.comp_def, Fin.prod_ofFn] using hp

private theorem sum_eq_ofTuple_eq {r : ℕ} {M : Type*} [AddCommMonoid M]
    {a b : Fin r → ℂˣ} (h : Eigenvalues.ofTuple a = Eigenvalues.ofTuple b) (g : ℂˣ → M) :
    (∑ i, g (a i)) = ∑ i, g (b i) :=
  prod_eq_ofTuple_eq (M := Multiplicative M) h (fun z => Multiplicative.ofAdd (g z))

/-- The standard factors of the lower twists by a common character times
all norm-trivial characters match those of the upper norm-pullback twist. -/
def SphericalNormDeterminantTwistFactorsStatement : Prop :=
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
    ∀ (χ : QuasiCharacter F) (A : Finset (F.Carrierˣ →* ℂˣ)),
      (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (ω : A → QuasiCharacter F), (∀ κ : A, (ω κ).toMonoidHom = κ.val * χ.toMonoidHom) →
    ∀ (JF : AutomorphicObject.{u, max u uA} F r.succPNat)
      (JE JEχ : AutomorphicObject.{v, max v uA} E r.succPNat) (s : Eigenvalues (r + 1)),
      HasSphericalSpectrum F JF s → HasSphericalSpectrum E JE (s.power f) →
    ∀ (Jω : A → AutomorphicObject.{u, max u uA} F r.succPNat),
      (∀ κ, Nonempty ((twist (determinantQuasiCharacter F r.succPNat (ω κ))
        JF.obj.representation).Equiv (Jω κ).obj.representation)) →
    let χE := χ.comp (localNorm F.canonicalTopologicalData E.canonicalTopologicalData)
    Nonempty ((twist (determinantQuasiCharacter E r.succPNat χE) JE.obj.representation).Equiv
      JEχ.obj.representation) →
    ∀ (J₁F : AutomorphicObject.{u, max u uA} F 1) (J₁E : AutomorphicObject.{v, max v uA} E 1),
      Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv J₁F.obj.representation) →
      Nonempty ((rankOneCharacter (1 : E.Carrierˣ →* ℂˣ)).Equiv J₁E.obj.representation) →
    ∀ (PF : A → ℂ[X]) (PE : ℂ[X]) (bF : A → ℂˣ × ℤ) (bE : ℂˣ × ℤ),
      (∀ κ, IsAutomorphicPairLPolynomial F ψF νF (automorphicClassOf F (Jω κ))
        (automorphicClassOf F J₁F) (PF κ)) →
      IsAutomorphicPairLPolynomial E ψE νE (automorphicClassOf E JEχ) (automorphicClassOf E J₁E) PE →
      (∀ κ, IsAutomorphicPairEpsilonFactor F ψF νF (automorphicClassOf F (Jω κ))
        (automorphicClassOf F J₁F) (bF κ)) →
      IsAutomorphicPairEpsilonFactor E ψE νE (automorphicClassOf E JEχ) (automorphicClassOf E J₁E) bE →
      (∏ κ : A, PF κ) = expand ℂ f PE ∧ (∑ κ : A, (bF κ).2) = (f : ℤ) * bE.2

set_option maxHeartbeats 1800000 in
theorem sphericalNormDeterminantTwistFactors : SphericalNormDeterminantTwistFactorsStatement.{u, v, uA} := by
  intro p _ F E _ _ _ _
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TE.topology
  let := TF.valuativeRel
  let := TE.valuativeRel
  intro _ f d r hf hd ψF ψE htrace νF νE hνF hνE χ A hA ω hω JF JE JEχ s hsF hsE Jω ht χE htE
    J₁F J₁E h₁F h₁E PF PE bF bE hPF hPE hbF hbE
  obtain ⟨a, ha, haS, hJF⟩ := exists_unramifiedDatum_isLanglandsQuotient.{u, max u uA}
    F JF JF.obj (Representation.Equiv.refl _) s hsF
  obtain ⟨b, hb, hbS, hJE⟩ := exists_unramifiedDatum_isLanglandsQuotient.{v, max v uA}
    E JE JE.obj (Representation.Equiv.refl _) (s.power f) hsE
  have htuple : Eigenvalues.ofTuple b = Eigenvalues.ofTuple (fun i => a i ^ f) := by
    rw [hbS, ← haS, Eigenvalues.power_ofTuple]
  have hF (κ : A) := classFactors_of_sphericalTwist F ψF νF hνF a ha (ω κ)
    JF (Jω κ) J₁F hJF (ht κ) h₁F (hPF κ) (hbF κ)
  obtain ⟨hE, heE⟩ := classFactors_of_sphericalTwist E ψE νE hνE b hb χE JE JEχ J₁E hJE htE h₁E hPE hbE
  have hNorm (z : ℂˣ) : ((character F z) * χ).comp (localNorm TF TE) = character E (z ^ f) * χE := by
    apply ContinuousMonoidHom.ext
    intro x
    change character F z (localNorm TF TE x) * χ (localNorm TF TE x) =
      character E (z ^ f) x * χ (localNorm TF TE x)
    rw [character_apply, character_apply, ord_localNorm_eq_residueDegree_mul TF TE hf,
      zpow_mul, zpow_natCast]
  have h₀ (i : Fin (r + 1)) := padicCharacterNormFactors p F E TF TE f d hf hd ψF ψE htrace
    (character F (a i) * χ) A hA (fun κ => character F (a i) * ω κ) (fun κ => by
      apply MonoidHom.ext
      intro x
      change character F (a i) x * (ω κ).toMonoidHom x =
        κ.val x * (character F (a i) x * χ.toMonoidHom x)
      rw [hω κ, MonoidHom.mul_apply]
      exact mul_left_comm _ _ _)
  have hPE' : (∏ i, lPolynomial TE (character E (a i ^ f) * χE)) = PE :=
    (prod_eq_ofTuple_eq htuple (fun z => lPolynomial TE (character E z * χE))).symm.trans hE.symm
  have hbE' : (∑ i, epsilonExponent TE (character E (a i ^ f) * χE) ψE) = bE.2 :=
    (sum_eq_ofTuple_eq htuple (fun z => epsilonExponent TE (character E z * χE) ψE)).symm.trans heE.symm
  constructor
  · calc
      _ = ∏ i, ∏ κ : A, lPolynomial TF (character F (a i) * ω κ) := by
        simp_rw [fun κ => (hF κ).1]
        exact Finset.prod_comm
      _ = ∏ i, expand ℂ f (lPolynomial TE (character E (a i ^ f) * χE)) := by
        apply Finset.prod_congr rfl
        intro i _
        simpa only [hNorm] using (h₀ i).1
      _ = _ := by rw [← map_prod, hPE']
  · calc
      _ = ∑ i, ∑ κ : A, epsilonExponent TF (character F (a i) * ω κ) ψF := by
        simp_rw [fun κ => (hF κ).2]
        exact Finset.sum_comm
      _ = ∑ i, (f : ℤ) * epsilonExponent TE (character E (a i ^ f) * χE) ψE := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [hNorm] using (h₀ i).2
      _ = _ := by rw [← Finset.mul_sum, hbE']

end Langlands.BaseChange
