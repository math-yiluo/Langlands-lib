import Langlands.BaseChange.SphericalNormDeterminantTwistFactors
import Langlands.BaseChange.StandardTwistFactorsAtCompletion
import Langlands.BaseChange.AuxiliaryFactorProductComparison

/-! # Finite auxiliary standard factors after simultaneous norm twists -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 5000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.BaseChange

open Automorphic Correspondence GeneralLinear Global Global.CompletionPadic Global.AdelicFunctoriality
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation Global.FunctionalEquationComparison
open ClassFieldTheory.Global.RelativeWeilGroup
open HarmonicAnalysis LocalClassField RankinSelberg Unramified
open LocalFactor.PadicAbelian (epsilonExponent)
open _root_.Polynomial
open scoped BigOperators Classical NumberField FiniteExtension

universe u uI

section AtPrime

variable {L : Type u} [Field L] [NumberField L] (w : FinitePlace L) {p : ℕ} [Fact p.Prime]
  (h : residuePrime w = p) {r : ℕ}
  (J : AutomorphicObject.{u, u} (padicField w) r.succPNat)
  (ξ : (w.adicCompletion L)ˣ →ₜ* ℂˣ)

private def objectAtPrime : AutomorphicObject.{u, u} (padicFieldAt w h) r.succPNat := by
  subst p
  exact J

private def standardAdditiveAtPrime : NontrivialAdditiveCharacter (padicFieldAt w h) := by
  subst p
  exact standardFiniteAdditiveComponent L w

private theorem standardAdditiveAtPrime_apply (x : w.adicCompletion L) :
    standardAdditiveAtPrime w h x = standardFiniteAdditiveComponent L w x := by
  subst p
  rfl

private theorem objectAtPrime_spherical (s : Eigenvalues (r + 1))
    (hs : HasSphericalSpectrum (padicField w) J s) :
    HasSphericalSpectrum (padicFieldAt w h) (objectAtPrime w h J) s := by
  subst p
  exact hs

private def twistChoiceAtPrime
    (c : StandardTwistFactorChoice (padicField w) (standardFiniteAdditiveComponent L w) J
      (quasicharacterBase w ξ)) :
    StandardTwistFactorChoice (padicFieldAt w h) (standardAdditiveAtPrime w h) (objectAtPrime w h J)
      (quasicharacterAt w h ξ) := by
  subst p
  exact c

private theorem twistChoiceAtPrime_lPolynomial
    (c : StandardTwistFactorChoice (padicField w) (standardFiniteAdditiveComponent L w) J
      (quasicharacterBase w ξ)) : (twistChoiceAtPrime w h J ξ c).lPolynomial = c.lPolynomial := by
  subst p
  rfl

private theorem twistChoiceAtPrime_epsilon
    (c : StandardTwistFactorChoice (padicField w) (standardFiniteAdditiveComponent L w) J
      (quasicharacterBase w ξ)) : (twistChoiceAtPrime w h J ξ c).epsilon = c.epsilon := by
  subst p
  rfl

private theorem epsilonExponentAtPrime :
    epsilonExponent (padicFieldAt w h).canonicalTopologicalData (quasicharacterAt w h ξ)
        (standardAdditiveAtPrime w h) =
      epsilonExponent (padicField w).canonicalTopologicalData (quasicharacterBase w ξ)
        (standardFiniteAdditiveComponent L w) := by
  subst p
  rfl

end AtPrime

section Values

private theorem prod_of_fiber_card {I A M : Type*} [Fintype I] [Fintype A]
    [DecidableEq A] [CommMonoid M] (res : I → A) (d : ℕ)
    (hres : ∀ a, Fintype.card {i // res i = a} = d) (g : A → M) :
    (∏ i, g (res i)) = (∏ a, g a) ^ d := by
  rw [← Fintype.prod_fiberwise' res g, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a _ => by simp [hres a]

/-- The residue-degree substitution and an exponent identity at each
upper place give the products of finite Euler values and positive epsilon bases. -/
private theorem groupedAuxiliaryValues {I A W : Type*} [Fintype I] [Fintype A] [Fintype W]
    [DecidableEq A] (res : I → A) (hres : ∀ a, Fintype.card {i // res i = a} = Fintype.card W)
    {q : ℕ} (hq : 0 < q) (q' f : W → ℕ) (hq' : ∀ w, q' w = q ^ f w)
    (P : A → ℂ[X]) (Q : W → ℂ[X]) (b : A → ℂˣ × ℤ) (e : W → ℂˣ × ℤ)
    (hP : ∀ w, (∏ a, P a) = expand ℂ (f w) (Q w))
    (hb : ∀ w, (∑ a, (b a).2) = (f w : ℤ) * (e w).2) :
    (∀ z : ℂ, (∏ i, ((P (res i)).eval (spectralPoint q z))⁻¹) =
      ∏ w, ((Q w).eval (spectralPoint (q' w) z))⁻¹) ∧
    finiteEpsilonBase Finset.univ (fun _ : I => q) (b ∘ res) =
      finiteEpsilonBase Finset.univ q' e := by
  classical
  have hc (a : A) : Fintype.card {x : A // id x = a} = Fintype.card Unit := by
    let ei : {x : A // id x = a} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨a, rfl⟩
        left_inv := fun x => Subtype.ext x.property.symm
        right_inv := fun _ => rfl }
    exact Fintype.card_congr ei
  have hlocal (w : W) := auxiliaryFactorProductComparison A A Unit id hc q (q' w) (f w) hq (hq' w)
    P (Q w) P (fun _ => Q w) (fun a => (b a).2) (e w).2 b (fun _ => e w) (hP w) (hb w)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro z
    let g (a : A) := ((P a).eval (spectralPoint q z))⁻¹
    rw [prod_of_fiber_card res _ hres g]
    have hu (w : W) : ((Q w).eval (spectralPoint (q' w) z))⁻¹ = ∏ a, g a := by
      simpa [g] using ((hlocal w).1 z).symm
    simp_rw [hu, Finset.prod_const, Finset.card_univ]
  · simp only [finiteEpsilonBase, Function.comp_apply]
    rw [prod_of_fiber_card res _ hres (fun a => (q : ℝ) ^ (b a).2)]
    have hu (w : W) : (q' w : ℝ) ^ (e w).2 = ∏ a, (q : ℝ) ^ (b a).2 := by
      simpa [finiteEpsilonBase] using (hlocal w).2.symm
    simp_rw [hu, Finset.prod_const, Finset.card_univ]

end Values

section Local

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : FinitePlace K) (w : FinitePlacesAbove L v)


set_option maxHeartbeats 1500000 in
/-- The character in the common p-adic tower is the local norm pullback of
the lower finite component. -/
theorem quasicharacterAt_normComp (ν : HeckeCharacter K) :
    letI := towerPadicField_isScalarTower v w.1
    letI := (padicField v).canonicalTopologicalData.topology
    letI := (CompletionPadic.towerPadicField v w.1).canonicalTopologicalData.topology
    quasicharacterAt w.1 (residuePrime_eq v w.1) ((ν.normComp (L := L)).finiteComponent w.1) =
      (quasicharacterBase v (ν.finiteComponent v)).comp
        (localNorm (padicField v).canonicalTopologicalData (CompletionPadic.towerPadicField v w.1).canonicalTopologicalData) := by
  let := towerPadicField_isScalarTower v w.1
  let := (padicField v).canonicalTopologicalData.topology
  let := (CompletionPadic.towerPadicField v w.1).canonicalTopologicalData.topology
  apply ContinuousMonoidHom.ext
  intro x
  exact ν.normComp_finiteComponent v w x

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] {r : ℕ}
  (A₀ : AutomorphicObject.{u, u} (padicField v) r.succPNat)
  (B₀ : AutomorphicObject.{u, u} (padicField w.1) r.succPNat)
  (ν : HeckeCharacter K)
  (A : Finset ((padicField v).Carrierˣ →* ℂˣ))
  (hA : ∀ κ : (padicField v).Carrierˣ →* ℂˣ, κ ∈ A ↔ IsNormTrivial (CompletionPadic.towerPadicField v w.1).Carrier κ)
  (χ : A → QuasiCharacter (padicField v))
  (hχ : letI := (padicField v).canonicalTopologicalData.topology
    ∀ κ : A, (χ κ).toMonoidHom = κ.val * (quasicharacterBase v (ν.finiteComponent v)).toMonoidHom)
  (cF : ∀ κ : A, StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v) A₀ (χ κ))
  (cE : StandardTwistFactorChoice (padicField w.1) (standardFiniteAdditiveComponent L w.1) B₀
    (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1)))

include hA hχ

set_option maxHeartbeats 3000000 in
private theorem spherical_commonTwistAtUpper (s : Eigenvalues (r + 1))
    (hF : HasSphericalSpectrum (padicField v) A₀ s) (hE : HasSphericalSpectrum (padicField w.1) B₀ (s.power (w.1.asIdeal.inertiaDeg (𝓞 K)))) :
    Finset.prod Finset.univ (fun κ : ↥A => (cF κ).lPolynomial) = expand ℂ (w.1.asIdeal.inertiaDeg (𝓞 K)) cE.lPolynomial ∧
      Finset.sum Finset.univ (fun κ : ↥A => (cF κ).epsilon.2) = ((w.1.asIdeal.inertiaDeg (𝓞 K)) : ℤ) * cE.epsilon.2 := by
  have hscalar := towerPadicField_isScalarTower v w.1
  obtain ⟨htop, hgal, hf, d, hd⟩ := completionRelativeFieldInvariants K L v w.1
  let := hscalar
  let := htop
  let := hgal
  let η := quasicharacterBase v (ν.finiteComponent v)
  let w₀ : A := ⟨1, (hA _).mpr (by intro; rfl)⟩
  let mF := (cF w₀).measure
  have hcert (κ : A) : (cF κ).measure = mF := by
    obtain ⟨_, _, hunique⟩ := existsUnique_selfDualMeasure_standardFiniteAdditiveComponent K v
    exact (hunique _ (cF κ).measure_spec).trans (hunique _ (cF w₀).measure_spec).symm
  let cE' := twistChoiceAtPrime w.1 (residuePrime_eq v w.1) B₀
    ((ν.normComp (L := L)).finiteComponent w.1) cE
  let E := CompletionPadic.towerPadicField v w.1
  let (n : ℕ) : TopologicalSpace (GeneralLinear n E.Carrier) := E.canonicalGeneralLinearTopology n
  let equivFor (ζ : QuasiCharacter E) := Nonempty
    ((twist (determinantQuasiCharacter E r.succPNat ζ)
      (objectAtPrime w.1 (residuePrime_eq v w.1) B₀).obj.representation).Equiv
      cE'.twisted.obj.representation)
  have hEequiv := Eq.mp (congrArg equivFor (quasicharacterAt_normComp v w ν))
    (show equivFor _ from cE'.twistEquiv)
  have htrace (x : (CompletionPadic.towerPadicField v w.1).Carrier) : (standardAdditiveAtPrime w.1 (residuePrime_eq v w.1)) x = (standardFiniteAdditiveComponent K v) (Algebra.trace (padicField v).Carrier (CompletionPadic.towerPadicField v w.1).Carrier x) :=
    (standardAdditiveAtPrime_apply w.1 (residuePrime_eq v w.1) x).trans
      (standardFiniteAdditiveComponent_trace v w.1 x)
  have hdata := sphericalNormDeterminantTwistFactors.{u, u, u} (residuePrime v) (padicField v) (CompletionPadic.towerPadicField v w.1) (w.1.asIdeal.inertiaDeg (𝓞 K)) d r hf hd
    (standardFiniteAdditiveComponent K v) (standardAdditiveAtPrime w.1 (residuePrime_eq v w.1)) htrace mF cE'.measure (cF w₀).measure_spec cE'.measure_spec η A hA χ hχ
    A₀ (objectAtPrime w.1 (residuePrime_eq v w.1) B₀) cE'.twisted s hF
    (objectAtPrime_spherical w.1 (residuePrime_eq v w.1) B₀ _ hE)
    (fun κ => (cF κ).twisted) (fun κ => (cF κ).twistEquiv) hEequiv
    (cF w₀).rankOne cE'.rankOne (cF w₀).trivialEquiv cE'.trivialEquiv
    (fun κ => (cF κ).lPolynomial) cE'.lPolynomial (fun κ => (cF κ).epsilon) cE'.epsilon
  have hRank (κ : A) : automorphicClassOf (padicField v) (cF κ).rankOne = automorphicClassOf (padicField v) (cF w₀).rankOne := by
    obtain ⟨e⟩ := (cF κ).trivialEquiv
    obtain ⟨e₀⟩ := (cF w₀).trivialEquiv
    exact (automorphicClassOf_eq_iff (padicField v) _ _).mpr ⟨e.symm.trans e₀⟩
  have h := hdata (fun κ => hRank κ ▸ hcert κ ▸ (cF κ).lPolynomial_spec) cE'.lPolynomial_spec
    (fun κ => hRank κ ▸ hcert κ ▸ (cF κ).epsilon_spec) cE'.epsilon_spec
  simpa only [cE', twistChoiceAtPrime_lPolynomial, twistChoiceAtPrime_epsilon] using h

set_option maxHeartbeats 3000000 in
private theorem ramified_commonTwistAtUpper
    (hF : letI := (padicField v).canonicalTopologicalData.topology
      ∀ κ : A, (cF κ).lPolynomial = 1 ∧ (cF κ).epsilon.2 = (r + 1 : ℕ) *
      epsilonExponent (padicField v).canonicalTopologicalData (χ κ) (standardFiniteAdditiveComponent K v))
    (hE : letI := (padicField w.1).canonicalTopologicalData.topology
      cE.lPolynomial = 1 ∧ cE.epsilon.2 = (r + 1 : ℕ) *
      epsilonExponent (padicField w.1).canonicalTopologicalData
        (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1)) (standardFiniteAdditiveComponent L w.1)) :
    Finset.prod Finset.univ (fun κ : ↥A => (cF κ).lPolynomial) = expand ℂ (w.1.asIdeal.inertiaDeg (𝓞 K)) cE.lPolynomial ∧
      Finset.sum Finset.univ (fun κ : ↥A => (cF κ).epsilon.2) = ((w.1.asIdeal.inertiaDeg (𝓞 K)) : ℤ) * cE.epsilon.2 := by
  have hscalar := towerPadicField_isScalarTower v w.1
  obtain ⟨htop, hgal, hf, d, hd⟩ := completionRelativeFieldInvariants K L v w.1
  let := hscalar
  let := htop
  let := hgal
  have htrace (x : (CompletionPadic.towerPadicField v w.1).Carrier) : (standardAdditiveAtPrime w.1 (residuePrime_eq v w.1)) x = (standardFiniteAdditiveComponent K v) (Algebra.trace (padicField v).Carrier (CompletionPadic.towerPadicField v w.1).Carrier x) :=
    (standardAdditiveAtPrime_apply w.1 (residuePrime_eq v w.1) x).trans
      (standardFiniteAdditiveComponent_trace v w.1 x)
  have h := (padicCharacterNormFactors (residuePrime v) (padicField v) (CompletionPadic.towerPadicField v w.1) (padicField v).canonicalTopologicalData
    (CompletionPadic.towerPadicField v w.1).canonicalTopologicalData (w.1.asIdeal.inertiaDeg (𝓞 K)) d hf hd (standardFiniteAdditiveComponent K v) (standardAdditiveAtPrime w.1 (residuePrime_eq v w.1)) htrace (quasicharacterBase v (ν.finiteComponent v))
    A hA χ hχ).2
  rw [← quasicharacterAt_normComp v w ν, epsilonExponentAtPrime] at h
  constructor
  · simp [fun κ => (hF κ).1, hE.1]
  · simp_rw [fun κ => (hF κ).2, ← Finset.mul_sum, h, hE.2]
    push_cast
    ring

end Local

section Product

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (v : FinitePlace K) {r : ℕ}


local instance auxiliaryBaseTopology : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology

private theorem standardTwistChoices_eq {A₀ : AutomorphicObject.{u, u} (padicField v) r.succPNat}
    {η η' : QuasiCharacter (padicField v)}
    (a : StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v) A₀ η)
    (b : StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v) A₀ η')
    (hη : η = η') :
    a.lPolynomial = b.lPolynomial ∧ a.epsilon = b.epsilon := by
  subst η'
  obtain ⟨ea⟩ := a.twistEquiv
  obtain ⟨eb⟩ := b.twistEquiv
  obtain ⟨fa⟩ := a.trivialEquiv
  obtain ⟨fb⟩ := b.trivialEquiv
  have htw := (automorphicClassOf_eq_iff (padicField v) _ _).mpr ⟨ea.symm.trans eb⟩
  have htriv := (automorphicClassOf_eq_iff (padicField v) _ _).mpr ⟨fa.symm.trans fb⟩
  obtain ⟨_, _, hmeasure⟩ := existsUnique_selfDualMeasure_standardFiniteAdditiveComponent K v
  have hm := (hmeasure _ a.measure_spec).trans (hmeasure _ b.measure_spec).symm
  have ha := a.lPolynomial_spec
  have he := a.epsilon_spec
  rw [htw, htriv, hm] at ha he
  exact ⟨ha.unique b.lPolynomial_spec, he.unique b.epsilon_spec⟩

variable (I : Type uI) [Fintype I] (κ : I → QuasiCharacter (padicField v))
  (ν : HeckeCharacter K) (A₀ : AutomorphicObject.{u, u} (padicField v) r.succPNat)
  (B₀ : ∀ w : FinitePlacesAbove L v, AutomorphicObject.{u, u} (padicField w.1) r.succPNat)
  (cF : ∀ i, StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v) A₀ (κ i * quasicharacterBase v (ν.finiteComponent v)))
  (cE : ∀ w : FinitePlacesAbove L v,
    StandardTwistFactorChoice (padicField w.1) (standardFiniteAdditiveComponent L w.1) (B₀ w)
      (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1)))

/-- For actual finite standard choices after a common norm twist, compare
Euler products and positive epsilon bases by the spherical or highly ramified
formula. Each local norm character occurs with the upper-place multiplicity. -/
def CommonNormTwistAuxiliaryFactorsStatement : Prop :=
    (∀ (w : FinitePlacesAbove L v) (θ : (padicField v).Carrierˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) θ ↔ ∃ i, (κ i).toMonoidHom = θ) ∧
      (IsNormTrivial (w.1.adicCompletion L) θ →
        Nat.card {i // (κ i).toMonoidHom = θ} = Nat.card (FinitePlacesAbove L v))) →
    (
      (∃ s : Eigenvalues (r + 1), HasSphericalSpectrum (padicField v) A₀ s ∧
        ∀ w, HasSphericalSpectrum (padicField w.1) (B₀ w)
          (s.power (w.1.asIdeal.inertiaDeg (𝓞 K)))) ∨
      ((∀ i, (cF i).lPolynomial = 1 ∧ (cF i).epsilon.2 = (r + 1 : ℕ) *
        epsilonExponent (padicField v).canonicalTopologicalData (κ i * quasicharacterBase v (ν.finiteComponent v)) (standardFiniteAdditiveComponent K v)) ∧
       (∀ w : FinitePlacesAbove L v,
        (cE w).lPolynomial = 1 ∧ (cE w).epsilon.2 = (r + 1 : ℕ) *
          epsilonExponent (padicField w.1).canonicalTopologicalData
            (quasicharacterBase w.1 ((ν.normComp (L := L)).finiteComponent w.1))
            (standardFiniteAdditiveComponent L w.1)))) →
    (∀ z : ℂ, (∏ i, (((cF i).lPolynomial).eval (spectralPoint (residueCardinality v) z))⁻¹) =
      ∏ w : FinitePlacesAbove L v,
        (((cE w).lPolynomial).eval (spectralPoint (residueCardinality w.1) z))⁻¹) ∧
    finiteEpsilonBase Finset.univ (fun _ : I => residueCardinality v) (fun i => (cF i).epsilon) =
      finiteEpsilonBase Finset.univ (fun w : FinitePlacesAbove L v => residueCardinality w.1)
        (fun w => (cE w).epsilon)

set_option maxHeartbeats 3500000 in
theorem commonNormTwistAuxiliaryFactors :
    CommonNormTwistAuxiliaryFactorsStatement v I κ ν A₀ B₀ cF cE := by
  classical
  intro hres hcase
  let η := quasicharacterBase v (ν.finiteComponent v)
  let raw (i : I) := (κ i).toMonoidHom
  let A := Finset.univ.image raw
  let res (i : I) : A := ⟨raw i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hs : Function.Surjective res := by
    intro a
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i, Subtype.ext hi⟩
  choose pick hpick using hs
  have hA (w : FinitePlacesAbove L v) (θ : (padicField v).Carrierˣ →* ℂˣ) :
      θ ∈ A ↔ IsNormTrivial (w.1.adicCompletion L) θ := by
    rw [(hres w θ).1]
    simp [A, raw]
  let χ (a : A) := κ (pick a) * η
  have hχ (a : A) : (χ a).toMonoidHom = a.val * η.toMonoidHom := by
    have h := congrArg Subtype.val (hpick a)
    exact congrArg (fun θ : (padicField v).Carrierˣ →* ℂˣ => θ * η.toMonoidHom) h
  let dF (a : A) := cF (pick a)
  have hd (i : I) : (cF i).lPolynomial = (dF (res i)).lPolynomial ∧
      (cF i).epsilon = (dF (res i)).epsilon := by
    have h : κ (pick (res i)) = κ i :=
      ContinuousMonoidHom.toMonoidHom_injective (congrArg Subtype.val (hpick (res i)))
    have he : χ (res i) = κ i * η := congrArg (fun ξ : QuasiCharacter (padicField v) => ξ * η) h
    exact standardTwistChoices_eq v (cF i) (dF (res i)) he.symm
  let w₀ := placeAbove L v
  have hcounts (a : A) : Fintype.card {i // res i = a} = Fintype.card (FinitePlacesAbove L v) := by
    have he (i : I) : res i = a ↔ raw i = a.val :=
      ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr (Equiv.subtypeEquivRight he)]
    exact (hres w₀ a.val).2 ((hA w₀ a.val).mp a.property)
  have hvals (w : FinitePlacesAbove L v) :
      (∏ a : A, (dF a).lPolynomial) = expand ℂ (w.1.asIdeal.inertiaDeg (𝓞 K)) (cE w).lPolynomial ∧
      (∑ a : A, (dF a).epsilon.2) = (w.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * (cE w).epsilon.2 := by
    rcases hcase with ⟨s, hs, hsw⟩ | ⟨hF, hE⟩
    · exact spherical_commonTwistAtUpper v w A₀ (B₀ w) ν A (hA w) χ hχ dF (cE w) s hs (hsw w)
    · exact ramified_commonTwistAtUpper v w A₀ (B₀ w) ν A (hA w) χ hχ dF (cE w)
        (fun a => hF (pick a)) (hE w)
  have hq (w : FinitePlacesAbove L v) :
      residueCardinality w.1 = residueCardinality v ^ w.1.asIdeal.inertiaDeg (𝓞 K) := by
    unfold residueCardinality
    rw [canonicalResidueCardinality_eq_absNorm, canonicalResidueCardinality_eq_absNorm]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal).symm
  have hqpos : 0 < residueCardinality v :=
    Nat.zero_lt_one.trans (padicField v).canonicalTopologicalData.residueCardinality_gt_one
  have h := groupedAuxiliaryValues res hcounts hqpos
    (fun w : FinitePlacesAbove L v => residueCardinality w.1) (fun w => w.1.asIdeal.inertiaDeg (𝓞 K)) hq
    (fun a => (dF a).lPolynomial) (fun w => (cE w).lPolynomial)
    (fun a => (dF a).epsilon) (fun w => (cE w).epsilon) (fun w => (hvals w).1) (fun w => (hvals w).2)
  simpa only [fun i => (hd i).1, fun i => (hd i).2, Function.comp_def] using h

end Product

end Langlands.BaseChange
