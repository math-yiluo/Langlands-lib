import Langlands.BaseChange.AuxiliaryFactorProductComparison
import Langlands.BaseChange.CompletionRelativeFieldInvariants
import Langlands.BaseChange.SphericalNormTwistFactors
import Langlands.Automorphic.AssociatedGammaFinal

/-! # Standard factor comparison at a spherical auxiliary place -/

noncomputable section

set_option autoImplicit false

universe u uQ uX

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic Global.AdelicFunctoriality
open Global.CuspidalPairFunctionalEquation Global.FunctionalEquationComparison
open Global.HeckeFunctionalEquation Automorphic.CuspidalWhittaker
open ClassField.Global.RelativeWeilGroup RankinSelberg Unramified
open scoped NumberField FiniteExtension

section FactorChoices

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
variable {r : ℕ} {T Td : CuspidalOperatorRealization K r} {T₁ Td₁ : CuspidalOperatorRealization K 0}
variable {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
variable {P₁ : CuspidalSpectralPresentation.{u, uQ} T₁}
variable {Pd₁ : CuspidalSpectralPresentation.{u, uQ} Td₁}
variable {h : HasIrreducibleAdmissibleComponents P} {hd : HasIrreducibleAdmissibleComponents Pd}
variable {h₁ : HasIrreducibleAdmissibleComponents P₁} {hd₁ : HasIrreducibleAdmissibleComponents Pd₁}

private theorem pairFactors_at_standardCharacter
    (c : FinitePairFactorChoice (standardGlobalAdditiveCharacter K) P P₁ Pd Pd₁ h h₁ hd hd₁)
    (v : Global.FinitePlace K) (ν : LocalAdditiveHaarMeasure (padicField v))
    (hν : IsSelfDualMeasure (padicField v) (standardFiniteAdditiveComponent K v) ν) :
    IsAutomorphicPairLPolynomial (padicField v) (standardFiniteAdditiveComponent K v) ν
      (localClass P h v) (localClass P₁ h₁ v) (c.lPolynomial v) ∧
    IsAutomorphicPairEpsilonFactor (padicField v) (standardFiniteAdditiveComponent K v) ν
      (localClass P h v) (localClass P₁ h₁ v) (c.epsilon v) := by
  have hψ := isCanonicalFiniteAdditiveComponent_unique (c.additive_spec v)
    (isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v)
  obtain ⟨ν₀, -, hν₀⟩ := existsUnique_selfDualMeasure_standardFiniteAdditiveComponent K v
  have hμ : c.measure v = ν := (hν₀ _ (hψ ▸ c.measure_spec v)).trans (hν₀ _ hν).symm
  exact ⟨hψ ▸ hμ ▸ c.lPolynomial_spec v, hψ ▸ hμ ▸ c.epsilon_spec v⟩

private theorem twistEquiv_of_isCharacterTwist {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {r : ℕ} (ω : QuasiCharacter F) (A B : AutomorphicObject.{u, u} F r.succPNat)
    (h : IsCharacterTwist F ω (automorphicClassOf F A) (automorphicClassOf F B)) :
    letI := F.canonicalTopologicalData.topology
    Nonempty ((Langlands.twist (determinantQuasiCharacter F r.succPNat ω)
      A.obj.representation).Equiv B.obj.representation) := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨A₀, B₀, ha, hb, ⟨e⟩⟩ := h
  obtain ⟨a⟩ := (automorphicClassOf_eq_iff F A A₀).mp ha.symm
  obtain ⟨b⟩ := (automorphicClassOf_eq_iff F B₀ B).mp hb
  exact ⟨((Langlands.twistEquiv _ a).trans e).trans b⟩

end FactorChoices

section Upper

private structure UpperSphericalFactors {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {r : ℕ} (s : Eigenvalues (r + 1)) (ψ : F.Carrier → Circle) (P : Polynomial ℂ) (b : ℂˣ × ℤ) where
  obj : AutomorphicObject.{u, u} F r.succPNat
  rankOne : AutomorphicObject.{u, u} F 1
  spectrum : HasSphericalSpectrum F obj s
  trivial : letI := F.canonicalTopologicalData.topology
    Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv rankOne.obj.representation)
  additive : NontrivialAdditiveCharacter F
  additive_eq : ∀ x, additive x = ψ x
  measure : LocalAdditiveHaarMeasure F
  selfDual : IsSelfDualMeasure F additive measure
  lPolynomial : IsAutomorphicPairLPolynomial F additive measure
    (automorphicClassOf F obj) (automorphicClassOf F rankOne) P
  epsilon : IsAutomorphicPairEpsilonFactor F additive measure
    (automorphicClassOf F obj) (automorphicClassOf F rankOne) b

variable {K : Type u} [Field K] [NumberField K] (w : Global.FinitePlace K)

private def upperSphericalFactors_atPrime {p : ℕ} [Fact p.Prime] (hp : residuePrime w = p)
    {r : ℕ} {s : Eigenvalues (r + 1)} {P : Polynomial ℂ} {b : ℂˣ × ℤ}
    (c : UpperSphericalFactors (padicField w) s (standardFiniteAdditiveComponent K w) P b) :
    UpperSphericalFactors (padicFieldAt w hp) s (standardFiniteAdditiveComponent K w) P b := by
  subst p
  exact c

end Upper

section LocalComparison

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
  (v : Global.FinitePlace K) (w : FinitePlacesAbove L v)

local notation "F" => padicField v
local notation "E" => CompletionPadic.towerPadicField v (Subtype.val w)
local notation "f" => Ideal.inertiaDeg
  (IsDedekindDomain.HeightOneSpectrum.asIdeal (Subtype.val w)) (𝓞 K)

set_option maxHeartbeats 950000 in
private theorem sphericalNormFactors_at_upper {r : ℕ} (s : Eigenvalues (r + 1))
    (JF : AutomorphicObject.{u, u} F r.succPNat) (J₁F : AutomorphicObject.{u, u} F 1)
    (hs : HasSphericalSpectrum F JF s)
    (h₁ : letI := (F).canonicalTopologicalData.topology
      Nonempty ((rankOneCharacter (1 : (F).Carrierˣ →* ℂˣ)).Equiv J₁F.obj.representation))
    (ν : LocalAdditiveHaarMeasure F)
    (hν : IsSelfDualMeasure F (standardFiniteAdditiveComponent K v) ν)
    (A : Finset ((F).Carrierˣ →* ℂˣ))
    (hA : ∀ κ, κ ∈ A ↔ IsNormTrivial (E).Carrier κ)
    (ω : A → QuasiCharacter F) (hω : letI := (F).canonicalTopologicalData.topology
      ∀ κ : A, (ω κ).toMonoidHom = κ.1)
    (J : A → AutomorphicObject.{u, u} F r.succPNat)
    (ht : ∀ κ, IsCharacterTwist F (ω κ) (automorphicClassOf F JF) (automorphicClassOf F (J κ)))
    (P : A → Polynomial ℂ) (b : A → ℂˣ × ℤ)
    (hP : ∀ κ, IsAutomorphicPairLPolynomial F (standardFiniteAdditiveComponent K v) ν
      (automorphicClassOf F (J κ)) (automorphicClassOf F J₁F) (P κ))
    (hb : ∀ κ, IsAutomorphicPairEpsilonFactor F (standardFiniteAdditiveComponent K v) ν
      (automorphicClassOf F (J κ)) (automorphicClassOf F J₁F) (b κ))
    {Q : Polynomial ℂ} {c : ℂˣ × ℤ}
    (up : UpperSphericalFactors (padicField w.1) (s.power f)
      (standardFiniteAdditiveComponent L w.1) Q c) :
    (∏ κ : A, P κ) = Polynomial.expand ℂ f Q ∧ (∑ κ : A, (b κ).2) = (f : ℤ) * c.2 := by
  have hscalar := towerPadicField_isScalarTower v w.1
  obtain ⟨htop, hgal, hf, d, hd⟩ := completionRelativeFieldInvariants K L v w.1
  let := hscalar
  let := htop
  let := hgal
  let up' := upperSphericalFactors_atPrime w.1 (residuePrime_eq v w.1) up
  have htrace (x : (E).Carrier) : up'.additive x =
      standardFiniteAdditiveComponent K v (Algebra.trace (F).Carrier (E).Carrier x) :=
    (up'.additive_eq x).trans (standardFiniteAdditiveComponent_trace v w.1 x)
  exact sphericalNormTwistFactors.{u, u, u} (residuePrime v) F E f d r hf hd
    (standardFiniteAdditiveComponent K v) up'.additive htrace ν up'.measure hν up'.selfDual
    A hA ω hω JF up'.obj s hs up'.spectrum J
    (fun κ => twistEquiv_of_isCharacterTwist F (ω κ) JF (J κ) (ht κ))
    J₁F up'.rankOne h₁ up'.trivial P Q b c hP up'.lPolynomial hb up'.epsilon

end LocalComparison

section Product

private theorem upperPlaceFactorValues {A : Type u} [Fintype A] [DecidableEq A]
    {q q' f : ℕ} (hq : 0 < q) (hq' : q' = q ^ f)
    (P : A → Polynomial ℂ) (b : A → ℂˣ × ℤ) (Q : Polynomial ℂ) (c : ℂˣ × ℤ)
    (hP : (∏ a, P a) = Polynomial.expand ℂ f Q) (hb : (∑ a, (b a).2) = (f : ℤ) * c.2) :
    (∀ z : ℂ, (∏ a, ((P a).eval (spectralPoint q z))⁻¹) = (Q.eval (spectralPoint q' z))⁻¹) ∧
      (∏ a, (q : ℝ) ^ (b a).2) = (q' : ℝ) ^ c.2 := by
  have hcard (a : A) : Fintype.card {x : A // id x = a} = Fintype.card Unit := by
    let e : {x : A // id x = a} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨a, rfl⟩
        left_inv := fun x => Subtype.ext x.property.symm
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  obtain ⟨hL, hε⟩ := auxiliaryFactorProductComparison A A Unit id hcard q q' f hq hq'
    P Q P (fun _ => Q) (fun a => (b a).2) c.2 b (fun _ => c) hP hb
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact ⟨fun z => by simpa using hL z, by simpa [finiteEpsilonBase] using hε⟩

private theorem prod_of_repeated_restriction {X A M : Type*} [Fintype X] [Fintype A]
    [DecidableEq A] [CommMonoid M] (res : X → A) (m : ℕ)
    (hm : ∀ a : A, Fintype.card {x : X // res x = a} = m) (g : A → M) :
    (∏ x, g (res x)) = (∏ a, g a) ^ m := by
  rw [← Fintype.prod_fiberwise' res g, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun a _ => by simp [hm a]

end Product

/-- Compare the forward finite Euler and positive epsilon products at a spherical base
place with the products over its upper places. The lower twists and both pair-factor
choices are the actual data from the global presentations. -/
def SphericalAuxiliaryCompletionComparisonStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] [CompactSpace (AdeleQuotient K)]
    [CompactSpace (AdeleQuotient L)] (r : ℕ) (X : Type uX) [Fintype X]
    (χ : X → HeckeCharacter K) (T : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (h : HasIrreducibleAdmissibleComponents P)
    (T' : CuspidalOperatorRealization L r) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h' : HasIrreducibleAdmissibleComponents P')
    (T₁ Td₁ : CuspidalOperatorRealization K 0) (P₁ : CuspidalSpectralPresentation.{u, uQ} T₁)
    (Pd₁ : CuspidalSpectralPresentation.{u, uQ} Td₁) (h₁ : HasIrreducibleAdmissibleComponents P₁)
    (hd₁ : HasIrreducibleAdmissibleComponents Pd₁)
    (T'₁ Td'₁ : CuspidalOperatorRealization L 0) (P'₁ : CuspidalSpectralPresentation.{u, uQ} T'₁)
    (Pd'₁ : CuspidalSpectralPresentation.{u, uQ} Td'₁) (h'₁ : HasIrreducibleAdmissibleComponents P'₁)
    (hd'₁ : HasIrreducibleAdmissibleComponents Pd'₁)
    (Td : X → CuspidalOperatorRealization K r) (Pd : ∀ x, CuspidalSpectralPresentation.{u, uQ} (Td x))
    (hd : ∀ x, HasIrreducibleAdmissibleComponents (Pd x))
    (Td' : CuspidalOperatorRealization L r) (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (hd' : HasIrreducibleAdmissibleComponents Pd')
    (cF : ∀ x, FinitePairFactorChoice (standardGlobalAdditiveCharacter K) (P.heckeDeterminantTwist (χ x))
      P₁ (Pd x) Pd₁ (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ x) h) h₁ (hd x) hd₁)
    (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) P' P'₁ Pd' Pd'₁ h' h'₁ hd' hd'₁)
    (v : Global.FinitePlace K) (s : Eigenvalues (r + 1)),
    HasSphericalSpectrum (padicField v) ((P.localComponent v).padicObject (h v).1 (h v).2) s →
    (∀ w : FinitePlacesAbove L v,
      HasSphericalSpectrum (padicField w.1) ((P'.localComponent w.1).padicObject (h' w.1).1 (h' w.1).2)
        (s.power (w.1.asIdeal.inertiaDeg (𝓞 K)))) →
    Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (P₁.localComponent v).representation) →
    (∀ w : FinitePlacesAbove L v,
      Nonempty ((rankOneCharacter (1 : (padicField w.1).Carrierˣ →* ℂˣ)).Equiv
        (P'₁.localComponent w.1).representation)) →
    (∀ (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ x, ((χ x).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {x // ((χ x).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
    (∀ z : ℂ, (∏ x, (cF x).finiteL v z) = ∏ w : FinitePlacesAbove L v, cE.finiteL w.1 z) ∧
    finiteEpsilonBase Finset.univ (fun _ : X => residueCardinality v) (fun x => (cF x).epsilon v) =
      finiteEpsilonBase Finset.univ (fun w : FinitePlacesAbove L v => residueCardinality w.1)
        (fun w => cE.epsilon w.1)

set_option maxHeartbeats 2500000 in
/-- Apply the spherical norm comparison in each completion, then count the repetitions
in the global character list. -/
theorem sphericalAuxiliaryCompletionComparison : SphericalAuxiliaryCompletionComparisonStatement.{u, uQ, uX} := by
  classical
  intro K L _ _ _ _ _ _ _ _ _ r X _ χ T P h T' P' h' T₁ Td₁ P₁ Pd₁ h₁ hd₁ T'₁ Td'₁ P'₁ Pd'₁ h'₁ hd'₁
    Td Pd hd Td' Pd' hd' cF cE v s hs hs' e₁ e'₁ hres
  let F := padicField v
  let raw (x : X) := ((χ x).finiteComponent v).toMonoidHom
  let A := Finset.univ.image raw
  let res (x : X) : A := ⟨raw x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have hsurj : Function.Surjective res := by
    intro a
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp a.property
    exact ⟨x, Subtype.ext hx⟩
  let pick (a : A) := Classical.choose (hsurj a)
  have hpick (a : A) : res (pick a) = a := Classical.choose_spec (hsurj a)
  have hmem (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ) :
      κ ∈ A ↔ IsNormTrivial (w.1.adicCompletion L) κ := by
    rw [(hres w κ).1]
    simp [A, raw]
  let JF := (P.localComponent v).padicObject (h v).1 (h v).2
  let J₁ := (P₁.localComponent v).padicObject (h₁ v).1 (h₁ v).2
  let hx (x : X) := P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ x) h
  let J (x : X) := ((P.heckeDeterminantTwist (χ x)).localComponent v).padicObject (hx x v).1 (hx x v).2
  let ω (x : X) := quasicharacterBase v ((χ x).finiteComponent v)
  have ht (x : X) : IsCharacterTwist F (ω x) (automorphicClassOf F JF) (automorphicClassOf F (J x)) :=
    P.isCharacterTwist_heckeDeterminantTwist_padicClass (χ x) v (h v).1 (h v).2 (hx x v).1 (hx x v).2
  have hω (a : A) : letI := F.canonicalTopologicalData.topology
      (ω (pick a)).toMonoidHom = a.1 := congrArg Subtype.val (hpick a)
  have htw (x : X) : automorphicClassOf F (J x) = automorphicClassOf F (J (pick (res x))) := by
    have he : ω (pick (res x)) = ω x := by
      let := F.canonicalTopologicalData.topology
      apply ContinuousMonoidHom.toMonoidHom_injective
      exact hω (res x)
    exact (ht x).unique (he ▸ ht (pick (res x)))
  let p (a : A) := (cF (pick a)).lPolynomial v
  let b (a : A) := (cF (pick a)).epsilon v
  obtain ⟨ν, hν, -⟩ := existsUnique_selfDualMeasure_standardFiniteAdditiveComponent K v
  have hcert (x : X) := pairFactors_at_standardCharacter (cF x) v ν hν
  have hrep (x : X) : (cF x).lPolynomial v = p (res x) ∧ (cF x).epsilon v = b (res x) := by
    obtain ⟨hP₀, hb₀⟩ := hcert x
    change IsAutomorphicPairLPolynomial F _ ν (automorphicClassOf F (J x))
      (automorphicClassOf F J₁) _ at hP₀
    change IsAutomorphicPairEpsilonFactor F _ ν (automorphicClassOf F (J x))
      (automorphicClassOf F J₁) _ at hb₀
    rw [htw x] at hP₀ hb₀
    exact ⟨hP₀.unique (hcert _).1, hb₀.unique (hcert _).2⟩
  have hvals (w : FinitePlacesAbove L v) :
      (∀ z : ℂ, (∏ a : A, ((p a).eval (spectralPoint (residueCardinality v) z))⁻¹) =
        cE.finiteL w.1 z) ∧
      (∏ a : A, (residueCardinality v : ℝ) ^ (b a).2) =
        (residueCardinality w.1 : ℝ) ^ (cE.epsilon w.1).2 := by
    let e := w.1.asIdeal.inertiaDeg (𝓞 K)
    have had := isCanonicalFiniteAdditiveComponent_unique (cE.additive_spec w.1)
      (isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent L w.1)
    let up : UpperSphericalFactors (padicField w.1) (s.power e)
      (standardFiniteAdditiveComponent L w.1) (cE.lPolynomial w.1) (cE.epsilon w.1) :=
      { obj := (P'.localComponent w.1).padicObject (h' w.1).1 (h' w.1).2
        rankOne := (P'₁.localComponent w.1).padicObject (h'₁ w.1).1 (h'₁ w.1).2
        spectrum := hs' w
        trivial := e'₁ w
        additive := cE.additive w.1
        additive_eq := fun z => congrArg (fun a : NontrivialAdditiveCharacter (padicField w.1) => a z) had
        measure := cE.measure w.1
        selfDual := cE.measure_spec w.1
        lPolynomial := cE.lPolynomial_spec w.1
        epsilon := cE.epsilon_spec w.1 }
    obtain ⟨hp, hb⟩ := sphericalNormFactors_at_upper v w s JF J₁ hs
      e₁ ν hν A (hmem w) (fun a => ω (pick a)) hω (fun a => J (pick a)) (fun a => ht (pick a))
      p b (fun a => (hcert (pick a)).1) (fun a => (hcert (pick a)).2) up
    have hq : residueCardinality w.1 = residueCardinality v ^ e := by
      change (padicField w.1).canonicalTopologicalData.residueCardinality =
        (padicField v).canonicalTopologicalData.residueCardinality ^ e
      rw [Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm w.1, Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm v]
      exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal).symm
    have hqpos : 0 < residueCardinality v := by
      change 0 < (padicField v).canonicalTopologicalData.residueCardinality
      rw [Langlands.Global.CompletionPadic.canonicalResidueCardinality_eq_absNorm v]
      exact Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    exact upperPlaceFactorValues hqpos hq p b _ _ hp hb
  let w₀ := placeAbove L v
  have hcount (a : A) : Fintype.card {x : X // res x = a} = Fintype.card (FinitePlacesAbove L v) := by
    have he (x : X) : res x = a ↔ raw x = a.1 :=
      ⟨congrArg Subtype.val, fun hx => Subtype.ext hx⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr (Equiv.subtypeEquivRight he)]
    exact (hres w₀ a.1).2 ((hmem w₀ a.1).mp a.property)
  constructor
  · intro z
    let g (a : A) := ((p a).eval (spectralPoint (residueCardinality v) z))⁻¹
    calc
      (∏ x, (cF x).finiteL v z) = ∏ x, g (res x) := by
        exact Finset.prod_congr rfl fun x _ => by simp only [FinitePairFactorChoice.finiteL, (hrep x).1, g]
      _ = (∏ a, g a) ^ Fintype.card (FinitePlacesAbove L v) :=
        prod_of_repeated_restriction res _ hcount g
      _ = _ := by
        simp_rw [← (hvals _).1 z]
        simp [g]
  · simp only [finiteEpsilonBase, fun x => (hrep x).2]
    rw [prod_of_repeated_restriction res _ hcount (fun a => (residueCardinality v : ℝ) ^ (b a).2)]
    simp_rw [← (hvals _).2]
    simp

end Langlands.BaseChange
