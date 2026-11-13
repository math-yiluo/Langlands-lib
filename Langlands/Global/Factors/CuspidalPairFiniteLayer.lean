import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.Factors.HeckeLocalData
import Langlands.Global.Factors.HeckeAdditiveConductors
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Representation.RankinSelberg.LanglandsPairLFactorExistenceProof
import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonFactorExistenceProof
import Langlands.Correspondence.UnramifiedPairFactors

/-! # The finite-place layer of the cuspidal pair functional equation -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open NumberField
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup

section LocalExistence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- Every pair of classes has a pair L-polynomial, for every self-dual measure. -/
theorem exists_isAutomorphicPairLPolynomial
    (ψ : Correspondence.NontrivialAdditiveCharacter K)
    {ν : Correspondence.LocalAdditiveHaarMeasure K}
    (hν : Correspondence.IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat) :
    ∃ P : Polynomial ℂ, Correspondence.IsAutomorphicPairLPolynomial K ψ ν π π' P := by
  obtain ⟨A, rfl⟩ := Correspondence.automorphicClass_has_representative K π
  obtain ⟨A', rfl⟩ := Correspondence.automorphicClass_has_representative K π'
  obtain ⟨P, hP⟩ := RankinSelberg.langlandsPairLFactorExistence.{u, u, u} p K ψ ⟨ν, hν⟩ r t
    A.obj A'.obj A.property.1 A.property.2 A'.property.1 A'.property.2
  exact ⟨P, (Correspondence.isAutomorphicPairLPolynomial_iff K A A' A.obj A'.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mpr hP⟩

/-- Every pair of classes has a pair epsilon factor, for every self-dual measure. -/
theorem exists_isAutomorphicPairEpsilonFactor
    (ψ : Correspondence.NontrivialAdditiveCharacter K)
    {ν : Correspondence.LocalAdditiveHaarMeasure K}
    (hν : Correspondence.IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (π : Correspondence.AutomorphicClass.{u, u} K r.succPNat)
    (π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat) :
    ∃ e : ℂˣ × ℤ, Correspondence.IsAutomorphicPairEpsilonFactor K ψ ν π π' e := by
  obtain ⟨A, rfl⟩ := Correspondence.automorphicClass_has_representative K π
  obtain ⟨A', rfl⟩ := Correspondence.automorphicClass_has_representative K π'
  obtain ⟨e, he⟩ := RankinSelberg.langlandsPairEpsilonFactorExistence.{u, u, u} p K ψ ⟨ν, hν⟩
    r t A.obj A'.obj A.property.1 A.property.2 A'.property.1 A'.property.2
  exact ⟨e, (Correspondence.isAutomorphicPairEpsilonFactor_iff K A A' A.obj A'.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mpr he⟩

/-- The pair Euler polynomial of two enumerated spectra is the double product. -/
theorem pairEulerPolynomial_ofTuple {n m : ℕ} (z : Fin n → ℂˣ) (z' : Fin m → ℂˣ) :
    pairEulerPolynomial (Unramified.Eigenvalues.ofTuple z) (Unramified.Eigenvalues.ofTuple z') =
      ∏ i, ∏ j, (1 - Polynomial.C ((z i : ℂ) * z' j) * Polynomial.X) := by
  unfold pairEulerPolynomial
  change (((List.ofFn z : Multiset ℂˣ) ×ˢ (List.ofFn z' : Multiset ℂˣ)).map _).prod = _
  rw [Multiset.prod_map_product_eq_prod_prod, ← Fin.univ_val_map z, ← Fin.univ_val_map z']
  simp only [Multiset.map_map, Function.comp_def, map_mul]
  rfl

/-- At a spherical pair, the pair L-polynomial is the pair Euler polynomial of the
spherical spectra. -/
theorem isAutomorphicPairLPolynomial_eq_pairEulerPolynomial
    (ψ : Correspondence.NontrivialAdditiveCharacter K)
    {ν : Correspondence.LocalAdditiveHaarMeasure K}
    (hν : Correspondence.IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (A : Correspondence.AutomorphicObject.{u, u} K r.succPNat)
    (A' : Correspondence.AutomorphicObject.{u, u} K t.succPNat)
    {s : Unramified.Eigenvalues (r + 1)} {s' : Unramified.Eigenvalues (t + 1)}
    (hs : Unramified.HasSphericalSpectrum K A s) (hs' : Unramified.HasSphericalSpectrum K A' s')
    {P : Polynomial ℂ}
    (hP : Correspondence.IsAutomorphicPairLPolynomial K ψ ν
      (Correspondence.automorphicClassOf K A) (Correspondence.automorphicClassOf K A') P) :
    P = pairEulerPolynomial s s' := by
  obtain ⟨z, hz, rfl, hd⟩ := Correspondence.exists_unramifiedDatum_isLanglandsQuotient.{u, u}
    K A A.obj (Representation.Equiv.refl _) s hs
  obtain ⟨z', hz', rfl, hd'⟩ := Correspondence.exists_unramifiedDatum_isLanglandsQuotient.{u, u}
    K A' A'.obj (Representation.Equiv.refl _) s' hs'
  rw [pairEulerPolynomial_ofTuple]
  exact Correspondence.unramifiedDatum_lPolynomial_eq K ψ ν hν z hz z' hz' A.obj A'.obj hd hd'
    ((Correspondence.isAutomorphicPairLPolynomial_iff K A A' A.obj A'.obj
      (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hP)

/-- At a spherical pair, with `ψ` of conductor zero and `ν` self-dual, the pair
epsilon factor is `(1, 0)`. -/
theorem isAutomorphicPairEpsilonFactor_eq_one
    (ψ : Correspondence.NontrivialAdditiveCharacter K)
    {ν : Correspondence.LocalAdditiveHaarMeasure K}
    (hν : Correspondence.IsSelfDualMeasure K ψ ν)
    (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) {r t : ℕ}
    (A : Correspondence.AutomorphicObject.{u, u} K r.succPNat)
    (A' : Correspondence.AutomorphicObject.{u, u} K t.succPNat)
    {s : Unramified.Eigenvalues (r + 1)} {s' : Unramified.Eigenvalues (t + 1)}
    (hs : Unramified.HasSphericalSpectrum K A s) (hs' : Unramified.HasSphericalSpectrum K A' s')
    {e : ℂˣ × ℤ}
    (he : Correspondence.IsAutomorphicPairEpsilonFactor K ψ ν
      (Correspondence.automorphicClassOf K A) (Correspondence.automorphicClassOf K A') e) :
    e = (1, 0) := by
  obtain ⟨z, hz, -, hd⟩ := Correspondence.exists_unramifiedDatum_isLanglandsQuotient.{u, u}
    K A A.obj (Representation.Equiv.refl _) s hs
  obtain ⟨z', hz', -, hd'⟩ := Correspondence.exists_unramifiedDatum_isLanglandsQuotient.{u, u}
    K A' A'.obj (Representation.Equiv.refl _) s' hs'
  exact Correspondence.unramifiedDatum_epsilonFactor_eq K ψ ν hν hψ z hz z' hz' A.obj A'.obj
    hd hd' ((Correspondence.isAutomorphicPairEpsilonFactor_iff K A A' A.obj A'.obj
      (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp he)

end LocalExistence

variable {F : Type u} [Field F] [NumberField F]

/-- The finite component of `ψ` at `v`, in the canonical topology of `padicField v`. -/
def canonicalFiniteAdditiveComponent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) (v : FinitePlace F) :
    Correspondence.NontrivialAdditiveCharacter (padicField v) := by
  letI : TopologicalSpace (FiniteCompletion F v) :=
    (padicField v).canonicalTopologicalData.topology
  exact
    { toAddChar := HeckeFunctionalEquation.finiteAdditiveRestriction ψ v
      continuous_toFun := by
        change @Continuous (FiniteCompletion F v) Circle
          (padicField v).canonicalTopologicalData.topology _
          (HeckeFunctionalEquation.finiteAdditiveRestriction ψ v)
        rw [← completion_topology_eq v]
        exact HeckeFunctionalEquation.continuous_finiteAdditiveRestriction ψ v
      nontrivial := HeckeFunctionalEquation.finiteAdditiveRestriction_ne_one ψ hdiag v }

/-- `canonicalFiniteAdditiveComponent ψ hdiag v` is a canonical finite component of `ψ`. -/
theorem isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) (v : FinitePlace F) :
    IsCanonicalFiniteAdditiveComponent ψ v (canonicalFiniteAdditiveComponent ψ hdiag v) := by
  intro x
  rfl

/-- Additive conductors agree for equal topological data and characters with the same
underlying additive character. -/
theorem additiveConductor_congr {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}
    {T T' : K.TopologicalData} (hT : T = T')
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ T.topology)
    (ψ' : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _ T'.topology)
    (h : @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _ T.topology ψ =
      @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _ T'.topology ψ') :
    T.additiveConductor ψ = T'.additiveConductor ψ' := by
  subst hT
  obtain ⟨χ, hc, hn⟩ := ψ
  obtain ⟨χ', hc', hn'⟩ := ψ'
  cases h
  rfl

/-- The canonical finite components of `ψ` have additive conductor zero outside a finite
set of finite places. -/
theorem exists_finiteAdditiveSupport
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) :
    ∃ S : Finset (FinitePlace F), FunctionalEquationComparison.FiniteAdditiveSupport ψ S := by
  obtain ⟨⟨e, he⟩, -⟩ := adelicDuality F ψ hdiag
  let ψf := fun v => HeckeFunctionalEquation.finiteAdditiveComponent ψ v
    (HeckeFunctionalEquation.finiteAdditiveRestriction_ne_one ψ hdiag v)
  obtain ⟨S, hS⟩ := HeckeFunctionalEquation.exists_finset_additiveConductor_eq_zero_of_pairing
    ψ e he ψf
    (fun v => HeckeFunctionalEquation.isFiniteAdditiveComponent_finiteAdditiveComponent ψ v _)
  refine ⟨S, fun v hv => ⟨canonicalFiniteAdditiveComponent ψ hdiag v,
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hdiag v, ?_⟩⟩
  rw [← hS v hv]
  exact additiveConductor_congr (topologicalData_eq_canonicalTopologicalData v).symm _ _ rfl

/-- `FiniteAdditiveSupport` is monotone in the exceptional set. -/
theorem finiteAdditiveSupport_mono {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    {S S' : Finset (FinitePlace F)}
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S) (h : S ⊆ S') :
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S' :=
  fun v hv => hS v (fun hvS => hv (h hvS))

/-- `ψ` has an additive component at every real place. -/
theorem exists_isRealAdditiveComponent
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) (v : {v : InfinitePlace F // v.IsReal}) :
    ∃ a : ℝˣ, HeckeFunctionalEquation.IsRealAdditiveComponent ψ v.1 v.2 a :=
  ⟨_, HeckeFunctionalEquation.isRealAdditiveComponent_realCompletionAdditiveScale ψ v.2
    (HeckeFunctionalEquation.infiniteAdditiveRestriction_ne_one ψ hdiag v.1)⟩

/-- `ψ` has an additive component at every complex place. -/
theorem exists_isComplexAdditiveComponent
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) (v : {v : InfinitePlace F // v.IsComplex}) :
    ∃ a : ℂˣ, HeckeFunctionalEquation.IsComplexAdditiveComponent ψ v.1 v.2 a :=
  ⟨_, HeckeFunctionalEquation.isComplexAdditiveComponent_complexCompletionAdditiveScale ψ v.2
    (HeckeFunctionalEquation.infiniteAdditiveRestriction_ne_one ψ hdiag v.1)⟩

variable [CompactSpace (AdeleQuotient F)]

/-- A finite factor choice exists: the canonical components of `ψ`, their self-dual
measures, and chosen pair L-polynomials and epsilon factors. -/
theorem nonempty_finitePairFactorChoice
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) {r t : ℕ}
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd') :
    Nonempty (FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') := by
  let ψf := canonicalFiniteAdditiveComponent ψ hdiag
  let μ := fun v => Correspondence.localSelfDualHaar (padicField v) (ψf v)
  have hμ : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψf v) (μ v) :=
    fun v => Correspondence.isSelfDual_localSelfDualHaar (padicField v) (ψf v)
  have hL := fun v => exists_isAutomorphicPairLPolynomial (padicField v) (ψf v) (hμ v)
    (localClass P h v) (localClass P' h' v)
  have hLd := fun v => exists_isAutomorphicPairLPolynomial (padicField v) (ψf v) (hμ v)
    (localClass Pd hd v) (localClass Pd' hd' v)
  have hε := fun v => exists_isAutomorphicPairEpsilonFactor (padicField v) (ψf v) (hμ v)
    (localClass P h v) (localClass P' h' v)
  exact ⟨{ additive := ψf
           additive_spec := isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent
             ψ hdiag
           measure := μ
           measure_spec := hμ
           lPolynomial := fun v => (hL v).choose
           lPolynomial_spec := fun v => (hL v).choose_spec
           dualLPolynomial := fun v => (hLd v).choose
           dualLPolynomial_spec := fun v => (hLd v).choose_spec
           epsilon := fun v => (hε v).choose
           epsilon_spec := fun v => (hε v).choose_spec }⟩

/-- Outside the exceptional set, the canonical p-adic local component of a presentation
has the presentation's spherical spectrum. -/
theorem hasSphericalSpectrum_padicObject {r : ℕ} {T : Automorphic.CuspidalOperatorRealization F r}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (h : HasIrreducibleAdmissibleComponents P) (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    Unramified.HasSphericalSpectrum (padicField v)
      ((P.localComponent v).padicObject (h v).1 (h v).2) (P.spectralSystem.eigenvalues v hv) :=
  (Unramified.sphericalHeckeComparison (padicField v) r _ _).mpr
    ((Unramified.hasSphericalHeckeSpectrumClass_classOf _ _ _).mp
      (((P.localComponent v).hasSphericalHeckeSpectrumClass_iff (h v).1 (h v).2 _).mpr
        (P.hasSpectrum v hv)))

/-- One finite set contains the four exceptional sets and the places where `ψ` is
ramified, and every choice of finite factors is unramified outside it. -/
theorem exists_isUnramifiedOutside
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) {r t : ℕ}
    {T Td : Automorphic.CuspidalOperatorRealization F r}
    {T' Td' : Automorphic.CuspidalOperatorRealization F t}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd') :
    ∃ S : Finset (FinitePlace F),
      P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧ Pd.exceptional ⊆ S ∧ Pd'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∀ c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd', c.IsUnramifiedOutside S := by
  classical
  obtain ⟨S0, hS0⟩ := exists_finiteAdditiveSupport ψ hdiag
  refine ⟨S0 ∪ P.exceptional ∪ P'.exceptional ∪ Pd.exceptional ∪ Pd'.exceptional,
    fun v hv => by simp [hv], fun v hv => by simp [hv], fun v hv => by simp [hv],
    fun v hv => by simp [hv], finiteAdditiveSupport_mono hS0 (fun v hv => by simp [hv]), ?_⟩
  intro c v hv
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨hv0, hvP⟩, hvP'⟩, hvPd⟩, hvPd'⟩ := hv
  refine ⟨fun hv hv' => ?_, fun hv hv' => ?_, ?_⟩
  · exact isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v) (c.additive v)
      (c.measure_spec v) _ _ (hasSphericalSpectrum_padicObject P h v hv)
      (hasSphericalSpectrum_padicObject P' h' v hv') (c.lPolynomial_spec v)
  · exact isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v) (c.additive v)
      (c.measure_spec v) _ _ (hasSphericalSpectrum_padicObject Pd hd v hv)
      (hasSphericalSpectrum_padicObject Pd' hd' v hv') (c.dualLPolynomial_spec v)
  · obtain ⟨ψz, hψz, hcond⟩ := hS0 v hv0
    have hψ : (padicField v).canonicalTopologicalData.additiveConductor (c.additive v) = 0 := by
      rw [← hcond]
      exact additiveConductor_congr rfl _ _
        (DFunLike.ext _ _ fun x => (c.additive_spec v x).trans (hψz x).symm)
    exact isAutomorphicPairEpsilonFactor_eq_one (padicField v) (c.additive v)
      (c.measure_spec v) hψ _ _ (hasSphericalSpectrum_padicObject P h v hvP)
      (hasSphericalSpectrum_padicObject P' h' v hvP') (c.epsilon_spec v)

end Langlands.Global.CuspidalPairFunctionalEquation
