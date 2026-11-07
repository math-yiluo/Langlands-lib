import Langlands.Global.Factors.RelativeWeilEngine
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.Factors.HeckeFiniteEpsilon
import Langlands.Global.Factors.FiniteComparisonProof
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Correspondence.LocalConventions

/-!
# Hecke functional equations as functional-equation packages

The Hecke global functional equation (`HeckeGlobalFunctionalEquationStatement`, a hypothesis
here) for a Hecke character `χ` of a number field `K`, together with the convergence and
nonvanishing of its Euler product (`HeckeEulerProduct`), gives a package
`HasGlobalEquation` on the finite places of `K`.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

open Filter Topology
open Langlands.Global Langlands.Global.HeckeFunctionalEquation

/-- The denominator of a reciprocal-entire function has a nonzero germ everywhere. -/
theorem nonzeroMeromorphic_denominator (F : LocalFactor.ReciprocalEntire) :
    NonzeroMeromorphic F.denominator := by
  have hmer : Meromorphic F.denominator := fun x => (F.entire.analyticAt x).meromorphicAt
  refine ⟨hmer, fun z => ?_⟩
  obtain ⟨z₀, hz₀⟩ := F.nonzero
  have h₀ : meromorphicOrderAt F.denominator z₀ ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmer z₀)]
    exact ((F.entire.continuous.continuousAt (x := z₀)).eventually_ne hz₀).filter_mono
      nhdsWithin_le_nhds
  exact (Meromorphic.meromorphicOn hmer (s := Set.univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ z) h₀

open scoped Classical

variable {K : Type u} [Field K] [NumberField K]

/-- The finite Hecke L-factor at `v`, as in the Hecke functional equation. -/
def heckeL (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) : ℂ :=
  LocalFactor.PadicAbelian.lFactor (CompletionPadic.topologicalData v) (χ.finiteComponent v) s

/-- The product of the archimedean denominators of a presentation, as in the Hecke
functional equation. -/
def heckeInfiniteDenominator
    (dR : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → LocalFactor.Archimedean.ComplexCharacterData)
    (s : ℂ) : ℂ :=
  (∏ v, (dR v).lFactor.denominator s) * ∏ v, (dC v).lFactor.denominator s

/-- The archimedean epsilon factor, as in the Hecke functional equation. -/
def heckeInfiniteEpsilon
    (dR : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → LocalFactor.Archimedean.ComplexCharacterData)
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ) (s : ℂ) : ℂ :=
  (∏ v, ((dR v).epsilon (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
    ∏ v, ((dC v).epsilon (aC v) ‖((aC v : ℂ))‖₊
      (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)

theorem nonzeroMeromorphic_heckeInfiniteDenominator
    (dR : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → LocalFactor.Archimedean.ComplexCharacterData) :
    NonzeroMeromorphic (heckeInfiniteDenominator dR dC) := by
  have h1 : NonzeroMeromorphic (fun s => ∏ v, (dR v).lFactor.denominator s) :=
    NonzeroMeromorphic.finsetProd Finset.univ fun v _ => nonzeroMeromorphic_denominator _
  have h2 : NonzeroMeromorphic (fun s => ∏ v, (dC v).lFactor.denominator s) :=
    NonzeroMeromorphic.finsetProd Finset.univ fun v _ => nonzeroMeromorphic_denominator _
  exact NonzeroMeromorphic.mul h1 h2

/-- The Hecke functional equation for `χ`, with all its local data, gives a package
`HasGlobalEquation` on the finite places of `K`: finite factors `heckeL χ` and
`heckeL χ⁻¹`, epsilon factors `finiteEpsilon χ ψf μ`, archimedean products the reciprocals of
the denominators of the presentations, and archimedean epsilon `heckeInfiniteEpsilon`, with
exceptional set the Hecke set `S`, outside which the finite epsilon factors are `1`. -/
theorem hasGlobalEquation_of_heckeFE (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (χ : HeckeCharacter K) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ1 : ∃ x : Adeles K, ψ x ≠ 1) (hψ2 : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (haR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (haC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))
    (dR dR' : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData)
    (hdR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hdR' : ∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v))
    (dC dC' : {v : InfinitePlace K // v.IsComplex} →
      LocalFactor.Archimedean.ComplexCharacterData)
    (hdC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (hdC' : ∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v)) :
    ∃ S : Finset (FinitePlace K), (∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1) ∧
      HasGlobalEquation (heckeL χ) (heckeL χ⁻¹) (finiteEpsilon χ ψf μ)
        (fun s => (heckeInfiniteDenominator dR dC s)⁻¹)
        (fun s => (heckeInfiniteDenominator dR' dC' s)⁻¹)
        (heckeInfiniteEpsilon dR dC aR aC) S := by
  obtain ⟨σ, Λ, Λd, S, hΛ, hΛd, hprod, hε, hfe⟩ :=
    (hH K χ ψ hψ1 hψ2).2 ψf hψf μ aR haR aC haC dR dR' hdR hdR' dC dC' hdC hdC'
  obtain ⟨σ₁, h₁⟩ := HeckeEulerProduct.exists_hasProd_lFactor χ
  obtain ⟨σ₂, h₂⟩ := HeckeEulerProduct.exists_hasProd_lFactor χ⁻¹
  have hD := nonzeroMeromorphic_heckeInfiniteDenominator dR dC
  have hD' := nonzeroMeromorphic_heckeInfiniteDenominator dR' dC'
  refine ⟨S, hε, max σ (max σ₁ σ₂), fun s => Λ s * heckeInfiniteDenominator dR dC s,
    fun s => Λd s * heckeInfiniteDenominator dR' dC' s,
    fun x => (hΛ x (Set.mem_univ x)).mul (hD.1 x),
    fun x => (hΛd x (Set.mem_univ x)).mul (hD'.1 x), fun s hs => ?_, ?_⟩
  · have hs0 : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs1 : σ₁ < s.re :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hs2 : σ₂ < s.re :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    obtain ⟨hp1, hp2⟩ := hprod s hs0
    obtain ⟨L₁, hL₁, hpL₁⟩ := h₁ s hs1
    obtain ⟨L₂, hL₂, hpL₂⟩ := h₂ s hs2
    refine ⟨⟨hp1, ?_⟩, ⟨hp2, ?_⟩⟩
    · have h : Λ s * heckeInfiniteDenominator dR dC s = L₁ := hp1.unique hpL₁
      change Λ s * heckeInfiniteDenominator dR dC s ≠ 0
      rw [h]
      exact hL₁
    · have h : Λd s * heckeInfiniteDenominator dR' dC' s = L₂ := hp2.unique hpL₂
      change Λd s * heckeInfiniteDenominator dR' dC' s ≠ 0
      rw [h]
      exact hL₂
  · intro z
    have hz := meromorphicEq_of_codiscrete hfe z
    have hDz := hD.eventually_ne_zero z
    have hDz' := (NonzeroMeromorphic.reflect hD').eventually_ne_zero z
    filter_upwards [hz, hDz, hDz'] with s hs1 hs2 hs3
    rw [mul_inv_cancel_right₀ hs2, mul_inv_cancel_right₀ hs3, hs1]
    unfold heckeInfiniteEpsilon finiteEpsilon
    ring

/-- Every nontrivial additive character of a finite completion admits a self-dual Haar
measure, by the published p-adic existence theorem. -/
theorem nonempty_selfDualHaar (v : FinitePlace K)
    (ψv : @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology) :
    Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) ψv) := by
  let F := CompletionPadic.padicField v
  let T := CompletionPadic.topologicalData v
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨htd, hμ⟩ := HarmonicAnalysis.padicSelfDualMeasureExists F T
  let := htd
  obtain ⟨μ, hμ⟩ := hμ ψv
  exact ⟨⟨μ, hμ⟩⟩

/-- A canonical-topology additive character of `padicField v`, read in the completion
topology used by the Hecke functional equation (the two topologies are equal). -/
def ofCanonicalCharacter (v : FinitePlace K)
    (ψ' : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology where
  toAddChar := @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
    (Correspondence.instTopologicalSpaceCarrier _) ψ'
  continuous_toFun := by
    have h0 := @HarmonicAnalysis.UnitaryAdditiveCharacter.continuous_toFun _ _
      (Correspondence.instTopologicalSpaceCarrier _) ψ'
    have h : (CompletionPadic.topologicalData v).topology =
        Correspondence.instTopologicalSpaceCarrier (CompletionPadic.padicField v) :=
      CompletionPadic.completion_topology_eq v
    rw [h]
    exact h0
  nontrivial := @HarmonicAnalysis.UnitaryAdditiveCharacter.nontrivial _ _
    (Correspondence.instTopologicalSpaceCarrier _) ψ'

theorem ofCanonicalCharacter_toAddChar (v : FinitePlace K)
    (ψ' : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v)) :
    (ofCanonicalCharacter v ψ').toAddChar = @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar _ _
      (Correspondence.instTopologicalSpaceCarrier _) ψ' := rfl

section ArchData

/-- The archimedean data of the Hecke functional equation for `χ` and `ψ`: additive
components at the real and complex places and presentations of the archimedean components of
`χ` and `χ⁻¹`. -/
structure HeckeArchData (χ : HeckeCharacter K)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)) where
  aR : {v : InfinitePlace K // v.IsReal} → ℝˣ
  haR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)
  aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ
  haC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)
  dR : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData
  dR' : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData
  hdR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v)
  hdR' : ∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v)
  dC : {v : InfinitePlace K // v.IsComplex} → LocalFactor.Archimedean.ComplexCharacterData
  dC' : {v : InfinitePlace K // v.IsComplex} → LocalFactor.Archimedean.ComplexCharacterData
  hdC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v)
  hdC' : ∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v)

namespace HeckeArchData

variable {χ : HeckeCharacter K} {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)}

/-- The archimedean L-function `1 / D`. -/
def A (D : HeckeArchData χ ψ) (s : ℂ) : ℂ := (heckeInfiniteDenominator D.dR D.dC s)⁻¹

/-- The dual archimedean L-function. -/
def Ad (D : HeckeArchData χ ψ) (s : ℂ) : ℂ := (heckeInfiniteDenominator D.dR' D.dC' s)⁻¹

/-- The archimedean epsilon factor. -/
def Ae (D : HeckeArchData χ ψ) (s : ℂ) : ℂ := heckeInfiniteEpsilon D.dR D.dC D.aR D.aC s

theorem nonzeroMeromorphic_A (D : HeckeArchData χ ψ) : NonzeroMeromorphic D.A :=
  NonzeroMeromorphic.inv (nonzeroMeromorphic_heckeInfiniteDenominator D.dR D.dC)

theorem nonzeroMeromorphic_Ad (D : HeckeArchData χ ψ) : NonzeroMeromorphic D.Ad :=
  NonzeroMeromorphic.inv (nonzeroMeromorphic_heckeInfiniteDenominator D.dR' D.dC')

theorem nonzeroMeromorphic_Ae (D : HeckeArchData χ ψ) : NonzeroMeromorphic D.Ae := by
  have hdiff : Differentiable ℂ D.Ae := by
    unfold Ae heckeInfiniteEpsilon
    refine Differentiable.mul ?_ ?_
    · exact Differentiable.fun_finsetProd fun v _ =>
        LocalFactor.Archimedean.RealCharacterData.differentiable_epsilon _ _ _ _
    · exact Differentiable.fun_finsetProd fun v _ =>
        LocalFactor.Archimedean.ComplexCharacterData.differentiable_epsilon _ _ _ _
  refine nonzeroMeromorphic_of_ne_zero_halfPlane (fun x => (hdiff.analyticAt x).meromorphicAt) 0
    fun s _ => ?_
  unfold Ae heckeInfiniteEpsilon
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _)
    (Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _)

/-- The same data serve every character with the same archimedean components. -/
def ofInfiniteComponent_eq (D : HeckeArchData χ ψ) {χ' : HeckeCharacter K}
    (h : ∀ v, χ'.infiniteComponent v = χ.infiniteComponent v) : HeckeArchData χ' ψ where
  aR := D.aR
  haR := D.haR
  aC := D.aC
  haC := D.haC
  dR := D.dR
  dR' := D.dR'
  hdR v := by rw [h]; exact D.hdR v
  hdR' v := by rw [HeckeCharacter.infiniteComponent_inv, h]; exact D.hdR' v
  dC := D.dC
  dC' := D.dC'
  hdC v := by rw [h]; exact D.hdC v
  hdC' v := by rw [HeckeCharacter.infiniteComponent_inv, h]; exact D.hdC' v

@[simp] theorem ofInfiniteComponent_eq_A (D : HeckeArchData χ ψ) {χ' : HeckeCharacter K}
    (h : ∀ v, χ'.infiniteComponent v = χ.infiniteComponent v) :
    (D.ofInfiniteComponent_eq h).A = D.A := rfl

@[simp] theorem ofInfiniteComponent_eq_Ad (D : HeckeArchData χ ψ) {χ' : HeckeCharacter K}
    (h : ∀ v, χ'.infiniteComponent v = χ.infiniteComponent v) :
    (D.ofInfiniteComponent_eq h).Ad = D.Ad := rfl

@[simp] theorem ofInfiniteComponent_eq_Ae (D : HeckeArchData χ ψ) {χ' : HeckeCharacter K}
    (h : ∀ v, χ'.infiniteComponent v = χ.infiniteComponent v) :
    (D.ofInfiniteComponent_eq h).Ae = D.Ae := rfl

end HeckeArchData

/-- The Hecke functional equation provides archimedean data for every `χ` and every
nontrivial `ψ` trivial on `K`. -/
theorem nonempty_heckeArchData (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (χ : HeckeCharacter K) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ1 : ∃ x : Adeles K, ψ x ≠ 1) (hψ2 : ∀ x : K, ψ (diagonal K x) = 1) :
    Nonempty (HeckeArchData χ ψ) := by
  obtain ⟨⟨-, hR, hC⟩, -⟩ := hH K χ ψ hψ1 hψ2
  obtain ⟨⟨-, hR', hC'⟩, -⟩ := hH K χ⁻¹ ψ hψ1 hψ2
  choose aR haR using fun v : {v : InfinitePlace K // v.IsReal} => (hR v.1 v.2).1
  choose dR hdR using fun v : {v : InfinitePlace K // v.IsReal} => (hR v.1 v.2).2
  choose aC haC using fun v : {v : InfinitePlace K // v.IsComplex} => (hC v.1 v.2).1
  choose dC hdC using fun v : {v : InfinitePlace K // v.IsComplex} => (hC v.1 v.2).2
  choose dR' hdR' using fun v : {v : InfinitePlace K // v.IsReal} => (hR' v.1 v.2).2
  choose dC' hdC' using fun v : {v : InfinitePlace K // v.IsComplex} => (hC' v.1 v.2).2
  exact ⟨⟨aR, haR, aC, haC, dR, dR', hdR, hdR', dC, dC', hdC, hdC'⟩⟩

/-- The package of the Hecke functional equation, with archimedean data `D`. -/
theorem hasGlobalEquation_of_heckeArchData (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (χ : HeckeCharacter K) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ1 : ∃ x : Adeles K, ψ x ≠ 1) (hψ2 : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (D : HeckeArchData χ ψ) :
    ∃ S : Finset (FinitePlace K), (∀ v ∉ S, ∀ s : ℂ, finiteEpsilon χ ψf μ v s = 1) ∧
      HasGlobalEquation (heckeL χ) (heckeL χ⁻¹) (finiteEpsilon χ ψf μ) D.A D.Ad D.Ae S :=
  hasGlobalEquation_of_heckeFE hH χ ψ hψ1 hψ2 ψf hψf μ D.aR D.haR D.aC D.haC D.dR D.dR'
    D.hdR D.hdR' D.dC D.dC' D.hdC D.hdC'

end ArchData

section Pushforward

open NumberField IsDedekindDomain
open Langlands.Global.AdelicFunctoriality

variable {L : Type u} [Field L] [NumberField L] [Algebra K L]

/-- The finite places of `L` above a finite place `p` of `K`, as a finite set. -/
def placesAbove (L : Type u) [Field L] [NumberField L] [Algebra K L] (p : FinitePlace K) :
    Finset (FinitePlace L) :=
  Finset.univ.map ⟨fun q : FinitePlacesAbove L p => q.1, Subtype.val_injective⟩

theorem mem_placesAbove (q : FinitePlace L) (p : FinitePlace K) :
    q ∈ placesAbove L p ↔ q.under (𝓞 K) = p := by
  constructor
  · intro hq
    obtain ⟨q', -, rfl⟩ := Finset.mem_map.mp hq
    exact finitePlacesAbove_under p q'
  · intro hq
    subst hq
    exact Finset.mem_map.mpr ⟨⟨q, liesOver_under q⟩, Finset.mem_univ _, rfl⟩

/-- A package on the finite places of `L`, whose epsilon factors are `1` off its exceptional
set `S`, gives a package on the finite places of `K` with the products over the places
above, at any finite set `T` of places of `K` containing the places under `S`. -/
theorem HasGlobalEquation.pushforwardPlaces {l d e : FinitePlace L → ℂ → ℂ}
    {A Ad Ae : ℂ → ℂ} {S : Finset (FinitePlace L)} (h : HasGlobalEquation l d e A Ad Ae S)
    (hS : ∀ q ∉ S, ∀ s, e q s = 1) (T : Finset (FinitePlace K))
    (hT : ∀ q ∈ S, q.under (𝓞 K) ∈ T) :
    HasGlobalEquation (fun p s => ∏ q ∈ placesAbove L p, l q s)
      (fun p s => ∏ q ∈ placesAbove L p, d q s) (fun p s => ∏ q ∈ placesAbove L p, e q s)
      A Ad Ae T := by
  classical
  have h' : HasGlobalEquation l d e A Ad Ae (T.biUnion (placesAbove L)) := by
    refine h.changeSet (fun q hq hq' => ?_) (fun q _ hq' => hS q hq')
    exact absurd (Finset.mem_biUnion.mpr ⟨q.under (𝓞 K), hT q hq,
      (mem_placesAbove q _).mpr rfl⟩) hq'
  exact h'.pushforward (fun q : FinitePlace L => q.under (𝓞 K)) (placesAbove L)
    (fun q p => mem_placesAbove q p)

end Pushforward

end Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
