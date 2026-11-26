import Langlands.Automorphic.Unramified.CuspidalPairRamifiedGammaOrder
import Langlands.Automorphic.Unramified.WeakInductionGoodPairTwist
import Langlands.Automorphic.Unramified.WeakInductionNormTwistDepth
import Langlands.Global.Arithmetic.RamifiedTwistIsolationProof
import Langlands.Global.Factors.CuspidalPairTwistEngineInputs
import Langlands.Global.Factors.TwoTwistGammaOrderMatching

/-! # Localization of the gamma order for norm-twisted cuspidal pairs -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW uI

namespace Langlands.Global.CuspidalPairFunctionalEquation

open Filter Langlands.Global.FunctionalEquationComparison Langlands.Global.CompletionPadic
open Langlands.Global.AdelicFunctoriality LocalFactor RankinSelberg
open scoped NumberField Classical

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

private theorem normPullback_prescribedInfinity_one (χ : HeckeCharacter F)
    (hχ : χ.HasPrescribedInfinityComponent 1) :
    HeckeCharacter.HasPrescribedInfinityComponent
      (χ.comp (ideleClassNorm (K := F) (L := E))) 1 := by
  apply DFunLike.ext
  intro x
  let y := Units.map (infiniteAdeleNorm (K := F) (L := E)) x
  change χ (ideleClassNorm (K := F) (QuotientGroup.mk (infiniteIdelesInclusion E x))) = 1
  have hy : χ.atInfinity y = 1 := by rw [hχ]; rfl
  change χ (QuotientGroup.mk (infiniteIdelesInclusion F y)) = 1 at hy
  rw [ideleClassNorm_mk]
  refine (congrArg (fun a : Ideles F => χ (QuotientGroup.mk a)) ?_).trans hy
  apply Units.ext
  exact Prod.ext rfl (map_one (finiteAdeleNorm (K := F) (L := E)))

private theorem normPullback_finiteComponent_one (χ : HeckeCharacter F) (v : FinitePlace F)
    (w : FinitePlacesAbove E v) (hχ : χ.finiteComponent v = 1) :
    HeckeCharacter.finiteComponent (χ.comp (ideleClassNorm (K := F) (L := E))) w.1 = 1 := by
  ext a
  rw [Automorphic.Unramified.finiteComponent_comp_ideleClassNorm χ v w a, hχ]
  rfl

private theorem nontrivialOnPrincipalUnits_of_le {v : FinitePlace F}
    {χ : (FiniteCompletion F v)ˣ →ₜ* ℂˣ} {a b : ℕ} (h : a ≤ b)
    (hb : NontrivialOnPrincipalUnits v χ b) : NontrivialOnPrincipalUnits v χ a := by
  obtain ⟨x, hx, hχ⟩ := hb
  exact ⟨x, Ideal.pow_le_pow_right h hx, hχ⟩

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
variable {I : Type uI} [Fintype I]
variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {ψE : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles E)} {r t m n : ℕ}

/-- Cofinite spherical pair matching for both the ordinary and the contragredient factors. -/
def CofiniteSphericalPairMatching (D : AutomorphicTwistSetup.{uF,uV} ψ r t)
    (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n) : Prop :=
  ∀ᶠ v : FinitePlace F in cofinite,
    D.SphericalAt v ∧ (∀ (i : I) (w : FinitePlacesAbove E v), (U i).SphericalAt w.1) ∧
    (∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1) ∧
    ∀ z : ℂ,
      (D.localFactors 1 (.inr v)).lFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors 1) (.inr v)).lFactor z ∧
      (D.localFactors 1 (.inr v)).dualLFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors 1) (.inr v)).dualLFactor z

private theorem analyticAt_finite_epsilon (D : AutomorphicTwistSetup.{uF,uV} ψ r t)
    (χ : HeckeCharacter F) (v : FinitePlace F) (z : ℂ) :
    AnalyticAt ℂ (D.localFactors χ (.inr v)).epsilonFactor z ∧
      (D.localFactors χ (.inr v)).epsilonFactor z ≠ 0 := by
  let q := residueCardinality v
  let e := (D.finiteData χ v).2.2
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (FinitePairFactorChoice.one_lt_residueCardinality v))
  exact ⟨epsilonMonomial_analyticAt q hq e.1 e.2 z, epsilonMonomial_ne_zero q hq e.1 e.2 z⟩

omit [CompactSpace (AdeleQuotient F)] in
private theorem analyticAt_grouped_epsilon (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n)
    (ξ : HeckeCharacter E) (v : FinitePlace F) (z : ℂ) :
    let L := numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)
    AnalyticAt ℂ L.epsilonFactor z ∧ L.epsilonFactor z ≠ 0 := by
  have h : (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)).epsilonFactor =
      fun s => ∏ w : FinitePlacesAbove E v, ∏ i, ((U i).localFactors ξ (.inr w.1)).epsilonFactor s := by
    funext s
    exact Finset.prod_map _ _ _
  dsimp only
  rw [h]
  exact ⟨Finset.univ.analyticAt_fun_prod fun w _ => Finset.univ.analyticAt_fun_prod fun i _ =>
    (analyticAt_finite_epsilon (U i) ξ w.1 z).1,
    Finset.prod_ne_zero_iff.mpr fun w _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
      (analyticAt_finite_epsilon (U i) ξ w.1 z).2⟩

private theorem order_gamma_eq_of_pairFactors {D E' : LocalFactors} {z : ℂ}
    (hLmer : NonzeroMeromorphic D.lFactor) (hDmer : NonzeroMeromorphic D.dualLFactor)
    (hL : D.lFactor = E'.lFactor) (hD : D.dualLFactor = E'.dualLFactor)
    (hEps : AnalyticAt ℂ D.epsilonFactor z) (hEps₀ : D.epsilonFactor z ≠ 0)
    (hEps' : AnalyticAt ℂ E'.epsilonFactor z) (hEps₀' : E'.epsilonFactor z ≠ 0) :
    meromorphicOrderAt D.gamma z = meromorphicOrderAt E'.gamma z := by
  let R (s : ℂ) := D.dualLFactor (1 - s) / D.lFactor s
  have hR : MeromorphicAt R z := (hDmer.reflect.1 z).div (hLmer.1 z)
  have hZ : meromorphicOrderAt D.epsilonFactor z = 0 := by
    rw [hEps.meromorphicOrderAt_eq, hEps.analyticOrderAt_eq_zero.mpr hEps₀]
    rfl
  have hZ' : meromorphicOrderAt E'.epsilonFactor z = 0 := by
    rw [hEps'.meromorphicOrderAt_eq, hEps'.analyticOrderAt_eq_zero.mpr hEps₀']
    rfl
  have eqD : D.gamma = fun s => D.epsilonFactor s * R s := by
    funext s
    exact mul_div_assoc ..
  have eqE : E'.gamma = fun s => E'.epsilonFactor s * R s := by
    funext s
    rw [LocalFactors.gamma, ← hL, ← hD]
    exact mul_div_assoc ..
  rw [eqD, eqE]
  change meromorphicOrderAt (D.epsilonFactor * R) z = meromorphicOrderAt (E'.epsilonFactor * R) z
  rw [meromorphicOrderAt_mul hEps.meromorphicAt hR,
    meromorphicOrderAt_mul hEps'.meromorphicAt hR, hZ, hZ']

omit [CompactSpace (AdeleQuotient F)] in
private theorem order_grouped_gamma (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n)
    (ξ : HeckeCharacter E) (v : FinitePlace F) (z : ℂ)
    (h : ∀ (i : I) (w : FinitePlacesAbove E v),
      MeromorphicAt ((U i).localFactors ξ (.inr w.1)).gamma z) :
    meromorphicOrderAt (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)).gamma z =
      ∑ w : FinitePlacesAbove E v, ∑ i, meromorphicOrderAt ((U i).localFactors ξ (.inr w.1)).gamma z := by
  rw [show (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)).gamma =
    fun s => ∏ w : FinitePlacesAbove E v, ∏ i, ((U i).localFactors ξ (.inr w.1)).gamma s from
      funext fun s => (numberFieldProductFactors_finite _ v s).2.2]
  rw [meromorphicOrderAt_fun_prod (fun w _ => MeromorphicAt.fun_prod fun i _ => h i w)]
  exact Finset.sum_congr rfl fun w _ => meromorphicOrderAt_fun_prod fun i _ => h i w

set_option maxHeartbeats 2500000 in
private theorem comparisonInputs_normTwist
    (D : AutomorphicTwistSetup.{uF,uV} ψ r t)
    (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n)
    (hD : D.HasEngineInputs) (hU : ∀ i, (U i).HasEngineInputs)
    (χ : HeckeCharacter F) (hχ : χ.HasPrescribedInfinityComponent 1) (A : Finset (FinitePlace F))
    (hmatch : ∀ v ∉ A, ∀ s : ℂ,
      let ξ : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
      (D.localFactors χ (.inr v)).lFactor s =
        (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)).lFactor s ∧
      (D.localFactors χ (.inr v)).dualLFactor s =
        (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr v)).dualLFactor s) :
    ∃ B : Finset (FinitePlace F), A ⊆ B ∧
      ∃ a d a' d' : ℂ → ℂ,
        let ξ : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
        ComparisonInputs ⟨D.localFactors χ, a, d⟩
          ⟨numberFieldProductFactors (fun i => (U i).localFactors ξ), a', d'⟩
          (exceptionalPlaces F B) ∧
        ∀ (i : I) (v : FinitePlace F), v ∈ B → ∀ w : FinitePlacesAbove E v,
          NonzeroMeromorphic ((U i).localFactors ξ (.inr w.1)).gamma := by
  let ξ : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
  obtain ⟨B₀, hB₀⟩ := hD χ hχ
  have hSE (i : I) := hU i ξ (normPullback_prescribedInfinity_one χ hχ)
  choose C hC using hSE
  let B := A ∪ B₀ ∪ (Finset.univ.biUnion fun i => (C i).image (fun w => w.under (𝓞 F)))
  have hA : A ⊆ B := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hB : B₀ ⊆ B := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hBC (i : I) : C i ⊆ finitePlacesOver B := fun w hw => (mem_finitePlacesOver B w).mpr
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hw⟩))
  have hUpper (i : I) := hC i _ (hBC i)
  obtain ⟨σ, a, d, hA₀, hL, hEq⟩ := hB₀ B hB
  obtain ⟨σ', a', d', hA₀', hL', hEq'⟩ := numberFieldEquationGrouping F E I
    (fun i => (U i).localFactors ξ) B hUpper
  refine ⟨B, hA, a, d, a', d', ⟨hA₀, hA₀', hEq, hEq', max σ σ', ?_, ?_, ?_⟩, ?_⟩
  · exact HeckeEulerFamily.hasEulerProductsOutside_mono (le_max_left _ _) hL
  · exact HeckeEulerFamily.hasEulerProductsOutside_mono (le_max_right _ _) hL'
  · exact HeckeEulerFamily.matchesOutside_exceptionalPlaces fun v hv z _ =>
      hmatch v (fun hv' => hv (hA hv')) z
  · intro i v hv w
    obtain ⟨_, _, _, hAᵢ, -, -⟩ := hUpper i
    have hw : w.1 ∈ finitePlacesOver B := (mem_finitePlacesOver B w.1).mpr
      (by rw [finitePlacesAbove_under v w]; exact hv)
    have hmem : (Sum.inr w.1 : AllPlaces E) ∈ exceptionalPlaces E (finitePlacesOver B) := by
      simpa only [exceptionalPlaces, Finset.inr_mem_disjSum] using hw
    obtain ⟨hLᵢ, hLdᵢ, hεᵢ⟩ := hAᵢ.2.2 _ hmem
    exact local_gamma_nonzero ((U i).localFactors ξ (.inr w.1)) hLᵢ hLdᵢ hεᵢ

private theorem exists_normPair_depth (D : AutomorphicTwistSetup.{uF,uV} ψ r t)
    (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n) (v : FinitePlace F) :
    ∃ a : ℕ, ∀ χ : HeckeCharacter F, NontrivialOnPrincipalUnits v (χ.finiteComponent v) a →
      ∀ z : ℂ,
        meromorphicOrderAt (D.localFactors χ (.inr v)).gamma z = 0 ∧
        ∀ (i : I) (w : FinitePlacesAbove E v),
          meromorphicOrderAt ((U i).localFactors
            (χ.comp (ideleClassNorm (K := F) (L := E))) (.inr w.1)).gamma z = 0 := by
  obtain ⟨b, hb⟩ := cuspidalPairRamifiedGammaOrder F D v
  have hU (i : I) (w : FinitePlacesAbove E v) := cuspidalPairRamifiedGammaOrder E (U i) w.1
  choose c hc using hU
  have hNorm (i : I) (w : FinitePlacesAbove E v) :=
    Automorphic.Unramified.weakInductionNormTwistDepth F E v w (c i w)
  choose d hd using hNorm
  let a := b + ∑ j : I × FinitePlacesAbove E v, d j.1 j.2
  refine ⟨a, fun χ hχ z => ⟨?_, ?_⟩⟩
  · have hba : b ≤ a := Nat.le_add_right _ _
    exact hb χ (hba.trans (LocalFactor.NonabelianBrauer.lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits
      v (χ.finiteComponent v) a hχ rfl).le) z
  · intro i w
    have hda : d i w ≤ a :=
      (Finset.single_le_sum (f := fun j : I × FinitePlacesAbove E v => d j.1 j.2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, w))).trans (Nat.le_add_left _ _)
    exact hc i w _ (hd i w χ (nontrivialOnPrincipalUnits_of_le hda hχ)).le z

private theorem archimedean_finiteGamma_eq {K : Type*} [Field K] [NumberField K]
    {D E' : FiniteEulerData (AllPlaces K)}
    (h : ∀ x : NumberField.InfinitePlace K, D.localFactors (.inl x) = E'.localFactors (.inl x)) :
    D.finiteGamma (archimedeanBlock K) = E'.finiteGamma (archimedeanBlock K) := by
  funext z
  apply Finset.prod_congr rfl
  intro q hq
  cases q with
  | inl x => rw [h]
  | inr v => simp [archimedeanBlock] at hq

omit [CompactSpace (AdeleQuotient F)] in
private theorem grouped_factors_inl_eq
    (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n) (ξ ξ' : HeckeCharacter E)
    (x : NumberField.InfinitePlace F) :
    numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inl x) =
      numberFieldProductFactors (fun i => (U i).localFactors ξ') (.inl x) := by
  simp only [numberFieldProductFactors, placesAbove, Sum.elim_inl, localFactorsProduct,
    Finset.prod_map, Function.Embedding.coeFn_mk, AutomorphicTwistSetup.localFactors_inl]

/-- The functional-equation inputs of the supplied twist families, combined with
cofinite spherical pair matching, identify the untwisted local gamma order with
the sum of the upper orders over the whole fibre and family. -/
def NormTwistedPairGammaOrderStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (I : Type uI) [Fintype I]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    {ψE : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles E)} {r t m n : ℕ},
    ∀ (D : AutomorphicTwistSetup.{uF,uV} ψ r t) (U : I → AutomorphicTwistSetup.{uE,uW} ψE m n),
      D.HasEngineInputs → (∀ i, (U i).HasEngineInputs) →
      CofiniteSphericalPairMatching D U → ∀ (v : FinitePlace F) (s : ℂ),
        meromorphicOrderAt (D.localFactors 1 (.inr v)).gamma s =
          ∑ w : FinitePlacesAbove E v, ∑ i,
            meromorphicOrderAt ((U i).localFactors 1 (.inr w.1)).gamma s

set_option maxHeartbeats 2500000 in
theorem normTwistedPairGammaOrder : NormTwistedPairGammaOrderStatement.{uF,uE,uV,uW,uI} := by
  classical
  intro F E _ _ _ _ _ _ _ I _ ψ ψE r t m n D U hD hU hGood v s
  have hbad := Filter.eventually_cofinite.mp hGood
  let A := insert v hbad.toFinset
  have hvA : v ∈ A := Finset.mem_insert_self _ _
  have hMatch (χ : HeckeCharacter F) (p : FinitePlace F) (hp : p ∉ A) (z : ℂ) :
      let ξ : HeckeCharacter E := χ.comp (ideleClassNorm (K := F) (L := E))
      (D.localFactors χ (.inr p)).lFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr p)).lFactor z ∧
      (D.localFactors χ (.inr p)).dualLFactor z =
        (numberFieldProductFactors (fun i => (U i).localFactors ξ) (.inr p)).dualLFactor z := by
    have h := not_not.mp (fun hn => hp (Finset.mem_insert_of_mem (hbad.mem_toFinset.mpr hn)))
    exact weakInductionGoodPairTwist F E I D U p h.1 h.2.1 h.2.2.1 h.2.2.2 χ z
  choose depth hdepth using exists_normPair_depth D U
  obtain ⟨χ₁, -, -, hinf₁, hdeep₁⟩ := ramifiedTwistIsolation F ∅ A (by simp)
    (fun _ => 1) (fun p => depth p.1) (fun p => (Finset.notMem_empty p.1 p.2).elim)
  have hdisj : Disjoint ({v} : Finset (FinitePlace F)) (A.erase v) :=
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _)
  obtain ⟨χ₂, -, hfin₂, hinf₂, hdeep₂⟩ := ramifiedTwistIsolation F {v} (A.erase v) hdisj
    (fun _ => 1) (fun p => depth p.1) (fun _ => ⟨1, Nat.one_pos, pow_one _⟩)
  let ξ₁ : HeckeCharacter E := χ₁.comp (ideleClassNorm (K := F) (L := E))
  let ξ₂ : HeckeCharacter E := χ₂.comp (ideleClassNorm (K := F) (L := E))
  obtain ⟨B₁, hB₁, a₁, b₁, c₁, d₁, h₁, hmer₁⟩ := comparisonInputs_normTwist
    D U hD hU χ₁ hinf₁ A (hMatch χ₁)
  obtain ⟨B₂, hB₂, a₂, b₂, c₂, d₂, h₂, hmer₂⟩ := comparisonInputs_normTwist
    D U hD hU χ₂ hinf₂ A (hMatch χ₂)
  let S₁ := exceptionalPlaces F B₁
  let S₂ := exceptionalPlaces F B₂
  let arch := archimedeanBlock F
  let D₁ : FiniteEulerData (AllPlaces F) := ⟨D.localFactors χ₁, a₁, b₁⟩
  let D₂ : FiniteEulerData (AllPlaces F) := ⟨D.localFactors χ₂, a₂, b₂⟩
  let E₁ : FiniteEulerData (AllPlaces F) := ⟨numberFieldProductFactors (fun i => (U i).localFactors ξ₁), c₁, d₁⟩
  let E₂ : FiniteEulerData (AllPlaces F) := ⟨numberFieldProductFactors (fun i => (U i).localFactors ξ₂), c₂, d₂⟩
  have harch₁ : arch ⊆ S₁ := by
    intro q hq
    cases q <;> simp_all [arch, S₁, archimedeanBlock, exceptionalPlaces]
  have harch₂ : insert (Sum.inr v) arch ⊆ S₂ := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa [S₂, exceptionalPlaces] using hB₂ hvA
    · cases q <;> simp_all [arch, S₂, archimedeanBlock, exceptionalPlaces]
  have hvarch : Sum.inr v ∉ arch := by simp [arch, archimedeanBlock]
  have harchD : D₁.finiteGamma arch = D₂.finiteGamma arch := archimedean_finiteGamma_eq
    (fun x => (D.localFactors_inl χ₁ x).trans (D.localFactors_inl χ₂ x).symm)
  have harchE : E₁.finiteGamma arch = E₂.finiteGamma arch := archimedean_finiteGamma_eq
    (grouped_factors_inl_eq U ξ₁ ξ₂)
  have hAux (χ : HeckeCharacter F) (p : FinitePlace F)
      (hmer : NonzeroMeromorphic (D.localFactors χ (.inr p)).lFactor ∧
        NonzeroMeromorphic (D.localFactors χ (.inr p)).dualLFactor)
      (hmerU : ∀ (w : FinitePlacesAbove E p) (i : I), MeromorphicAt
        ((U i).localFactors (χ.comp (ideleClassNorm (K := F) (L := E))) (.inr w.1)).gamma s)
      (hdeep : p ∈ A → NontrivialOnPrincipalUnits p (χ.finiteComponent p) (depth p)) :
      meromorphicOrderAt (D.localFactors χ (.inr p)).gamma s =
        meromorphicOrderAt (numberFieldProductFactors
          (fun i => (U i).localFactors (χ.comp (ideleClassNorm (K := F) (L := E)))) (.inr p)).gamma s := by
    by_cases hp : p ∈ A
    · obtain ⟨hD, hU⟩ := hdepth p χ (hdeep hp) s
      rw [order_grouped_gamma U _ p s fun i w => hmerU w i, hD]
      simp [hU]
    · have heq := hMatch χ p hp
      obtain ⟨ha, hne⟩ := analyticAt_finite_epsilon D χ p s
      obtain ⟨ha', hne'⟩ := analyticAt_grouped_epsilon U _ p s
      exact order_gamma_eq_of_pairFactors hmer.1 hmer.2
        (funext fun z => (heq z).1) (funext fun z => (heq z).2) ha hne ha' hne'
  have hlocal := twoTwistGammaOrderMatching (AllPlaces F) S₁ S₂ arch (.inr v) D₁ E₁ D₂ E₂
    harch₁ harch₂ hvarch h₁ h₂ s (congrArg (fun f => meromorphicOrderAt f s) harchD)
    (congrArg (fun f => meromorphicOrderAt f s) harchE) ?_ ?_
  · have hv₂ : χ₂.finiteComponent v = 1 := hfin₂ ⟨v, Finset.mem_singleton_self _⟩
    have hL := D.localFactors_inr_of_finiteComponent_eq (χ := χ₂) (χ' := 1) hv₂
    have hvU (w : FinitePlacesAbove E v) (i : I) := (U i).localFactors_inr_of_finiteComponent_eq
      (χ := ξ₂) (χ' := 1) (normPullback_finiteComponent_one χ₂ v w hv₂)
    change meromorphicOrderAt (D.localFactors χ₂ (.inr v)).gamma s = _ at hlocal
    rw [hL, order_grouped_gamma U ξ₂ v s
      (fun i w => (hmer₂ i v (hB₂ hvA) w).1 s)] at hlocal
    simpa only [hvU] using hlocal
  · intro q hq hn
    cases q with
    | inl x => exact (hn (by simp [arch, archimedeanBlock])).elim
    | inr p =>
      have hp : p ∈ B₁ := by simpa only [S₁, exceptionalPlaces, Finset.inr_mem_disjSum] using hq
      have ha := h₁.1.2.2 (.inr p) hq
      exact hAux χ₁ p ⟨ha.1, ha.2.1⟩ (fun w i => (hmer₁ i p hp w).1 s)
        (fun hp' => hdeep₁ ⟨p, hp'⟩)
  · intro q hq hn
    cases q with
    | inl x => exact (hn (Finset.mem_insert_of_mem (by simp [arch, archimedeanBlock]))).elim
    | inr p =>
      have hp : p ∈ B₂ := by simpa only [S₂, exceptionalPlaces, Finset.inr_mem_disjSum] using hq
      have hpv : p ≠ v := fun h => hn (by simp [h])
      have ha := h₂.1.2.2 (.inr p) hq
      exact hAux χ₂ p ⟨ha.1, ha.2.1⟩ (fun w i => (hmer₂ i p hp w).1 s)
        (fun hp' => hdeep₂ ⟨p, Finset.mem_erase.mpr ⟨hpv, hp'⟩⟩)

end Langlands.Global.CuspidalPairFunctionalEquation
