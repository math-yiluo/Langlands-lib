import Langlands.Global.EisensteinConstantTerm.UnfoldingMain

/-! # The intertwining side of the unfolding identity for abstract locally compact groups -/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup isClosed_conjStab

variable {𝒢 : Type u} [Group 𝒢] [TopologicalSpace 𝒢] [IsTopologicalGroup 𝒢] [T2Space 𝒢]
  [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢] [MeasurableSpace 𝒢] [BorelSpace 𝒢]

/-- A topological group automorphism of modulus one preserves the normalized Haar measure
`normalizedHaar Δ hΔ` of a discrete subgroup `Δ` for which one compact set meets every orbit. -/
theorem measurePreserving_normalizedHaar {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (Δ : Subgroup X) (hΔ : IsDiscrete (Δ : Set X))
    {K : Set X} (hK : IsCompact K) (hKcover : ∀ x, ∃ γ ∈ Δ, γ * x ∈ K)
    (φ : X ≃ₜ* X) (hφ : mulEquivHaarChar φ = 1) :
    MeasurePreserving φ (normalizedHaar Δ hΔ) (normalizedHaar Δ hΔ) := by
  have := isHaarMeasure_normalizedHaar Δ hΔ hK hKcover
  have := regular_normalizedHaar Δ hΔ
  refine ⟨φ.continuous.measurable, ?_⟩
  have h := mulEquivHaarChar_smul_map (normalizedHaar Δ hΔ) φ
  rwa [hφ, one_smul] at h

section Right

variable (R : Subgroup 𝒢) (hR : IsDiscrete (R : Set 𝒢))
  (V V' U' B : Subgroup 𝒢) [IsClosed (V : Set 𝒢)] [IsClosed (V' : Set 𝒢)]
  [IsClosed (U' : Set 𝒢)] [IsClosed (B : Set 𝒢)]
  (w : 𝒢) (hVV' : V ≤ V') (hBV' : B ≤ V') (hBU' : ∀ b ∈ B, w⁻¹ * b * w ∈ U')
  (hratV : ∀ x ∈ V', x ∈ R → ∀ v ∈ V, ∀ b ∈ B, v * b = x → b ∈ R)

include hR hBU' hratV in
/-- **Conjugation by the complement `B`.** Let `V, B ≤ V'` be closed with `w⁻¹ B w ⊆ U'`, and
let `pB : V' → B` be a continuous retraction with `pB = id` on `B` and kernel `V`, so that
`V' = V ⋊ B`; suppose the `B`-component of every element of `V' ∩ R` lies in `R`. If compact sets
meet every orbit of `V ∩ R` in `V`, of `V' ∩ R` in `V'` and of `V ∩ R ∩ w U' w⁻¹` in
`V ∩ w U' w⁻¹`, then for every `b ∈ B`, conjugation by `b⁻¹` preserves the normalized Haar
measures of `V` and of `V ∩ w U' w⁻¹` for these lattices. -/
theorem exists_conj_measurePreserving
    (pB : V' →* B) (hpc : Continuous pB) (hpj : ∀ m, pB (Subgroup.inclusion hBV' m) = m)
    (hpi : ∀ n, pB (Subgroup.inclusion hVV' n) = 1)
    (hker : ∀ h, pB h = 1 → ∃ n, Subgroup.inclusion hVV' n = h)
    {CV : Set V} (hCV : IsCompact CV) (hCVc : ∀ k, ∃ γ ∈ latticeOf R V, γ * k ∈ CV)
    {CV' : Set V'} (hCV' : IsCompact CV') (hCV'c : ∀ k, ∃ γ ∈ latticeOf R V', γ * k ∈ CV')
    {CN : Set (conjStab V U' w)} (hCN : IsCompact CN)
    (hCNc : ∀ k, ∃ γ ∈ conjStabLattice R V w U', γ * k ∈ CN) (b : B) :
    ∃ (φ : V ≃ₜ* V) (φN : conjStab V U' w ≃ₜ* conjStab V U' w),
      MeasurePreserving φ (normalizedHaar (latticeOf R V) (isDiscrete_latticeOf R hR V))
        (normalizedHaar (latticeOf R V) (isDiscrete_latticeOf R hR V)) ∧
      MeasurePreserving φN
        (normalizedHaar (conjStabLattice R V w U') (isDiscrete_conjStabLattice R hR V w U'))
        (normalizedHaar (conjStabLattice R V w U') (isDiscrete_conjStabLattice R hR V w U')) ∧
      (∀ n, (φN n : V) = φ n) ∧ ∀ v : V, ((φ v : V) : 𝒢) = b.val⁻¹ * v.val * b.val := by
  obtain ⟨-, ⟨CB, hCB, hCBc⟩, hδV, -⟩ := semidirect_haar R hR V' V B hVV' hBV' hratV pB hpc
    hpj hpi hker hCV hCVc hCV' hCV'c
  have hBd := isDiscrete_latticeOf R hR B
  have : IsFiniteMeasure (haarQuotientMeasure (latticeOf R B) hBd) :=
    isFiniteMeasure_haarQuotientMeasure_of_cover _ hBd hCB hCBc
  let i : V →* V' := Subgroup.inclusion hVV'
  let j : B →* V' := Subgroup.inclusion hBV'
  have hi : IsEmbedding i := IsEmbedding.inclusion hVV'
  have hj : Continuous j := continuous_inclusion hBV'
  let φ := Semidirect.conj i j pB hpj hker hpi hi hj b⁻¹
  have hφval : ∀ v : V, ((φ v : V) : 𝒢) = b.val⁻¹ * v.val * b.val := by
    intro v
    have h := congrArg Subtype.val (Semidirect.i_conj i j pB hpj hker hpi hi hj b⁻¹ v)
    simpa [i, j] using h
  -- the stabilizers
  set N := conjStab V U' w
  set N' := conjStab V' U' w
  let iN : N →* N' := ((Subgroup.inclusion hVV').comp N.subtype).codRestrict N'
    (fun n => (mem_conjStab _).mpr ((mem_conjStab n.val).mp n.property))
  let jN : B →* N' := (Subgroup.inclusion hBV').codRestrict N'
    (fun b => (mem_conjStab _).mpr (hBU' b.val b.property))
  let pN : N' →* B := pB.comp N'.subtype
  have hpjN : ∀ m, pN (jN m) = m := fun m => hpj m
  have hpiN : ∀ n, pN (iN n) = 1 := fun n => hpi n.val
  have hkerN : ∀ x, pN x = 1 → ∃ n, iN n = x := by
    intro x hx
    obtain ⟨v, hv⟩ := hker x.val hx
    have hvN : v ∈ N := by
      rw [mem_conjStab]
      have := (mem_conjStab x.val).mp x.property
      rwa [← hv] at this
    exact ⟨⟨v, hvN⟩, Subtype.ext hv⟩
  have hiN : IsEmbedding iN := by
    rw [← IsEmbedding.subtypeVal.of_comp_iff]
    exact hi.comp IsEmbedding.subtypeVal
  have hjN : Continuous jN := hj.subtype_mk _
  have hΓd := isDiscrete_conjStabLattice R hR V' w U'
  have hNd := isDiscrete_conjStabLattice R hR V w U'
  have hδN := Semidirect.mulEquivHaarChar_conj_eq_one iN jN pN hpjN hkerN hpiN hiN hjN
    (conjStabLattice R V' w U') hΓd hCN
    (fun n => by
      obtain ⟨γ, hγ, hγK⟩ := hCNc n
      exact ⟨γ, ⟨hγ.1, (iN γ).property⟩, hγK⟩)
    (latticeOf R B) hBd (fun γ hγ => ⟨hγ, (jN γ).property⟩) b⁻¹
  let φN := Semidirect.conj iN jN pN hpjN hkerN hpiN hiN hjN b⁻¹
  refine ⟨φ, φN, measurePreserving_normalizedHaar _ _ hCV hCVc φ (hδV b⁻¹),
    measurePreserving_normalizedHaar _ hNd hCN hCNc φN hδN, ?_, hφval⟩
  intro n
  apply Subtype.ext
  rw [hφval]
  have h := congrArg (fun x : N' => x.val.val)
    (Semidirect.i_conj iN jN pN hpjN hkerN hpiN hiN hjN b⁻¹ n)
  simpa [iN, jN] using h

variable (hVn : ∀ x ∈ V', ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hBV : ∀ b ∈ B, b ∈ V → b = 1)
  (hdecV : ∀ x ∈ V', ∃ v ∈ V, ∃ b ∈ B, v * b = x)

include hR hBV' hBU' hratV hVn hBV hdecV in
/-- **The intertwining side.** Let `V' = V ⋊ B` be a closed semidirect decomposition (`V`
normal in `V'`, `V ∩ B = 1`, `V' = V B`) with `w⁻¹ B w ⊆ U'`, such that the `B`-component of
every element of `V' ∩ R` lies in `R`. Suppose compact sets meet every orbit of `V ∩ R` in `V`, of
`V' ∩ R` in `V'` and of `V ∩ R ∩ w U' w⁻¹` in `V ∩ w U' w⁻¹`, and let `ν` be a compatible quotient
measure on `(V ∩ w U' w⁻¹) \ V` for the normalized Haar measures of these lattices. A measurable
function `Φ` on `V'`, left invariant under `V' ∩ w U' w⁻¹`, whose values at the chosen
representatives of the quotient are `ν`-integrable, is integrable on the chosen fundamental domain
of `V' ∩ R ∩ w U' w⁻¹` in `V'`, and its integral there equals the `ν`-integral of those values. -/
theorem integral_rightTransversal_eq
    {CV : Set V} (hCV : IsCompact CV) (hCVc : ∀ k, ∃ γ ∈ latticeOf R V, γ * k ∈ CV)
    {CV' : Set V'} (hCV' : IsCompact CV') (hCV'c : ∀ k, ∃ γ ∈ latticeOf R V', γ * k ∈ CV')
    {CN : Set (conjStab V U' w)} (hCN : IsCompact CN)
    (hCNc : ∀ k, ∃ γ ∈ conjStabLattice R V w U', γ * k ∈ CN)
    [MeasurableSpace (LeftQuotient (conjStab V U' w))]
    [BorelSpace (LeftQuotient (conjStab V U' w))]
    (μN : Measure (conjStab V U' w)) [SFinite μN] [μN.IsMulRightInvariant]
    [μN.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μN]
    (hμN : μN = normalizedHaar (conjStabLattice R V w U') (isDiscrete_conjStabLattice R hR V w U'))
    (ν : Measure (LeftQuotient (conjStab V U' w)))
    (hν : IsCompatible (conjStab V U' w)
      (normalizedHaar (latticeOf R V) (isDiscrete_latticeOf R hR V)) μN ν)
    (Φ : V' → ℂ) (hΦm : Measurable Φ) (hΦN : ∀ n ∈ conjStab V' U' w, ∀ x, Φ (n * x) = Φ x)
    (hint : Integrable (fun q => Φ (Subgroup.inclusion hVV' (Quotient.out q))) ν) :
    IntegrableOn Φ (fundamentalDomain (latticeOf R V' ⊓ conjStab V' U' w)
        ((isDiscrete_latticeOf R hR V').mono inf_le_left))
        (normalizedHaar (latticeOf R V') (isDiscrete_latticeOf R hR V')) ∧
      ∫ x in fundamentalDomain (latticeOf R V' ⊓ conjStab V' U' w)
          ((isDiscrete_latticeOf R hR V').mono inf_le_left), Φ x
          ∂normalizedHaar (latticeOf R V') (isDiscrete_latticeOf R hR V') =
        ∫ q, Φ (Subgroup.inclusion hVV' (Quotient.out q)) ∂ν := by
  subst hμN
  have hVd := isDiscrete_latticeOf R hR V
  have hBd := isDiscrete_latticeOf R hR B
  have hNd := isDiscrete_conjStabLattice R hR V w U'
  set μV := normalizedHaar (latticeOf R V) hVd
  have : μV.IsHaarMeasure := isHaarMeasure_normalizedHaar _ hVd hCV hCVc
  obtain ⟨pB, hpc, hpj, hpi, hker⟩ :=
    exists_retraction_of_semidirect V' V B hVV' hBV' hVn hBV hdecV
  obtain ⟨hΛp, ⟨CB, hCB, hCBc⟩, -, hμV'⟩ := semidirect_haar R hR V' V B hVV' hBV' hratV pB
    hpc hpj hpi hker hCV hCVc hCV' hCV'c
  set μB := normalizedHaar (latticeOf R B) hBd
  have hμBt : μB (fundamentalDomain (latticeOf R B) hBd) = 1 :=
    normalizedHaar_fundamentalDomain _ hBd hCB hCBc
  let i : V →* V' := Subgroup.inclusion hVV'
  let j : B →* V' := Subgroup.inclusion hBV'
  have hi : IsEmbedding i := IsEmbedding.inclusion hVV'
  have hj : Continuous j := continuous_inclusion hBV'
  set Γ' := latticeOf R V' ⊓ conjStab V' U' w
  set Γ₀ := latticeOf R V ⊓ conjStab V U' w
  have hΓ'd : IsDiscrete (Γ' : Set V') := (isDiscrete_latticeOf R hR V').mono inf_le_left
  have hΓ₀d : IsDiscrete (Γ₀ : Set V) := hVd.mono inf_le_left
  have : Countable Γ' := countable_of_isDiscrete _ hΓ'd
  have hΓ'p : ∀ x ∈ Γ', j (pB x) ∈ Γ' := fun x hx =>
    ⟨hΛp x hx.1, (mem_conjStab _).mpr (hBU' _ (pB x).property)⟩
  have hΓ'i : Γ'.comap i = Γ₀ := Subgroup.ext fun v => Iff.rfl
  have hΓ'j : Γ'.comap j = latticeOf R B := Subgroup.ext fun b =>
    ⟨fun h => h.1, fun h => ⟨h, (mem_conjStab _).mpr (hBU' b.val b.property)⟩⟩
  have htN : ∀ n, ∃! γ : Γ'.comap i, (γ : V) * n ∈ fundamentalDomain Γ₀ hΓ₀d := by
    rw [hΓ'i]; exact fundamentalDomain_unique Γ₀ hΓ₀d
  have htM : ∀ m, ∃! γ : Γ'.comap j, (γ : B) * m ∈ fundamentalDomain (latticeOf R B) hBd := by
    rw [hΓ'j]; exact fundamentalDomain_unique _ hBd
  have hΦΓ' : ∀ γ ∈ Γ', ∀ x, Φ (γ * x) = Φ x := fun γ hγ x => hΦN γ hγ.2 x
  have hprod := Semidirect.setIntegral_transversal_eq_prod i j pB hpj hker hpi hi hj hpc μV μB _
    hμV' Γ' hΓ'p (measurableSet_fundamentalDomain Γ' hΓ'd) (fundamentalDomain_unique Γ' hΓ'd)
    (measurableSet_fundamentalDomain Γ₀ hΓ₀d) htN (measurableSet_fundamentalDomain _ hBd) htM
    Φ hΦΓ'
  have hlprod := Semidirect.setLIntegral_transversal_eq_prod i j pB hpj hker hpi hi hj hpc μV μB _
    hμV' Γ' hΓ'p (measurableSet_fundamentalDomain Γ' hΓ'd) (fundamentalDomain_unique Γ' hΓ'd)
    (measurableSet_fundamentalDomain Γ₀ hΓ₀d) htN (measurableSet_fundamentalDomain _ hBd) htM
    (fun x => ‖Φ x‖ₑ) (fun γ hγ x => by rw [hΦΓ' γ hγ x])
  -- conjugation by elements of `B`
  choose φ φN hφ hφN hφNval hφval using fun b => exists_conj_measurePreserving R hR V V' U' B w
    hVV' hBV' hBU' hratV pB hpc hpj hpi hker hCV hCVc hCV' hCV'c hCN hCNc b
  let Ψ : V → ℂ := fun v => Φ (i v)
  have hΨm : Measurable Ψ := hΦm.comp (continuous_inclusion hVV').measurable
  have hΨN : ∀ n ∈ conjStab V U' w, ∀ v, Ψ (n * v) = Ψ v := by
    intro n hn v
    change Φ (i (n * v)) = Φ (i v)
    rw [map_mul]
    exact hΦN (i n) ((mem_conjStab _).mpr ((mem_conjStab n).mp hn)) _
  have hFval : ∀ (v : V) (b : B), Φ (i v * j b) = Ψ (φ b v) := by
    intro v b
    have hjb : j b ∈ conjStab V' U' w := (mem_conjStab _).mpr (hBU' b.val b.property)
    have heq : i v * j b = j b * i (φ b v) := by
      apply Subtype.ext
      change v.val * b.val = b.val * ((φ b v : V) : 𝒢)
      rw [hφval]
      group
    rw [heq]
    exact hΦN _ hjb _
  have hμNt := normalizedHaar_fundamentalDomain _ hNd hCN hCNc
  have hinnerL : ∀ b : B, ∫⁻ v in fundamentalDomain Γ₀ hΓ₀d, ‖Ψ (φ b v)‖ₑ ∂μV =
      ∫⁻ q, ‖Ψ (Quotient.out q)‖ₑ ∂ν := fun b =>
    lintegral_conj_eq_of_invariant (conjStab V U' w) (isClosed_conjStab V U' w) _ μV ν hν
      (φ b) (hφ b) (φN b) (hφN b) (hφNval b) Γ₀ hΓ₀d inf_le_right
      (measurableSet_fundamentalDomain _ hNd) (fundamentalDomain_unique _ hNd) hμNt
      (fun v => ‖Ψ v‖ₑ) hΨm.enorm (fun n hn v => by rw [hΨN n hn v])
  have hinner : ∀ b : B, ∫ v in fundamentalDomain Γ₀ hΓ₀d, Ψ (φ b v) ∂μV =
      ∫ q, Ψ (Quotient.out q) ∂ν := fun b =>
    (integral_conj_eq_of_invariant (conjStab V U' w) (isClosed_conjStab V U' w) _ μV ν hν
      (φ b) (hφ b) (φN b) (hφN b) (hφNval b) Γ₀ hΓ₀d inf_le_right
      (measurableSet_fundamentalDomain _ hNd) (fundamentalDomain_unique _ hNd) hμNt
      Ψ hΨm.stronglyMeasurable hΨN hint).2
  -- the integrand on the product
  set s := fundamentalDomain Γ₀ hΓ₀d
  set tB := fundamentalDomain (latticeOf R B) hBd
  let Fz : V × B → ℂ := fun z => Φ (i z.1 * j z.2)
  have hFm : Measurable Fz :=
    hΦm.comp ((hi.continuous.comp continuous_fst).mul (hj.comp continuous_snd)).measurable
  have hFlint : ∫⁻ z, ‖Fz z‖ₑ ∂((μV.restrict s).prod (μB.restrict tB)) =
      ∫⁻ q, ‖Ψ (Quotient.out q)‖ₑ ∂ν := by
    rw [lintegral_prod_symm _ hFm.enorm.aemeasurable]
    simp_rw [Fz, hFval, hinnerL]
    rw [setLIntegral_const, hμBt, mul_one]
  have hfin : ∫⁻ q, ‖Ψ (Quotient.out q)‖ₑ ∂ν < ∞ := hint.hasFiniteIntegral
  have hFint : Integrable Fz ((μV.restrict s).prod (μB.restrict tB)) :=
    ⟨hFm.aestronglyMeasurable, by rw [HasFiniteIntegral, hFlint]; exact hfin⟩
  refine ⟨⟨hΦm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [HasFiniteIntegral, hlprod, ← Measure.prod_restrict]
    change ∫⁻ z, ‖Fz z‖ₑ ∂((μV.restrict s).prod (μB.restrict tB)) < ∞
    rw [hFlint]
    exact hfin
  · rw [hprod, ← Measure.prod_restrict]
    change ∫ z, Fz z ∂((μV.restrict s).prod (μB.restrict tB)) = _
    rw [integral_prod_symm _ hFint]
    simp_rw [Fz, hFval, hinner]
    rw [setIntegral_const, Measure.real, hμBt, ENNReal.toReal_one, one_smul]


end Right

end Langlands.Global.LeftCosetSpace
