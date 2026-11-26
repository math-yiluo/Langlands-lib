import Langlands.Global.EisensteinConstantTerm.UnfoldingStages
import Langlands.Global.EisensteinConstantTerm.UnfoldingLattices

/-! # The unfolding identity of the geometric lemma for abstract locally compact groups -/

noncomputable section

universe u v

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

/-- A closed subgroup of a locally compact group is locally compact. -/
theorem locallyCompactSpace_of_isClosed_subgroup {Y : Type*} [Group Y] [TopologicalSpace Y]
    [LocallyCompactSpace Y] (S : Subgroup Y) [h : IsClosed (S : Set Y)] :
    LocallyCompactSpace S :=
  h.locallyCompactSpace

/-- A subgroup of a second countable group is second countable. -/
theorem secondCountableTopology_subgroup {Y : Type*} [Group Y] [TopologicalSpace Y]
    [SecondCountableTopology Y] (S : Subgroup Y) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set Y)

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup

variable {𝒢 : Type u} [Group 𝒢] [TopologicalSpace 𝒢] [IsTopologicalGroup 𝒢] [T2Space 𝒢]
  [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢] [MeasurableSpace 𝒢] [BorelSpace 𝒢]
  (R : Subgroup 𝒢) (hR : IsDiscrete (R : Set 𝒢))

/-- The intersection of a subgroup `X` with `R`, as a subgroup of `X`. -/
abbrev latticeOf (X : Subgroup 𝒢) : Subgroup X := R.comap X.subtype

omit [IsTopologicalGroup 𝒢] [T2Space 𝒢] [LocallyCompactSpace 𝒢] [SecondCountableTopology 𝒢]
  [MeasurableSpace 𝒢] [BorelSpace 𝒢] in
include hR in
theorem isDiscrete_latticeOf (X : Subgroup 𝒢) : IsDiscrete (latticeOf R X : Set X) :=
  hR.preimage continuous_subtype_val.continuousOn Subtype.val_injective

section Semidirect

variable (H K A : Subgroup 𝒢) [IsClosed (H : Set 𝒢)] [IsClosed (K : Set 𝒢)]
  [IsClosed (A : Set 𝒢)]
  (hKH : K ≤ H) (hAH : A ≤ H) (hnorm : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
  (hdisj : ∀ a ∈ A, a ∈ K → a = 1) (hdec : ∀ x ∈ H, ∃ k ∈ K, ∃ a ∈ A, k * a = x)
  (hrat : ∀ x ∈ H, x ∈ R → ∀ k ∈ K, ∀ a ∈ A, k * a = x → a ∈ R)

omit [T2Space 𝒢] [MeasurableSpace 𝒢] [BorelSpace 𝒢] in
include hKH hAH hnorm hdisj hdec in
/-- The retraction of a closed semidirect decomposition `H = K ⋊ A` of closed subgroups. -/
theorem exists_retraction_of_semidirect :
    ∃ p : H →* A, Continuous p ∧ (∀ m, p (Subgroup.inclusion hAH m) = m) ∧
      (∀ n, p (Subgroup.inclusion hKH n) = 1) ∧
      (∀ h, p h = 1 → ∃ n, Subgroup.inclusion hKH n = h) := by
  let i : K →* H := Subgroup.inclusion hKH
  let j : A →* H := Subgroup.inclusion hAH
  have hj : Continuous j := continuous_inclusion hAH
  have hrange : (i.range : Set H) = Subtype.val ⁻¹' (K : Set 𝒢) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact k.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
  have hnormal : i.range.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : n.val ∈ K := by
      have : n ∈ (i.range : Set H) := hn
      rw [hrange] at this
      exact this
    have : (g * n * g⁻¹ : H) ∈ (i.range : Set H) := by
      rw [hrange]
      exact hnorm g.val g.property n.val hn'
    exact this
  have hclosed : IsClosed (i.range : Set H) := by
    rw [hrange]
    exact (inferInstance : IsClosed (K : Set 𝒢)).preimage continuous_subtype_val
  have hdec' : ∀ h : H, ∃ n m, i n * j m = h := by
    intro h
    obtain ⟨k, hk, a, ha, hka⟩ := hdec h.val h.property
    exact ⟨⟨k, hk⟩, ⟨a, ha⟩, Subtype.ext hka⟩
  have hdisj' : ∀ m, j m ∈ i.range → m = 1 := by
    intro m hm
    have : (j m : H) ∈ (i.range : Set H) := hm
    rw [hrange] at this
    exact Subtype.ext (hdisj m.val m.property this)
  exact exists_continuous_retraction i j hj hnormal hclosed hdec' hdisj'

omit [T2Space 𝒢] in
include hR hrat in
/-- **Haar measure of a closed semidirect product compatible with `R`.** For a continuous
retraction `p : H → A` with kernel `K`, under the compactness hypotheses of
`setIntegral_latticeOf_eq_of_semidirect`: `p` carries `H ∩ R` into `A ∩ R`; one compact set meets
every orbit of `A ∩ R` in `A`; conjugation by `A` preserves Haar measure on `K`; and the
normalized Haar measure of `H` is the image of the product of those of `K` and `A` under
`(k, a) ↦ k * a`. -/
theorem semidirect_haar (p : H →* A) (hpc : Continuous p)
    (hpj : ∀ m, p (Subgroup.inclusion hAH m) = m) (hpi : ∀ n, p (Subgroup.inclusion hKH n) = 1)
    (hker : ∀ h, p h = 1 → ∃ n, Subgroup.inclusion hKH n = h)
    {CK : Set K} (hCK : IsCompact CK) (hCKc : ∀ k, ∃ γ ∈ latticeOf R K, γ * k ∈ CK)
    {CH : Set H} (hCH : IsCompact CH) (hCHc : ∀ x, ∃ γ ∈ latticeOf R H, γ * x ∈ CH) :
    (∀ x ∈ latticeOf R H, Subgroup.inclusion hAH (p x) ∈ latticeOf R H) ∧
    (∃ CA : Set A, IsCompact CA ∧ ∀ a, ∃ γ ∈ latticeOf R A, γ * a ∈ CA) ∧
    (∀ m, mulEquivHaarChar (Semidirect.conj (Subgroup.inclusion hKH) (Subgroup.inclusion hAH) p
      hpj hker hpi (IsEmbedding.inclusion hKH) (continuous_inclusion hAH) m) = 1) ∧
    normalizedHaar (latticeOf R H) (isDiscrete_latticeOf R hR H) =
      Measure.map (Semidirect.prodHomeomorph (Subgroup.inclusion hKH) (Subgroup.inclusion hAH) p
        hpj hker hpi (IsEmbedding.inclusion hKH) (continuous_inclusion hAH) hpc)
        ((normalizedHaar (latticeOf R K) (isDiscrete_latticeOf R hR K)).prod
          (normalizedHaar (latticeOf R A) (isDiscrete_latticeOf R hR A))) := by
  let i : K →* H := Subgroup.inclusion hKH
  let j : A →* H := Subgroup.inclusion hAH
  have hi : IsEmbedding i := IsEmbedding.inclusion hKH
  have hj : Continuous j := continuous_inclusion hAH
  set Λ := latticeOf R H
  have hΛd := isDiscrete_latticeOf R hR H
  have hKd := isDiscrete_latticeOf R hR K
  have hAd := isDiscrete_latticeOf R hR A
  have : Countable Λ := countable_of_isDiscrete Λ hΛd
  have hΛp : ∀ x ∈ Λ, j (p x) ∈ Λ := by
    intro x hx
    have hdecx := Semidirect.i_normalPart_mul_j_p i j p hpj hker x
    exact hrat x.val x.property hx _ (Semidirect.normalPart i j p hpj hker x).property _
      (p x).property (congrArg Subtype.val hdecx)
  have hcoverA : ∃ CA : Set A, IsCompact CA ∧ ∀ a, ∃ γ ∈ latticeOf R A, γ * a ∈ CA :=
    exists_cover_of_map Λ hCH hCHc p hpc (fun a => ⟨j a, hpj a⟩) (latticeOf R A)
      (fun γ hγ => hΛp γ hγ)
  obtain ⟨CA, hCA, hCAc⟩ := hcoverA
  have : IsFiniteMeasure (haarQuotientMeasure (latticeOf R A) hAd) :=
    isFiniteMeasure_haarQuotientMeasure_of_cover _ hAd hCA hCAc
  have hδ := Semidirect.mulEquivHaarChar_conj_eq_one i j p hpj hker hpi hi hj Λ hΛd hCK
    (fun n => (hCKc n).imp fun γ hγ => hγ) (latticeOf R A) hAd (fun γ hγ => hγ)
  refine ⟨hΛp, ⟨CA, hCA, hCAc⟩, hδ, ?_⟩
  exact Semidirect.smul_haar_eq_map_prod i j p hpj hker hpi hi hj hpc hδ Λ hΛp
    (measurableSet_fundamentalDomain Λ hΛd) (fundamentalDomain_unique Λ hΛd)
    (measurableSet_fundamentalDomain _ hKd) (fundamentalDomain_unique _ hKd)
    (measurableSet_fundamentalDomain _ hAd) (fundamentalDomain_unique _ hAd)
    _ _ _ (inv_haar_mul_haar_fundamentalDomain Λ hΛd hCH hCHc)
    (inv_haar_mul_haar_fundamentalDomain _ hKd hCK hCKc)
    (inv_haar_mul_haar_fundamentalDomain _ hAd hCA hCAc)

omit [T2Space 𝒢] in
include hR hKH hAH hnorm hdisj hdec hrat in
/-- **Integration over a closed semidirect product.** Let `H = K ⋊ A` be a closed semidirect
decomposition of closed subgroups of `𝒢`, compatible with the discrete subgroup `R` (the
`A`-component of an element of `H ∩ R` lies in `R`), and suppose that one compact set meets every
orbit of `K ∩ R` in `K`, and one meets every orbit of `H ∩ R` in `H`. For each subgroup take the
Haar measure giving mass one to the chosen fundamental domain of its intersection with `R`. Then
for a function on `𝒢` that is left invariant under `K` and under `H ∩ R`, the integral over the
fundamental domain of `H ∩ R` in `H` is the integral over the fundamental domain of `A ∩ R` in
`A`. Moreover one compact set meets every orbit of `A ∩ R` in `A`. -/
theorem setIntegral_latticeOf_eq_of_semidirect
    {CK : Set K} (hCK : IsCompact CK) (hCKc : ∀ k, ∃ γ ∈ latticeOf R K, γ * k ∈ CK)
    {CH : Set H} (hCH : IsCompact CH) (hCHc : ∀ x, ∃ γ ∈ latticeOf R H, γ * x ∈ CH) :
    (∃ CA : Set A, IsCompact CA ∧ ∀ a, ∃ γ ∈ latticeOf R A, γ * a ∈ CA) ∧
    ∀ {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝒢 → E),
      (∀ k ∈ K, ∀ x, f (k * x) = f x) → (∀ γ ∈ H, γ ∈ R → ∀ x, f (γ * x) = f x) →
      ∫ x in fundamentalDomain (latticeOf R H) (isDiscrete_latticeOf R hR H), f x
          ∂normalizedHaar (latticeOf R H) (isDiscrete_latticeOf R hR H) =
        ∫ a in fundamentalDomain (latticeOf R A) (isDiscrete_latticeOf R hR A), f a
          ∂normalizedHaar (latticeOf R A) (isDiscrete_latticeOf R hR A) := by
  obtain ⟨p, hpc, hpj, hpi, hker⟩ :=
    exists_retraction_of_semidirect H K A hKH hAH hnorm hdisj hdec
  obtain ⟨hΛp, hcoverA, -, hμ⟩ := semidirect_haar R hR H K A hKH hAH hrat p hpc hpj hpi hker
    hCK hCKc hCH hCHc
  refine ⟨hcoverA, ?_⟩
  intro E _ _ f hfK hfR
  let i : K →* H := Subgroup.inclusion hKH
  let j : A →* H := Subgroup.inclusion hAH
  have hi : IsEmbedding i := IsEmbedding.inclusion hKH
  have hj : Continuous j := continuous_inclusion hAH
  have hΛd := isDiscrete_latticeOf R hR H
  have hKd := isDiscrete_latticeOf R hR K
  have hAd := isDiscrete_latticeOf R hR A
  have : Countable (latticeOf R H) := countable_of_isDiscrete _ hΛd
  have h := Semidirect.setIntegral_transversal_eq_of_invariant i j p hpj hker hpi hi hj hpc
    (normalizedHaar (latticeOf R K) hKd) (normalizedHaar (latticeOf R A) hAd)
    (normalizedHaar (latticeOf R H) hΛd) hμ (latticeOf R H) hΛp
    (measurableSet_fundamentalDomain _ hΛd) (fundamentalDomain_unique _ hΛd)
    (measurableSet_fundamentalDomain _ hKd) (fundamentalDomain_unique _ hKd)
    (measurableSet_fundamentalDomain _ hAd) (fundamentalDomain_unique _ hAd)
    (fun x : H => f x.val) (fun γ hγ x => hfR γ.val γ.property hγ x.val)
    (fun n x => hfK n.val n.property x.val)
  rw [h, normalizedHaar_fundamentalDomain _ hKd hCK hCKc, ENNReal.toReal_one, one_smul]
  rfl

end Semidirect

end Langlands.Global.LeftCosetSpace
