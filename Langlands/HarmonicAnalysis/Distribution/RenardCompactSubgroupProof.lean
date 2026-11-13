import Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroupStatements
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionLawsProof

/-! # Renard II.3.11: proofs of the compact-subgroup distribution formulas -/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution

universe uH uG

section CompactHaar

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

omit [T2Space H] in
/-- Mathlib's Haar measure normalized on the whole compact group has mass one. -/
theorem haarMeasure_top_isProbabilityMeasure :
    IsProbabilityMeasure
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)) := by
  constructor
  have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

omit [T2Space H] in
/-- On a compact group the normalized Haar measure is also right invariant:
its right translate is again a Haar probability measure. -/
theorem haarMeasure_top_isMulRightInvariant :
    (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)).IsMulRightInvariant := by
  have := haarMeasure_top_isProbabilityMeasure (H := H)
  constructor
  intro g
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactHaar

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The normalized Haar integral over an actual compact subgroup of an ambient
scalar function; this is the integral used by `compactSubgroupHaar`. -/
def subgroupIntegral (K : Subgroup G) (hK : IsCompact (K : Set G)) (φ : G → ℂ) : ℂ :=
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  ∫ k : K, φ k.val ∂(Measure.haarMeasure ⊤)

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem subgroupIntegral_congr (K : Subgroup G) (hK : IsCompact (K : Set G))
    {φ ψ : G → ℂ} (h : ∀ k ∈ K, φ k = ψ k) :
    subgroupIntegral K hK φ = subgroupIntegral K hK ψ := by
  unfold subgroupIntegral
  congr 1
  funext k
  exact h k.val k.property

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem subgroupIntegral_const (K : Subgroup G) (hK : IsCompact (K : Set G)) (c : ℂ) :
    subgroupIntegral K hK (fun _ => c) = c := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have := haarMeasure_top_isProbabilityMeasure (H := K)
  change ∫ _ : K, c ∂(Measure.haarMeasure ⊤) = c
  rw [integral_const, probReal_univ, one_smul]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem subgroupIntegral_mul_left (K : Subgroup G) (hK : IsCompact (K : Set G))
    (φ : G → ℂ) {k₀ : G} (hk₀ : k₀ ∈ K) :
    subgroupIntegral K hK (fun x => φ (k₀ * x)) = subgroupIntegral K hK φ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  change ∫ k : K, φ (k₀ * k.val) ∂(Measure.haarMeasure ⊤) =
    ∫ k : K, φ k.val ∂(Measure.haarMeasure ⊤)
  exact integral_mul_left_eq_self (fun k : K => φ k.val) ⟨k₀, hk₀⟩

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem subgroupIntegral_mul_right (K : Subgroup G) (hK : IsCompact (K : Set G))
    (φ : G → ℂ) {k₀ : G} (hk₀ : k₀ ∈ K) :
    subgroupIntegral K hK (fun x => φ (x * k₀)) = subgroupIntegral K hK φ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have := haarMeasure_top_isMulRightInvariant (H := K)
  change ∫ k : K, φ (k.val * k₀) ∂(Measure.haarMeasure ⊤) =
    ∫ k : K, φ k.val ∂(Measure.haarMeasure ⊤)
  exact integral_mul_right_eq_self (fun k : K => φ k.val) ⟨k₀, hk₀⟩

theorem support_compactSubgroupHaar_subset (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    support (compactSubgroupHaar K hK : Distribution G) ⊆ (K : Set G) :=
  support_subset_of_mem_supportedOn hK.isClosed
    (compactSubgroupDistribution_mem_supportedOn K hK)

omit [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G] in
theorem support_dirac_subset (x : G) : support (dirac x : Distribution G) ⊆ {x} :=
  support_subset_of_mem_supportedOn isClosed_singleton (by
    intro f hf
    exact hf x (Set.mem_singleton x))

/-- The extended pairing of `e_K` with a locally constant function is the
normalized subgroup integral. -/
theorem compactSupportPairing_compactSubgroupHaar (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (f : LocallyConstant G ℂ) :
    compactSupportPairing (compactSubgroupHaar K hK) f = subgroupIntegral K hK f := by
  obtain ⟨g, hg⟩ := exists_testFunction_agrees_on_compact hK f
  rw [compactSupportPairing_eq_of_agrees (compactSubgroupHaar K hK) f g
    (fun x hx => hg x (support_compactSubgroupHaar_subset K hK hx))]
  change subgroupIntegral K hK (g : G → ℂ) = _
  exact subgroupIntegral_congr K hK hg

theorem leftDistributions_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) :
    GroupAction.leftDistributions k (compactSubgroupHaar K hK : Distribution G) =
      compactSubgroupHaar K hK := by
  ext f
  change subgroupIntegral K hK (GroupAction.leftTests k⁻¹ f : G → ℂ) =
    subgroupIntegral K hK (f : G → ℂ)
  rw [subgroupIntegral_congr K hK (ψ := fun x => f (k * x))
    (fun x _ => by rw [GroupAction.leftTests_apply, inv_inv])]
  exact subgroupIntegral_mul_left K hK f hk

theorem rightDistributions_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) :
    GroupAction.rightDistributions k (compactSubgroupHaar K hK : Distribution G) =
      compactSubgroupHaar K hK := by
  ext f
  change subgroupIntegral K hK (GroupAction.rightTests k⁻¹ f : G → ℂ) =
    subgroupIntegral K hK (f : G → ℂ)
  rw [subgroupIntegral_congr K hK (ψ := fun x => f (x * k⁻¹))
    (fun x _ => GroupAction.rightTests_apply _ _ _)]
  exact subgroupIntegral_mul_right K hK f (K.inv_mem hk)

theorem compactDirac_convolution_compactSubgroupHaar (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) :
    convolution (compactDirac k) (compactSubgroupHaar K hK) = compactSubgroupHaar K hK :=
  Subtype.ext ((convolution_dirac_left k _).trans
    (leftDistributions_compactSubgroupHaar K hK hk))

theorem compactSubgroupHaar_convolution_compactDirac (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) :
    convolution (compactSubgroupHaar K hK) (compactDirac k) = compactSubgroupHaar K hK :=
  Subtype.ext ((convolution_dirac_right k _).trans
    (rightDistributions_compactSubgroupHaar K hK (K.inv_mem hk)))

theorem leftDistributions_eq_of_convolution (k : G) (T : compactlySupported (X := G))
    (h : convolution (compactDirac k) T = T) :
    GroupAction.leftDistributions k (T : Distribution G) = T := by
  rw [← convolution_dirac_left, h]

theorem rightDistributions_eq_of_convolution (l : G) (T : compactlySupported (X := G))
    (h : convolution T (compactDirac l⁻¹) = T) :
    GroupAction.rightDistributions l (T : Distribution G) = T := by
  have he := convolution_dirac_right l⁻¹ T
  rw [inv_inv] at he
  rw [← he, h]

/-- Left `K`-invariant compact distributions absorb `e_K` on the left. -/
theorem compactSubgroupHaar_convolution_of_left (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (T : compactlySupported (X := G))
    (hT : ∀ k ∈ K, GroupAction.leftDistributions k (T : Distribution G) = T) :
    convolution (compactSubgroupHaar K hK) T = T := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing, compactSupportPairing_compactSubgroupHaar,
    subgroupIntegral_congr K hK (ψ := fun _ => (T : Distribution G) f),
    subgroupIntegral_const]
  intro k hk
  rw [compactPartial_apply, compactSupportPairing_eq_of_agrees T _
    (GroupAction.leftTests k⁻¹ f)]
  · exact congrArg (fun D : Distribution G => D f) (hT k hk)
  · intro y _
    simp [mulFunction]

/-- Right `L`-invariant compact distributions absorb `e_L` on the right. -/
theorem convolution_compactSubgroupHaar_of_right (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (T : compactlySupported (X := G))
    (hT : ∀ l ∈ L, GroupAction.rightDistributions l (T : Distribution G) = T) :
    convolution T (compactSubgroupHaar L hL) = T := by
  apply Subtype.ext
  ext f
  rw [convolution_eq_pairing, compactPairing_swap, compactSupportPairing_compactSubgroupHaar,
    subgroupIntegral_congr L hL (ψ := fun _ => (T : Distribution G) f),
    subgroupIntegral_const]
  intro l hl
  rw [compactPartial_apply, compactSupportPairing_eq_of_agrees T _
    (GroupAction.rightTests l f)]
  · have h := congrArg (fun D : Distribution G => D f) (hT l⁻¹ (L.inv_mem hl))
    simpa only [GroupAction.rightDistributions_apply, inv_inv] using h
  · intro x _
    simp [mulFunction]

theorem compactPartial_mulFunction_one (S : compactlySupported (X := G)) :
    compactPartial S (mulFunction (1 : LocallyConstant G ℂ)) =
      compactSupportPairing S 1 • (1 : LocallyConstant G ℂ) := by
  ext x
  simp only [compactPartial_apply, LocallyConstant.coe_smul, Pi.smul_apply,
    LocallyConstant.coe_one, Pi.one_apply, smul_eq_mul, mul_one]
  rfl

/-- Total mass is multiplicative under compact convolution. -/
theorem compactSupportPairing_convolution_one (T S : compactlySupported (X := G)) :
    compactSupportPairing (convolution T S) 1 =
      compactSupportPairing T 1 * compactSupportPairing S 1 := by
  rw [compactSupportPairing_convolution, compactPartial_mulFunction_one,
    compactSupportPairing_smul_right, smul_eq_mul, mul_comm]

theorem compactSupportPairing_compactSubgroupHaar_one (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    compactSupportPairing (compactSubgroupHaar K hK) 1 = 1 := by
  rw [compactSupportPairing_compactSubgroupHaar]
  exact subgroupIntegral_const K hK 1

omit [Group G] [IsTopologicalGroup G] in
theorem compactSupportPairing_compactDirac_one (x : G) :
    compactSupportPairing (compactDirac x) (1 : LocallyConstant G ℂ) = 1 :=
  compactSupportPairing_dirac x 1

/-- The locally constant function `y ↦ ∫_K ∫_L f(k y l)`, written through
the existing extended evaluations. -/
def biAverage (K L : Subgroup G) (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G))
    (f : SchwartzBruhat G) : LocallyConstant G ℂ :=
  compactPartial (compactSubgroupHaar K hK)
    ⟨fun p : G × G => mulFunction (compactPartial (compactSubgroupHaar L hL)
        (mulFunction ⟨(f : G → ℂ), f.locallyConstant⟩)) (p.2, p.1),
      (mulFunction (compactPartial (compactSubgroupHaar L hL)
        (mulFunction ⟨(f : G → ℂ), f.locallyConstant⟩))).isLocallyConstant.comp_continuous
          continuous_swap⟩

theorem convolution_three_apply (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (T : compactlySupported (X := G)) (f : SchwartzBruhat G) :
    (convolution (convolution (compactSubgroupHaar K hK) T) (compactSubgroupHaar L hL) :
        Distribution G) f =
      compactSupportPairing T (biAverage K L hK hL f) := by
  rw [convolution_eq_pairing, compactSupportPairing_convolution, compactPairing_swap]
  rfl

theorem biAverage_apply (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (f : SchwartzBruhat G) (y : G) :
    biAverage K L hK hL f y =
      subgroupIntegral K hK (fun k => subgroupIntegral L hL (fun l => f (k * y * l))) := by
  rw [biAverage, compactPartial_apply, compactSupportPairing_compactSubgroupHaar]
  apply subgroupIntegral_congr
  intro k _
  change compactSupportPairing (compactSubgroupHaar L hL) _ = _
  rw [compactSupportPairing_compactSubgroupHaar]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] in
theorem mul_mem_doubleCoset {K L : Subgroup G} {k l : G} (g : G) (hk : k ∈ K) (hl : l ∈ L) :
    k * g * l ∈ (K : Set G) * {g} * (L : Set G) :=
  Set.mul_mem_mul (Set.mul_mem_mul hk rfl) hl

theorem biAverage_eq_of_mem (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (f : SchwartzBruhat G) {g y : G}
    (hy : y ∈ (K : Set G) * {g} * (L : Set G)) :
    biAverage K L hK hL f y = biAverage K L hK hL f g := by
  obtain ⟨x, hx, l₀, hl₀, rfl⟩ := Set.mem_mul.mp hy
  obtain ⟨k₀, hk₀, g', hg', rfl⟩ := Set.mem_mul.mp hx
  rw [Set.mem_singleton_iff] at hg'
  subst hg'
  rw [biAverage_apply, biAverage_apply]
  have inner : ∀ x : G, subgroupIntegral L hL (fun l => f (x * l₀ * l)) =
      subgroupIntegral L hL (fun l => f (x * l)) := by
    intro x
    have h := subgroupIntegral_mul_left L hL (fun l => f (x * l)) hl₀
    simpa only [mul_assoc] using h
  calc subgroupIntegral K hK (fun k => subgroupIntegral L hL (fun l => f (k * (k₀ * g' * l₀) * l)))
      = subgroupIntegral K hK (fun k => subgroupIntegral L hL (fun l => f (k * k₀ * g' * l))) := by
        congr 1
        funext k
        rw [← inner (k * k₀ * g')]
        congr 1
        funext l
        group
    _ = subgroupIntegral K hK (fun k => subgroupIntegral L hL (fun l => f (k * g' * l))) :=
        subgroupIntegral_mul_right K hK
          (fun k => subgroupIntegral L hL (fun l => f (k * g' * l))) hk₀

/-- The source's final identification: every compact distribution with the
double-coset support, both invariances and mass one is `e_K * δ_g * e_L`. -/
theorem eq_doubleCoset (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G) (T : compactlySupported (X := G))
    (hsupp : support (T : Distribution G) ⊆ (K : Set G) * {g} * (L : Set G))
    (hleft : ∀ k ∈ K, GroupAction.leftDistributions k (T : Distribution G) = T)
    (hright : ∀ l ∈ L, GroupAction.rightDistributions l (T : Distribution G) = T)
    (hmass : compactSupportPairing T 1 = 1) :
    T = convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
      (compactSubgroupHaar L hL) := by
  have h1 := compactSubgroupHaar_convolution_of_left K hK T hleft
  have h2 := convolution_compactSubgroupHaar_of_right L hL T hright
  apply Subtype.ext
  ext f
  have hT : (T : Distribution G) f = (convolution (convolution (compactSubgroupHaar K hK) T)
      (compactSubgroupHaar L hL) : Distribution G) f := by
    rw [h1, h2]
  rw [hT, convolution_three_apply, convolution_three_apply, compactSupportPairing_dirac]
  rw [compactSupportPairing_congr T
    (g := biAverage K L hK hL f g • (1 : LocallyConstant G ℂ))]
  · rw [compactSupportPairing_smul_right, hmass, smul_eq_mul, mul_one]
  · intro y hy
    simp [biAverage_eq_of_mem K L hK hL f (hsupp hy)]

theorem support_doubleCoset_subset (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G) :
    support ((convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
      (compactSubgroupHaar L hL) : compactlySupported (X := G)) : Distribution G) ⊆
        (K : Set G) * {g} * (L : Set G) :=
  (support_convolutionDistribution_subset _ _).trans
    (Set.mul_subset_mul
      ((support_convolutionDistribution_subset _ _).trans
        (Set.mul_subset_mul (support_compactSubgroupHaar_subset K hK)
          (support_dirac_subset g)))
      (support_compactSubgroupHaar_subset L hL))

theorem leftDistributions_doubleCoset (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G) {k : G} (hk : k ∈ K) :
    GroupAction.leftDistributions k
      ((convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
        (compactSubgroupHaar L hL) : compactlySupported (X := G)) : Distribution G) =
      (convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
        (compactSubgroupHaar L hL) : compactlySupported (X := G)) := by
  apply leftDistributions_eq_of_convolution
  rw [← convolution_associative, ← convolution_associative,
    compactDirac_convolution_compactSubgroupHaar K hK hk]

theorem rightDistributions_doubleCoset (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G) {l : G} (hl : l ∈ L) :
    GroupAction.rightDistributions l
      ((convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
        (compactSubgroupHaar L hL) : compactlySupported (X := G)) : Distribution G) =
      (convolution (convolution (compactSubgroupHaar K hK) (compactDirac g))
        (compactSubgroupHaar L hL) : compactlySupported (X := G)) := by
  apply rightDistributions_eq_of_convolution
  rw [convolution_associative (convolution (compactSubgroupHaar K hK) (compactDirac g)),
    compactSubgroupHaar_convolution_compactDirac L hL (L.inv_mem hl)]

theorem mass_doubleCoset (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (g : G) :
    compactSupportPairing (convolution (convolution (compactSubgroupHaar K hK)
      (compactDirac g)) (compactSubgroupHaar L hL)) 1 = 1 := by
  rw [compactSupportPairing_convolution_one, compactSupportPairing_convolution_one,
    compactSupportPairing_compactSubgroupHaar_one, compactSupportPairing_compactDirac_one,
    compactSupportPairing_compactSubgroupHaar_one]
  norm_num

/-- `e_K * e_K = e_K` and the two absorption identities for `K ≤ L`. -/
theorem compactSubgroupHaar_convolution_of_le (K L : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (hKL : K ≤ L) :
    convolution (compactSubgroupHaar K hK) (compactSubgroupHaar L hL) =
        compactSubgroupHaar L hL ∧
      convolution (compactSubgroupHaar L hL) (compactSubgroupHaar K hK) =
        compactSubgroupHaar L hL :=
  ⟨compactSubgroupHaar_convolution_of_left K hK _
      (fun _ hk => leftDistributions_compactSubgroupHaar L hL (hKL hk)),
    convolution_compactSubgroupHaar_of_right K hK _
      (fun _ hk => rightDistributions_compactSubgroupHaar L hL (hKL hk))⟩

theorem compactSubgroupHaar_convolution_self (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    convolution (compactSubgroupHaar K hK) (compactSubgroupHaar K hK) =
      compactSubgroupHaar K hK :=
  (compactSubgroupHaar_convolution_of_le K K hK hK le_rfl).1

/-- Proposition (i): if the supplied compact subgroup has underlying set `KL`,
its normalized Haar distribution is `e_K * e_L`. -/
theorem compactSubgroupHaar_eq_convolution (K L M : Subgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (hM : IsCompact (M : Set G))
    (hMKL : (M : Set G) = (K : Set G) * (L : Set G)) :
    compactSubgroupHaar M hM = convolution (compactSubgroupHaar K hK)
      (compactSubgroupHaar L hL) := by
  have hKM : K ≤ M := by
    intro k hk
    change k ∈ (M : Set G)
    rw [hMKL]
    exact ⟨k, hk, 1, L.one_mem, mul_one k⟩
  have hLM : L ≤ M := by
    intro l hl
    change l ∈ (M : Set G)
    rw [hMKL]
    exact ⟨1, K.one_mem, l, hl, one_mul l⟩
  have h := eq_doubleCoset K L hK hL 1 (compactSubgroupHaar M hM) ?_
    (fun _ hk => leftDistributions_compactSubgroupHaar M hM (hKM hk))
    (fun _ hl => rightDistributions_compactSubgroupHaar M hM (hLM hl))
    (compactSupportPairing_compactSubgroupHaar_one M hM)
  · rwa [convolution_dirac_one_right] at h
  · intro x hx
    have hxM : x ∈ (M : Set G) := support_compactSubgroupHaar_subset M hM hx
    rw [hMKL] at hxM
    obtain ⟨k, hk, l, hl, rfl⟩ := hxM
    simpa only [mul_one] using mul_mem_doubleCoset (K := K) (L := L) 1 hk hl

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] in
theorem mem_conj_map_iff (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ ∃ k ∈ K, g * k * g⁻¹ = y := by
  simp [Subgroup.mem_map, MulAut.conj_apply]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem isCompact_conj_map (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have he : ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (fun x => g * x * g⁻¹) '' (K : Set G) := by
    ext y
    rw [SetLike.mem_coe, mem_conj_map_iff]
    rfl
  rw [he]
  exact hK.image (by fun_prop)

theorem support_conj_subset (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    support ((convolution (convolution (compactDirac g) (compactSubgroupHaar K hK))
      (compactDirac g⁻¹) : compactlySupported (X := G)) : Distribution G) ⊆
        {g} * (K : Set G) * {g⁻¹} :=
  (support_convolutionDistribution_subset _ _).trans
    (Set.mul_subset_mul
      ((support_convolutionDistribution_subset _ _).trans
        (Set.mul_subset_mul (support_dirac_subset g)
          (support_compactSubgroupHaar_subset K hK)))
      (support_dirac_subset g⁻¹))

/-- Dirac conjugation of `e_K` is `e_K'` for any compact subgroup `K'` whose
elements are exactly the conjugates `g k g⁻¹`, `k ∈ K`. -/
theorem convolution_conj_eq (K K' : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsCompact (K' : Set G)) (g : G)
    (hmem : ∀ y, y ∈ K' ↔ ∃ k ∈ K, g * k * g⁻¹ = y) :
    convolution (convolution (compactDirac g) (compactSubgroupHaar K hK))
        (compactDirac g⁻¹) = compactSubgroupHaar K' hK' := by
  have h := eq_doubleCoset K' K' hK' hK' 1
    (convolution (convolution (compactDirac g) (compactSubgroupHaar K hK)) (compactDirac g⁻¹))
    ?_ ?_ ?_ ?_
  · rw [convolution_dirac_one_right, compactSubgroupHaar_convolution_self] at h
    exact h
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp (support_conj_subset K hK g hx)
    obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.mp hy
    rw [Set.mem_singleton_iff] at ha hz
    rw [ha, hz]
    have hm : g * k * g⁻¹ ∈ K' := (hmem _).mpr ⟨k, hk, rfl⟩
    simpa only [mul_one] using mul_mem_doubleCoset (K := K') (L := K') 1 hm K'.one_mem
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (hmem x).mp hx
    apply leftDistributions_eq_of_convolution
    have hd : convolution (compactDirac (g * k * g⁻¹)) (compactDirac g) =
        convolution (compactDirac g) (compactDirac k) := by
      rw [convolution_dirac_dirac, convolution_dirac_dirac]
      congr 1
      group
    rw [← convolution_associative, ← convolution_associative, hd,
      convolution_associative (compactDirac g),
      compactDirac_convolution_compactSubgroupHaar K hK hk]
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (hmem x).mp hx
    apply rightDistributions_eq_of_convolution
    have hd : convolution (compactDirac g⁻¹) (compactDirac (g * k * g⁻¹)⁻¹) =
        convolution (compactDirac k⁻¹) (compactDirac g⁻¹) := by
      rw [convolution_dirac_dirac, convolution_dirac_dirac]
      congr 1
      group
    rw [convolution_associative, hd, ← convolution_associative,
      convolution_associative (compactDirac g),
      compactSubgroupHaar_convolution_compactDirac K hK (K.inv_mem hk)]
  · rw [compactSupportPairing_convolution_one, compactSupportPairing_convolution_one,
      compactSupportPairing_compactSubgroupHaar_one, compactSupportPairing_compactDirac_one,
      compactSupportPairing_compactDirac_one]
    norm_num

/-- Proposition (ii): Dirac conjugation of `e_K` is `e_(gKg⁻¹)`. -/
theorem convolution_conj_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    (g : G) :
    convolution (convolution (compactDirac g) (compactSubgroupHaar K hK))
        (compactDirac g⁻¹) =
      compactSubgroupHaar (K.map (MulAut.conj g).toMonoidHom) (isCompact_conj_map K hK g) :=
  convolution_conj_eq K _ hK (isCompact_conj_map K hK g) g (mem_conj_map_iff K g)

end Group

namespace RenardCompactSubgroup

theorem extendedIntegral : ExtendedIntegralStatement.{uG} := by
  intro G _ _ _ _ _ _ K hK f
  exact compactSupportPairing_compactSubgroupHaar K hK f

theorem doubleCosetUniqueness : DoubleCosetUniquenessStatement.{uG} := by
  intro G _ _ _ _ _ _ K L hK hL g
  exact ⟨support_doubleCoset_subset K L hK hL g,
    fun k => leftDistributions_doubleCoset K L hK hL g k.property,
    fun l => rightDistributions_doubleCoset K L hK hL g l.property,
    mass_doubleCoset K L hK hL g,
    fun T hsupp hleft hright hmass => eq_doubleCoset K L hK hL g T hsupp
      (fun k hk => hleft ⟨k, hk⟩) (fun l hl => hright ⟨l, hl⟩) hmass⟩

theorem product : ProductStatement.{uG} := by
  intro G _ _ _ _ _ _ K L M hK hL hM hMKL
  refine ⟨compactSubgroupHaar_eq_convolution K L M hK hL hM hMKL,
    compactSubgroupHaar_eq_convolution L K M hL hK hM ?_⟩
  ext x
  constructor
  · intro hx
    have hinv : x⁻¹ ∈ (M : Set G) := M.inv_mem hx
    rw [hMKL] at hinv
    obtain ⟨k, hk, l, hl, hkl⟩ := hinv
    refine ⟨l⁻¹, L.inv_mem hl, k⁻¹, K.inv_mem hk, ?_⟩
    change l⁻¹ * k⁻¹ = x
    have hkl' : k * l = x⁻¹ := hkl
    rw [← mul_inv_rev, hkl', inv_inv]
  · rintro ⟨l, hl, k, hk, rfl⟩
    have hinv : (l * k)⁻¹ ∈ (M : Set G) := by
      rw [hMKL, mul_inv_rev]
      exact ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, rfl⟩
    have h := M.inv_mem hinv
    rw [inv_inv] at h
    exact h

theorem conjugation : ConjugationStatement.{uG} := by
  intro G _ _ _ _ _ _ K hK g
  exact ⟨isCompact_conj_map K hK g, convolution_conj_compactSubgroupHaar K hK g⟩

theorem idempotenceAbsorption : IdempotenceAbsorptionStatement.{uG} := by
  intro G _ _ _ _ _ _
  exact ⟨fun K hK => compactSubgroupHaar_convolution_self K hK,
    fun K L hK hL hKL => compactSubgroupHaar_convolution_of_le K L hK hL hKL⟩

/-- All five II.3.11 targets, at the full group universe. -/
theorem statements : Statements.{uG} :=
  ⟨extendedIntegral, doubleCosetUniqueness, product, conjugation, idempotenceAbsorption⟩

end RenardCompactSubgroup
end Langlands.HarmonicAnalysis.Distribution
