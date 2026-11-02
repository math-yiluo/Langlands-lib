import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical

/-! # `Ξ` through a Levi subgroup

Waldspurger 2003, Lemma II.1.6: for a parabolic subgroup `P = M U` containing `P₀`,
`Ξ(g) = ∫_K δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g)) dk`, where `m_P(g)` is the `M`-component of a
factorization `g = u_P(g) m_P(g) k_P(g)` and `Ξ^M` is the spherical function of `M` built
from `P₀ ∩ M` and `K ∩ M`. This module states and proves the identity for the abstract
Iwasawa data of `Spherical`, with the Levi projection given as a retraction `m_P : P →* M`.
-/

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

section Levi

variable {G : Type u} [Group G]
variable {K P₀ P M : Subgroup G}

/-- `G = P₀ K` and `P₀ ≤ P` give `G = P K`. -/
theorem IsIwasawaPair.mono (h : IsIwasawaPair P₀ K) (hle : P₀ ≤ P) : IsIwasawaPair P K :=
  fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := h g
    exact ⟨p, hle hp, k, hk, e⟩

/-- The Levi component `m_P(g) ∈ M` of a factorization `g = u_P(g) m_P(g) k_P(g)`
(Waldspurger I.1): the image under the Levi projection `m_P : P →* M` of the `P`-component
chosen by `iwasawaFactor`. -/
def leviComponent (hPK : IsIwasawaPair P K) (mP : P →* M) (g : G) : M :=
  mP (iwasawaFactor hPK g)

/-- The relations between the data `(P₀, K, δ₀)` of `G` and `(P₀ ∩ M, K ∩ M, δ₀^M)` of a Levi
subgroup `M` of `P ⊇ P₀` used in Waldspurger's Lemma II.1.6. Here `m_P` is the Levi
projection `P = M U → M`, whose kernel `U` lies in `P₀`; `δ₀` is trivial on `U` and equals
`δ_P δ₀^M` on `P₀ ∩ M`; and `δ_P` is trivial on `K ∩ M`. -/
structure LeviData (K P₀ P M : Subgroup G) (δ₀ : P₀ →* ℝ≥0ˣ) (δP : M →* ℝ≥0ˣ)
    (δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ) (mP : P →* M) : Prop where
  le_P₀ : P₀ ≤ P
  le_M : M ≤ P
  /-- `m_P` is the identity on `M`. -/
  apply_inclusion : ∀ m : M, mP (Subgroup.inclusion le_M m) = m
  /-- The kernel of `m_P` (the unipotent radical `U`) lies in `P₀`. -/
  mem_of_apply_eq_one : ∀ p : P, mP p = 1 → (p : G) ∈ P₀
  /-- `δ₀` is trivial on `U ⊆ P₀`. -/
  δ₀_of_apply_eq_one : ∀ p : P₀, mP (Subgroup.inclusion le_P₀ p) = 1 → δ₀ p = 1
  /-- `δ₀ = δ_P δ₀^M` on `P₀ ∩ M`. -/
  δ₀_of_mem : ∀ (p : P₀) (hp : (p : G) ∈ M), δ₀ p = δP ⟨p, hp⟩ * δ₀M ⟨⟨p, hp⟩, p.2⟩
  /-- `δ_P` is trivial on `K ∩ M`. -/
  δP_of_mem : ∀ m : M, (m : G) ∈ K → δP m = 1

variable {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}

/-- `M = (P₀ ∩ M)(K ∩ M)`, when `m_P` maps `P₀` into `P₀` and `P ∩ K` into `K`. -/
theorem LeviData.isIwasawaPair (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hP₀K : IsIwasawaPair P₀ K)
    (hmP₀ : ∀ p : P₀, (mP (Subgroup.inclusion hL.le_P₀ p) : G) ∈ P₀)
    (hmK : ∀ p : P, (p : G) ∈ K → (mP p : G) ∈ K) :
    IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M) := by
  intro m
  obtain ⟨p, hp, k, hk, e⟩ := hP₀K (m : G)
  have hkP : k ∈ P := by
    have : k = p⁻¹ * m := by rw [e, inv_mul_cancel_left]
    rw [this]
    exact P.mul_mem (P.inv_mem (hL.le_P₀ hp)) (hL.le_M m.2)
  have hsplit : Subgroup.inclusion hL.le_M m =
      Subgroup.inclusion hL.le_P₀ ⟨p, hp⟩ * ⟨k, hkP⟩ := Subtype.ext e
  refine ⟨mP (Subgroup.inclusion hL.le_P₀ ⟨p, hp⟩), hmP₀ ⟨p, hp⟩, mP ⟨k, hkP⟩,
    hmK ⟨k, hkP⟩ hk, ?_⟩
  rw [← map_mul, ← hsplit, hL.apply_inclusion]

/-- Pointwise form of Lemma II.1.6: for `p ∈ P` and `k_M ∈ K ∩ M`, the weight
`φ₀(x) = δ₀(p₀)^{1/2}` (`x = p₀ k`) of `G` at `k_M p` equals `δ_P(m_P(p))^{1/2}` times the
weight `φ₀^M` of `M` at `k_M m_P(p)`. -/
theorem LeviData.iwasawaWeight_mul (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (p : P) (kM : K.subgroupOf M) :
    iwasawaWeight hP₀K δ₀ (((kM : M) : G) * p) =
      NNReal.sqrt (δP (mP p) : ℝ≥0) * iwasawaWeight hM δ₀M ((kM : M) * mP p) := by
  set m : M := mP p with hm
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor hM ((kM : M) * m)
  set a := iwasawaFactor hM ((kM : M) * m) with ha
  -- `v = k' m⁻¹ p k'⁻¹` lies in `P` and in the kernel of `m_P`
  set v : P := Subgroup.inclusion hL.le_M k' * (Subgroup.inclusion hL.le_M m)⁻¹ * p *
    (Subgroup.inclusion hL.le_M k')⁻¹ with hv
  have hmv : mP v = 1 := by
    simp only [hv, map_mul, map_inv, hL.apply_inclusion, hm, inv_mul_cancel_right,
      mul_inv_cancel]
  have hvP₀ : (v : G) ∈ P₀ := hL.mem_of_apply_eq_one v hmv
  have haP₀ : ((a : M) : G) ∈ P₀ := a.2
  -- the factorization `k_M p = (a v) k'`
  have hfacG : ((kM : M) : G) * p = (((a : M) : G) * v) * ((k' : M) : G) := by
    have h1 : ((kM : M) : G) = ((a : M) : G) * ((k' : M) : G) * ((m : M) : G)⁻¹ := by
      have := congrArg (fun x : M => (x : G)) hfac
      simp only [Subgroup.coe_mul] at this
      rw [eq_mul_inv_iff_mul_eq, this]
    rw [h1, hv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  have hk'G : ((k' : M) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
  rw [hfacG, Langlands.HarishChandraSchwartz.iwasawaWeight_mul hδ₀
    (P₀.mul_mem haP₀ hvP₀) hk'G]
  -- evaluate `δ₀(a v) = δ_P(m) δ₀^M(a)`
  have hδv : δ₀ ⟨v, hvP₀⟩ = 1 := by
    refine hL.δ₀_of_apply_eq_one _ ?_
    have : Subgroup.inclusion hL.le_P₀ ⟨(v : G), hvP₀⟩ = v := Subtype.ext rfl
    rw [this, hmv]
  have hδa : δ₀ ⟨((a : M) : G), haP₀⟩ = δP m * δ₀M a := by
    rw [hL.δ₀_of_mem ⟨((a : M) : G), haP₀⟩ (a : M).2]
    have hδPa : δP (a : M) = δP m := by
      have h2 : (a : M) = (kM : M) * m * k'⁻¹ := by
        rw [hfac, mul_inv_cancel_right]
      rw [h2, map_mul, map_mul, map_inv, hL.δP_of_mem _ (Subgroup.mem_subgroupOf.mp kM.2),
        hL.δP_of_mem _ hk'G, one_mul, inv_one, mul_one]
    rw [← hδPa]
  have hmul : (⟨((a : M) : G) * v, P₀.mul_mem haP₀ hvP₀⟩ : P₀) =
      ⟨((a : M) : G), haP₀⟩ * ⟨v, hvP₀⟩ := rfl
  rw [hmul, map_mul, hδv, mul_one, hδa]
  unfold iwasawaWeight
  rw [← ha]
  simp only [Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul]

end Levi

section Integral

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {K P₀ P M : Subgroup G} [CompactSpace K] [CompactSpace (K.subgroupOf M)]
variable {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}

omit [CompactSpace K] in
/-- The integrand of Lemma II.1.6 does not depend on the factorization: for `p ∈ P` and
`k ∈ K`, `δ_P(m_P(p k))^{1/2} Ξ^M(m_P(p k)) = δ_P(m_P(p))^{1/2} Ξ^M(m_P(p))`, when `m_P` maps
`P ∩ K` into `K`. -/
theorem LeviData.sqrt_mul_xi_leviComponent_mul (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hPK : IsIwasawaPair P K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀M : ∀ p : P₀.subgroupOf M, ((p : M) : G) ∈ K → δ₀M p = 1)
    (hmK : ∀ p : P, (p : G) ∈ K → (mP p : G) ∈ K) (p : P) {k : G} (hk : k ∈ K) :
    NNReal.sqrt (δP (leviComponent hPK mP ((p : G) * k)) : ℝ≥0) *
        xi hM δ₀M (leviComponent hPK mP ((p : G) * k)) =
      NNReal.sqrt (δP (mP p) : ℝ≥0) * xi hM δ₀M (mP p) := by
  obtain ⟨k'', hk'', hfac⟩ := exists_iwasawaFactor hPK ((p : G) * k)
  set q := iwasawaFactor hPK ((p : G) * k) with hq
  -- `q⁻¹ p = k'' k⁻¹ ∈ P ∩ K`
  have hc : ((q⁻¹ * p : P) : G) ∈ K := by
    have h1 : ((q⁻¹ * p : P) : G) = k'' * k⁻¹ := by
      push_cast
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hfac, inv_mul_cancel_left]
    rw [h1]
    exact K.mul_mem hk'' (K.inv_mem hk)
  have hcM : mP (q⁻¹ * p) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr (hmK _ hc)
  have hp : mP p = mP q * mP (q⁻¹ * p) := by
    rw [← map_mul, mul_inv_cancel_left]
  have hl : leviComponent hPK mP ((p : G) * k) = mP q := rfl
  rw [hl, hp, map_mul, hL.δP_of_mem _ (Subgroup.mem_subgroupOf.mp hcM), mul_one,
    xi_mul_right hδ₀M _ hcM]

/-- Waldspurger, Lemma II.1.6: `Ξ(g) = ∫_K δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g)) dk`.
Second countability makes the Borel σ-algebra of `(K ∩ M) × K` the product σ-algebra, for
Fubini's theorem. -/
theorem LeviData.xi_eq_integral [SecondCountableTopology G]
    (hL : LeviData K P₀ P M δ₀ δP δ₀M mP) (hK : IsOpen (K : Set G))
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (g : G) :
    xi hP₀K δ₀ g =
      ∫ k : K, NNReal.sqrt (δP (leviComponent (hP₀K.mono hL.le_P₀) mP ((k : G) * g)) : ℝ≥0) *
        xi hM δ₀M (leviComponent (hP₀K.mono hL.le_P₀) mP ((k : G) * g)) ∂(normalizedHaar K) := by
  have : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have : SecondCountableTopology (K.subgroupOf M) :=
    TopologicalSpace.Subtype.secondCountableTopology ((K.subgroupOf M : Subgroup M) : Set M)
  set hPK := hP₀K.mono hL.le_P₀
  set μ := normalizedHaar K
  set ν := normalizedHaar (K.subgroupOf M)
  have hw : Continuous (iwasawaWeight hP₀K δ₀) := continuous_iwasawaWeight hδ₀ hK
  -- the double integrand on `(K ∩ M) × K`
  set F : K.subgroupOf M → K → ℝ :=
    fun kM k => iwasawaWeight hP₀K δ₀ (((kM : M) : G) * ((k : G) * g)) with hF
  have hFc : Continuous (Function.uncurry F) :=
    hw.comp ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
  have hFi : Integrable (Function.uncurry F) (ν.prod μ) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hFi
  -- the inner integral over `K ∩ M` is the integrand of the lemma
  have hinner : ∀ k : K, ∫ kM, F kM k ∂ν =
      NNReal.sqrt (δP (leviComponent hPK mP ((k : G) * g)) : ℝ≥0) *
        xi hM δ₀M (leviComponent hPK mP ((k : G) * g)) := by
    intro k
    obtain ⟨k'', hk'', hfac⟩ := exists_iwasawaFactor hPK ((k : G) * g)
    set q := iwasawaFactor hPK ((k : G) * g)
    have hpt : ∀ kM : K.subgroupOf M, F kM k =
        NNReal.sqrt (δP (leviComponent hPK mP ((k : G) * g)) : ℝ≥0) *
          iwasawaWeight hM δ₀M ((kM : M) * leviComponent hPK mP ((k : G) * g)) := by
      intro kM
      have h1 : ((kM : M) : G) * ((k : G) * g) = (((kM : M) : G) * (q : G)) * k'' := by
        rw [hfac, mul_assoc]
      show iwasawaWeight hP₀K δ₀ (((kM : M) : G) * ((k : G) * g)) = _
      rw [h1, iwasawaWeight_mul_right hδ₀ _ hk'']
      exact hL.iwasawaWeight_mul hP₀K hM hδ₀ q kM
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    rfl
  -- the inner integral over `K` is `Ξ(g)`, by left invariance
  have houter : ∀ kM : K.subgroupOf M, ∫ k, F kM k ∂μ = xi hP₀K δ₀ g := by
    intro kM
    have hkM : ((kM : M) : G) ∈ K := Subgroup.mem_subgroupOf.mp kM.2
    have hinv := integral_mul_left_eq_self (μ := μ)
      (fun k : K => iwasawaWeight hP₀K δ₀ ((k : G) * g)) ⟨_, hkM⟩
    simp only [Subgroup.coe_mul, mul_assoc] at hinv
    exact hinv
  calc xi hP₀K δ₀ g = ∫ _kM, xi hP₀K δ₀ g ∂ν := by simp
    _ = ∫ kM, ∫ k, F kM k ∂μ ∂ν := integral_congr_ae (Filter.Eventually.of_forall
        fun kM => (houter kM).symm)
    _ = ∫ k, ∫ kM, F kM k ∂ν ∂μ := hswap
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hinner)

end Integral

end Langlands.HarishChandraSchwartz
