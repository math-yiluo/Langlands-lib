import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.DeltaDecomposition
import Langlands.Representation.CuspidalSupport.DualAveraging
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Whittaker.Algebraic

/-!
# Invariant pairings with compact induction from a character are integrals

Let `N` be a subgroup of a σ-compact topological group `G` with a basis of compact open
subgroups at the identity, let `θ : N →* ℂˣ` be a character with open kernel, and let `ν` be a
nonzero right-invariant Borel measure on `N \ G` that is finite on compact sets. Every linear
functional on `c-Ind_N^G θ` that is invariant under a compact open subgroup `K` is integration
against a right `K`-invariant `θ⁻¹`-equivariant function, and that function is unique. As a
consequence, a `G`-invariant bilinear form on `c-Ind_N^G θ × π`, for a smooth representation
`π`, is integration against an intertwiner from `π` to the `θ⁻¹`-equivariant functions.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open MeasureTheory QuotientIntegration Induction Whittaker.CompletenessPairing

universe uG

section Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G}
  [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [OpensMeasurableSpace (QuotientIntegration.LeftQuotient N)]

/-- Images of open cosets have positive measure for a nonzero right-invariant measure. -/
theorem measure_orbit_pos [SigmaCompactSpace G] (ν : Measure (QuotientIntegration.LeftQuotient N))
    (hν0 : ν ≠ 0) (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (g : G) : 0 < ν (orbit N K g) := by
  classical
  rw [pos_iff_ne_zero]
  intro h0
  apply hν0
  let O := orbit N K g
  have hO : IsOpen O := isOpen_orbit N hK g
  let U : QuotientIntegration.LeftQuotient N → Set (QuotientIntegration.LeftQuotient N) :=
    fun q => rightTranslate N ((Quotient.out q)⁻¹ * g) ⁻¹' O
  have hU : ∀ q, U q ∈ nhds q := by
    intro q
    apply (hO.preimage (rightTranslate N _).continuous).mem_nhds
    have hq : rightTranslate N ((Quotient.out q)⁻¹ * g) q = Quotient.mk _ g := by
      have e : q = Quotient.mk _ (Quotient.out q) := (Quotient.out_eq q).symm
      calc rightTranslate N ((Quotient.out q)⁻¹ * g) q
          = rightTranslate N ((Quotient.out q)⁻¹ * g) (Quotient.mk _ (Quotient.out q)) :=
            congrArg (rightTranslate N ((Quotient.out q)⁻¹ * g)) e
        _ = Quotient.mk _ (Quotient.out q * ((Quotient.out q)⁻¹ * g)) := rightTranslate_mk _ _ _
        _ = Quotient.mk _ g := by rw [mul_inv_cancel_left]
    change rightTranslate N ((Quotient.out q)⁻¹ * g) q ∈ O
    rw [hq]
    exact mk_mem_orbit N K g
  obtain ⟨t, htc, htU⟩ := LindelofSpace.elim_nhds_subcover U hU
  have hnull : ∀ q, ν (U q) = 0 := by
    intro q
    rw [(hνinv _).measure_preimage hO.measurableSet.nullMeasurableSet]
    exact h0
  have huniv : ν Set.univ = 0 := by
    rw [← htU]
    exact (measure_biUnion_null_iff htc).mpr fun q _ => hnull q
  exact Measure.measure_univ_eq_zero.mp huniv

/-- Images of compact open cosets have finite measure for a regular measure. -/
theorem measure_orbit_lt_top (ν : Measure (QuotientIntegration.LeftQuotient N))
    [IsFiniteMeasureOnCompacts ν] {K : Subgroup G} (hK : IsCompact (K : Set G)) (g : G) :
    ν (orbit N K g) < ⊤ := by
  apply IsCompact.measure_lt_top
  have : orbit N K g = (fun k : G => (Quotient.mk _ (g * k) :
      QuotientIntegration.LeftQuotient N)) '' (K : Set G) := by
    ext q
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.val, k.property, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [this]
  exact hK.image ((continuous_quot_mk).comp (continuous_const.mul continuous_id))

theorem measureReal_orbit_ne_zero [SigmaCompactSpace G]
    (ν : Measure (QuotientIntegration.LeftQuotient N)) [IsFiniteMeasureOnCompacts ν]
    (hν0 : ν ≠ 0) (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) (g : G) :
    ν.real (orbit N K g) ≠ 0 := by
  rw [measureReal_def]
  exact (ENNReal.toReal_pos (measure_orbit_pos ν hν0 hνinv K.isOpen g).ne'
    (measure_orbit_lt_top ν hK g).ne).ne'

end Measure

section Representing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}
  [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [OpensMeasurableSpace (QuotientIntegration.LeftQuotient N)]
  (ν : Measure (QuotientIntegration.LeftQuotient N))

theorem orbit_mul_left (K : Subgroup G) (n : N) (g : G) :
    orbit N K ((n : G) * g) = orbit N K g := by
  apply orbit_eq_of_mk_mem
  refine ⟨1, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel _ (g * ((1 : K) : G)) ((n : G) * g)
  rw [QuotientGroup.rightRel_apply]
  simpa [mul_assoc] using n.property

theorem orbit_mul_right {K : Subgroup G} (g : G) {k : G} (hk : k ∈ K) :
    orbit N K (g * k) = orbit N K g :=
  orbit_eq_of_mk_mem ⟨⟨k, hk⟩, rfl⟩

theorem deltaVector_mul_left (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {g : G}
    (hg : IsGood N θ K g) (n : N) :
    deltaVector K hK ((n : G) * g) ((isGood_mul_left n).mpr hg) =
      ((((θ n)⁻¹ : ℂˣ) : ℂ)) • deltaVector K hK g hg := by
  apply compactFunctions_ext
  intro x
  rw [eval_deltaVector, eval_smul, eval_deltaVector, deltaFun_mul_left hg, smul_eq_mul]

theorem deltaVector_mul_right (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {g : G}
    (hg : IsGood N θ K g) {k : G} (hk : k ∈ (K : Subgroup G)) :
    deltaVector K hK (g * k) ((isGood_mul_right hk).mpr hg) = deltaVector K hK g hg := by
  apply compactFunctions_ext
  intro x
  rw [eval_deltaVector, eval_deltaVector, deltaFun_mul_right hg hk]

open Classical in
/-- The candidate representing function of a linear functional `L`, built from the delta
vectors of a compact open subgroup `K`. -/
def reprFun (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) : ℂ :=
  if h : IsGood N θ K g then L (deltaVector K hK g h) / ν.real (orbit N K g) else 0

theorem reprFun_isInverseEquivariant
    (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : IsInverseEquivariant θ (reprFun ν L K hK) := by
  classical
  intro n g
  by_cases hg : IsGood N θ K g
  · have hng : IsGood N θ K ((n : G) * g) := (isGood_mul_left n).mpr hg
    rw [reprFun, dif_pos hng, reprFun, dif_pos hg, deltaVector_mul_left K hK hg n, map_smul,
      orbit_mul_left, smul_eq_mul, mul_div_assoc]
  · have hng : ¬ IsGood N θ K ((n : G) * g) := fun h => hg ((isGood_mul_left n).mp h)
    rw [reprFun, dif_neg hng, reprFun, dif_neg hg, mul_zero]

theorem reprFun_right (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) {k : G}
    (hk : k ∈ (K : Subgroup G)) : reprFun ν L K hK (g * k) = reprFun ν L K hK g := by
  classical
  by_cases hg : IsGood N θ K g
  · have hgk : IsGood N θ K (g * k) := (isGood_mul_right hk).mpr hg
    rw [reprFun, dif_pos hgk, reprFun, dif_pos hg, deltaVector_mul_right K hK hg hk,
      orbit_mul_right g hk]
  · have hgk : ¬ IsGood N θ K (g * k) := fun h => hg ((isGood_mul_right hk).mp h)
    rw [reprFun, dif_neg hgk, reprFun, dif_neg hg]

/-- The product of a covariant vector and a `θ⁻¹`-equivariant function is left `N`-invariant. -/
theorem eval_mul_invariant (x : CompactFunctions N (characterRepresentation θ)) {f : G → ℂ}
    (hf : IsInverseEquivariant θ f) (n : N) (y : G) :
    eval _ _ x.1 ((n : G) * y) * f ((n : G) * y) = eval _ _ x.1 y * f y := by
  have h1 : eval _ _ x.1 ((n : G) * y) = (θ n : ℂ) * eval _ _ x.1 y := by
    have := x.1.1.property n y
    change eval _ _ x.1 ((n : G) * y) = (θ n : ℂ) • eval _ _ x.1 y at this
    rw [this, smul_eq_mul]
  rw [h1, hf]
  have : ((θ n : ℂˣ) : ℂ) * (((θ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (θ n : ℂ) * eval _ _ x.1 y * ((((θ n)⁻¹ : ℂˣ) : ℂ) * f y)
      = ((θ n : ℂ) * (((θ n)⁻¹ : ℂˣ) : ℂ)) * (eval _ _ x.1 y * f y) := by ring
    _ = eval _ _ x.1 y * f y := by rw [this, one_mul]

/-- The pairing of a vector with a `θ⁻¹`-equivariant function, as a function on `N \ G`. -/
def pairingFun (x : CompactFunctions N (characterRepresentation θ)) {f : G → ℂ}
    (hf : IsInverseEquivariant θ f) : QuotientIntegration.LeftQuotient N → ℂ :=
  descend N (fun y => eval _ _ x.1 y * f y) (eval_mul_invariant x hf)

/-- For a right `K`-invariant vector and function, the pairing function is a finite sum of
indicator functions of cosets. -/
theorem pairingFun_eq_sum (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : CompactFunctions N (characterRepresentation θ))
    (hx : ∀ y, ∀ k ∈ (K : Subgroup G), eval _ _ x.1 (y * k) = eval _ _ x.1 y)
    {f : G → ℂ} (hf : IsInverseEquivariant θ f)
    (hfK : ∀ y, ∀ k ∈ (K : Subgroup G), f (y * k) = f y) :
    ∃ s : Finset G, (∀ c ∈ s, eval _ _ x.1 c ≠ 0 → IsGood N θ K c) ∧
      x = ∑ c ∈ s, eval _ _ x.1 c • deltaVector' K hK c ∧
      pairingFun x hf = fun q => ∑ c ∈ s, eval _ _ x.1 c *
        (orbit N K c).indicator (fun _ => f c) q := by
  classical
  obtain ⟨s, hgood, hdec⟩ := exists_delta_decomposition K hK x hx
  refine ⟨s, hgood, hdec, ?_⟩
  funext q
  induction q using Quotient.inductionOn with
  | h y =>
    change eval _ _ x.1 y * f y = _
    have hy : eval _ _ x.1 y = ∑ c ∈ s, eval _ _ x.1 c *
        eval _ _ (deltaVector' (N := N) (θ := θ) K hK c).1 y := by
      conv_lhs => rw [hdec]
      rw [eval_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [eval_smul, smul_eq_mul]
    rw [hy, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hx0 : eval _ _ x.1 c = 0
    · rw [hx0, zero_mul, zero_mul, zero_mul]
    · have hgc := hgood c hc hx0
      rw [deltaVector'_of_good hgc, eval_deltaVector, mul_assoc]
      congr 1
      exact congrFun (descend_deltaFun_mul_eq_indicator hgc hf hfK) (Quotient.mk _ y)

theorem integrable_sum_indicator [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (s : Finset G) (a b : G → ℂ) :
    Integrable (fun q => ∑ c ∈ s, a c * (orbit N K c).indicator (fun _ => b c) q) ν := by
  apply integrable_finsetSum
  intro c _
  apply Integrable.const_mul
  rw [integrable_indicator_iff (isOpen_orbit N K.isOpen c).measurableSet]
  exact integrableOn_const (measure_orbit_lt_top ν hK c).ne

theorem integral_sum_indicator [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (s : Finset G) (a b : G → ℂ) :
    ∫ q, ∑ c ∈ s, a c * (orbit N K c).indicator (fun _ => b c) q ∂ν =
      ∑ c ∈ s, a c * (ν.real (orbit N K c) • b c) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, integral_indicator_const _ (isOpen_orbit N K.isOpen c).measurableSet]
  · intro c _
    apply Integrable.const_mul
    rw [integrable_indicator_iff (isOpen_orbit N K.isOpen c).measurableSet]
    exact integrableOn_const (measure_orbit_lt_top ν hK c).ne

/-- The representing function represents `L` on right `K`-invariant vectors. -/
theorem integral_pairingFun_reprFun [SigmaCompactSpace G] [IsFiniteMeasureOnCompacts ν]
    (hν0 : ν ≠ 0) (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (x : CompactFunctions N (characterRepresentation θ))
    (hx : ∀ y, ∀ k ∈ (K : Subgroup G), eval _ _ x.1 (y * k) = eval _ _ x.1 y) :
    ∫ q, pairingFun x (reprFun_isInverseEquivariant ν L K hK) q ∂ν = L x := by
  classical
  obtain ⟨s, hgood, hdec, hpt⟩ := pairingFun_eq_sum K hK x hx
    (reprFun_isInverseEquivariant ν L K hK) (fun y k hk => reprFun_right ν L K hK y hk)
  rw [hpt, integral_sum_indicator ν K hK]
  conv_rhs => rw [hdec]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [map_smul, smul_eq_mul]
  by_cases hx0 : eval _ _ x.1 c = 0
  · rw [hx0, zero_mul, zero_mul]
  · have hgc := hgood c hc hx0
    congr 1
    rw [reprFun, dif_pos hgc, deltaVector'_of_good hgc, Complex.real_smul, mul_div_cancel₀]
    exact_mod_cast measureReal_orbit_ne_zero ν hν0 hνinv hK c

end Representing

section Functional

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}
  [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [BorelSpace (QuotientIntegration.LeftQuotient N)]
  (ν : Measure (QuotientIntegration.LeftQuotient N)) [IsFiniteMeasureOnCompacts ν]

omit [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [BorelSpace (QuotientIntegration.LeftQuotient N)] [IsFiniteMeasureOnCompacts ν] in
theorem exists_compact_le
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
  obtain ⟨K, hK, hKU⟩ := hcof U (U.isOpen.mem_nhds U.one_mem)
  exact ⟨K, hK, fun x hx => hKU hx⟩

omit [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [BorelSpace (QuotientIntegration.LeftQuotient N)] [IsFiniteMeasureOnCompacts ν] in
/-- Every compactly induced vector is right invariant under a compact open subgroup inside a
given open subgroup. -/
theorem exists_compact_stabilizer
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (U : OpenSubgroup G)
    (x : CompactFunctions N (characterRepresentation θ)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U ∧
      ∀ y, ∀ k ∈ (K : Subgroup G), eval _ _ x.1 (y * k) = eval _ _ x.1 y := by
  obtain ⟨V, hV⟩ := x.1.property
  obtain ⟨K, hK, hKle⟩ := exists_compact_le hcof (U ⊓ V)
  refine ⟨K, hK, fun z hz => (hKle hz).1, ?_⟩
  intro y k hk
  have := congrArg (fun F : EquivariantFunctions N (characterRepresentation θ) => F.1 y)
    (hV ⟨k, (hKle hk).2⟩)
  exact this

/-- Pairing functions are integrable. -/
theorem integrable_pairingFun
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (x : CompactFunctions N (characterRepresentation θ))
    {f : G → ℂ} (hf : IsInverseEquivariant θ f) (K0 : OpenSubgroup G)
    (hfK : ∀ y, ∀ k ∈ (K0 : Subgroup G), f (y * k) = f y) :
    Integrable (pairingFun x hf) ν := by
  obtain ⟨K, hK, hKle, hx⟩ := exists_compact_stabilizer hcof K0 x
  obtain ⟨s, -, -, hpt⟩ := pairingFun_eq_sum K hK x hx hf (fun y k hk => hfK y k (hKle hk))
  rw [hpt]
  exact integrable_sum_indicator ν K hK s _ _

/-- Integration against a right invariant `θ⁻¹`-equivariant function, as a linear functional on
compact induction. -/
def pairingFunctional
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {f : G → ℂ} (hf : IsInverseEquivariant θ f) (K0 : OpenSubgroup G)
    (hfK : ∀ y, ∀ k ∈ (K0 : Subgroup G), f (y * k) = f y) :
    CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ where
  toFun x := ∫ q, pairingFun x hf q ∂ν
  map_add' x y := by
    have h : pairingFun (x + y) hf = pairingFun x hf + pairingFun y hf := by
      funext q
      induction q using Quotient.inductionOn with
      | h z =>
        change eval _ _ (x + y).1 z * f z = eval _ _ x.1 z * f z + eval _ _ y.1 z * f z
        rw [eval_add, add_mul]
    rw [h]
    exact integral_add (integrable_pairingFun ν hcof x hf K0 hfK)
      (integrable_pairingFun ν hcof y hf K0 hfK)
  map_smul' c x := by
    have h : pairingFun (c • x) hf = c • pairingFun x hf := by
      funext q
      induction q using Quotient.inductionOn with
      | h z =>
        change eval _ _ (c • x).1 z * f z = c • (eval _ _ x.1 z * f z)
        rw [eval_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
    rw [h, RingHom.id_apply]
    exact integral_smul c (pairingFun x hf)

theorem pairingFunctional_apply
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {f : G → ℂ} (hf : IsInverseEquivariant θ f) (K0 : OpenSubgroup G)
    (hfK : ∀ y, ∀ k ∈ (K0 : Subgroup G), f (y * k) = f y)
    (x : CompactFunctions N (characterRepresentation θ)) :
    pairingFunctional ν hcof hf K0 hfK x = ∫ q, pairingFun x hf q ∂ν := rfl

/-- Right translation of the vector translates the pairing function. -/
theorem pairingFun_translate {f : G → ℂ} (hf : IsInverseEquivariant θ f)
    (x : CompactFunctions N (characterRepresentation θ)) {k : G} (hfk : ∀ y, f (y * k) = f y) :
    pairingFun (compactInduced N (characterRepresentation θ) k x) hf =
      pairingFun x hf ∘ rightTranslate N k := by
  funext q
  induction q using Quotient.inductionOn with
  | h z =>
    change eval _ _ x.1 (z * k) * f z = eval _ _ x.1 (z * k) * f (z * k)
    rw [hfk]

theorem pairingFunctional_translate
    (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {f : G → ℂ} (hf : IsInverseEquivariant θ f) (K0 : OpenSubgroup G)
    (hfK : ∀ y, ∀ k ∈ (K0 : Subgroup G), f (y * k) = f y)
    (x : CompactFunctions N (characterRepresentation θ)) {k : G}
    (hk : k ∈ (K0 : Subgroup G)) :
    pairingFunctional ν hcof hf K0 hfK (compactInduced N (characterRepresentation θ) k x) =
      pairingFunctional ν hcof hf K0 hfK x := by
  rw [pairingFunctional_apply, pairingFunctional_apply,
    pairingFun_translate hf x (fun y => hfK y k hk)]
  exact (hνinv k).integral_comp (rightTranslate N k).measurableEmbedding _

/-- A linear functional fixed by a compact open subgroup under the dual action. -/
theorem mem_fixedVectors_dual_of_invariant
    (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ) (K0 : OpenSubgroup G)
    (hL : ∀ k ∈ (K0 : Subgroup G), ∀ x,
      L (compactInduced N (characterRepresentation θ) k x) = L x) :
    L ∈ fixedVectors (compactInduced N (characterRepresentation θ)).dual K0.toSubgroup := by
  intro k
  apply LinearMap.ext
  intro v
  change ((compactInduced N (characterRepresentation θ)).dual (k : G) L) v = L v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  exact hL _ (K0.toSubgroup.inv_mem k.property) v

/-- Every linear functional fixed by a compact open subgroup `K0` is integration against its
representing function. -/
theorem eq_pairingFunctional_reprFun [SigmaCompactSpace G] (hν0 : ν ≠ 0)
    (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (L : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ) (K0 : OpenSubgroup G)
    (hK0 : IsCompact (K0 : Set G))
    (hL : ∀ k ∈ (K0 : Subgroup G), ∀ x,
      L (compactInduced N (characterRepresentation θ) k x) = L x)
    (x : CompactFunctions N (characterRepresentation θ)) :
    L x = pairingFunctional ν hcof (reprFun_isInverseEquivariant ν L K0 hK0) K0
      (fun y k hk => reprFun_right ν L K0 hK0 y hk) x := by
  let ρ := compactInduced N (characterRepresentation θ)
  have hρ : IsSmooth ρ := compactInduced_smooth _ _
  let x' := Compact.averageMap ρ hρ K0 hK0 x
  have hfix := Compact.averageMap_mem_fixedVectors ρ hρ K0 hK0 x
  have hx' : ∀ y, ∀ k ∈ (K0 : Subgroup G), eval _ _ x'.1 (y * k) = eval _ _ x'.1 y := by
    intro y k hk
    have := congrArg (fun z : CompactFunctions N (characterRepresentation θ) => eval _ _ z.1 y)
      (hfix ⟨k, hk⟩)
    exact this
  let Λ := pairingFunctional ν hcof (reprFun_isInverseEquivariant ν L K0 hK0) K0
    (fun y k hk => reprFun_right ν L K0 hK0 y hk)
  have h1 : L x' = L x :=
    Compact.dual_averageMap_eq_of_mem_fixedVectors ρ hρ K0 hK0 L
      (mem_fixedVectors_dual_of_invariant L K0 hL) x
  have h2 : Λ x' = Λ x :=
    Compact.dual_averageMap_eq_of_mem_fixedVectors ρ hρ K0 hK0 Λ
      (mem_fixedVectors_dual_of_invariant Λ K0 (fun k hk z =>
        pairingFunctional_translate ν hνinv hcof _ K0 _ z hk)) x
  have h3 : Λ x' = L x' := integral_pairingFun_reprFun ν hν0 hνinv L K0 hK0 x' hx'
  rw [← h1, ← h3, h2]

/-- Good compact open subgroups exist inside every open subgroup, for a character with open
kernel. -/
theorem exists_good_compact (hθ : IsOpen (θ.ker : Set N))
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (U : OpenSubgroup G) (g : G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U ∧ IsGood N θ K g := by
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hθ
  have h1 : (1 : G) ∈ O := by
    have : (1 : N) ∈ (Subtype.val ⁻¹' O) := by rw [hOeq]; exact θ.ker.one_mem
    exact this
  have hW : (U : Set G) ∩ (fun y => g * y * g⁻¹) ⁻¹' O ∈ nhds (1 : G) := by
    apply Filter.inter_mem (U.isOpen.mem_nhds U.one_mem)
    apply (hO.preimage (by continuity)).mem_nhds
    simpa using h1
  obtain ⟨K, hK, hKW⟩ := hcof _ hW
  refine ⟨K, hK, fun y hy => (hKW hy).1, ?_⟩
  intro n hn
  have hO' : g * (g⁻¹ * (n : G) * g) * g⁻¹ ∈ O := (hKW hn).2
  have hn' : (n : G) ∈ O := by simpa [mul_assoc] using hO'
  have : n ∈ (Subtype.val ⁻¹' O : Set N) := hn'
  rw [hOeq] at this
  exact this

/-- Uniqueness of representing functions. -/
theorem eq_of_pairingFunctional_eq [SigmaCompactSpace G] (hν0 : ν ≠ 0)
    (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hθ : IsOpen (θ.ker : Set N))
    {f₁ f₂ : G → ℂ} (hf₁ : IsInverseEquivariant θ f₁) (hf₂ : IsInverseEquivariant θ f₂)
    (K₁ K₂ : OpenSubgroup G) (hfK₁ : ∀ y, ∀ k ∈ (K₁ : Subgroup G), f₁ (y * k) = f₁ y)
    (hfK₂ : ∀ y, ∀ k ∈ (K₂ : Subgroup G), f₂ (y * k) = f₂ y)
    (h : ∀ x, pairingFunctional ν hcof hf₁ K₁ hfK₁ x = pairingFunctional ν hcof hf₂ K₂ hfK₂ x) :
    f₁ = f₂ := by
  funext g
  obtain ⟨K, hK, hKle, hg⟩ := exists_good_compact hθ hcof (K₁ ⊓ K₂) g
  have hx := h (deltaVector K hK g hg)
  rw [pairingFunctional_apply, pairingFunctional_apply] at hx
  have e₁ : pairingFun (deltaVector K hK g hg) hf₁ =
      descend N (fun y => deltaFun N θ K g y * f₁ y) (deltaFun_mul_invariant hg hf₁) := rfl
  have e₂ : pairingFun (deltaVector K hK g hg) hf₂ =
      descend N (fun y => deltaFun N θ K g y * f₂ y) (deltaFun_mul_invariant hg hf₂) := rfl
  rw [e₁, e₂, integral_deltaFun_mul ν K.isOpen hg hf₁ (fun y k hk => hfK₁ y k (hKle hk).1),
    integral_deltaFun_mul ν K.isOpen hg hf₂ (fun y k hk => hfK₂ y k (hKle hk).2)] at hx
  have hne : (ν.real (orbit N K g) : ℂ) ≠ 0 := by
    exact_mod_cast measureReal_orbit_ne_zero ν hν0 hνinv hK g
  rw [Complex.real_smul, Complex.real_smul] at hx
  exact mul_left_cancel₀ hne hx

end Functional

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}
  [MeasurableSpace (QuotientIntegration.LeftQuotient N)]
  [BorelSpace (QuotientIntegration.LeftQuotient N)]
  (ν : Measure (QuotientIntegration.LeftQuotient N)) [IsFiniteMeasureOnCompacts ν]

theorem IsInverseEquivariant.add {f₁ f₂ : G → ℂ} (h₁ : IsInverseEquivariant θ f₁)
    (h₂ : IsInverseEquivariant θ f₂) : IsInverseEquivariant θ (f₁ + f₂) := by
  intro n x
  simp only [Pi.add_apply, h₁ n x, h₂ n x, mul_add]

theorem IsInverseEquivariant.smul {f : G → ℂ} (h : IsInverseEquivariant θ f) (c : ℂ) :
    IsInverseEquivariant θ (c • f) := by
  intro n x
  simp only [Pi.smul_apply, h n x, smul_eq_mul]
  ring

theorem IsInverseEquivariant.translate {f : G → ℂ} (h : IsInverseEquivariant θ f) (g : G) :
    IsInverseEquivariant θ (fun y => f (y * g)) := by
  intro n x
  simp only [mul_assoc, h n (x * g)]

theorem pairingFun_add_fun (x : CompactFunctions N (characterRepresentation θ))
    {f₁ f₂ : G → ℂ} (h₁ : IsInverseEquivariant θ f₁) (h₂ : IsInverseEquivariant θ f₂) :
    pairingFun x (h₁.add h₂) = pairingFun x h₁ + pairingFun x h₂ := by
  funext q
  induction q using Quotient.inductionOn with
  | h z =>
    change eval _ _ x.1 z * (f₁ z + f₂ z) = eval _ _ x.1 z * f₁ z + eval _ _ x.1 z * f₂ z
    ring

theorem pairingFun_smul_fun (x : CompactFunctions N (characterRepresentation θ))
    {f : G → ℂ} (h : IsInverseEquivariant θ f) (c : ℂ) :
    pairingFun x (h.smul c) = c • pairingFun x h := by
  funext q
  induction q using Quotient.inductionOn with
  | h z =>
    change eval _ _ x.1 z * (c * f z) = c * (eval _ _ x.1 z * f z)
    ring

theorem pairingFun_translate_fun (x : CompactFunctions N (characterRepresentation θ))
    {f : G → ℂ} (h : IsInverseEquivariant θ f) (g : G) :
    pairingFun x (h.translate g) =
      pairingFun (compactInduced N (characterRepresentation θ) g⁻¹ x) h ∘
        rightTranslate N g := by
  funext q
  induction q using Quotient.inductionOn with
  | h z =>
    change eval _ _ x.1 z * f (z * g) = eval _ _ x.1 (z * g * g⁻¹) * f (z * g)
    rw [mul_inv_cancel_right]

set_option maxHeartbeats 800000 in
/-- **Invariant pairings are integrals.** Let `π` be a smooth representation of `G` and `β` a
`G`-invariant bilinear form on `c-Ind_N^G θ × π`. There is an intertwiner `Φ` from `π` to the
`θ⁻¹`-equivariant functions on `G` such that `β x e = ∫_{N \ G} x · Φ(e)`. -/
theorem exists_pairing_intertwiner [SigmaCompactSpace G] (hν0 : ν ≠ 0)
    (hνinv : ∀ s : G, MeasurePreserving (rightTranslate N s) ν ν)
    (hcof : ∀ U ∈ nhds (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hθ : IsOpen (θ.ker : Set N))
    {E : Type*} [AddCommGroup E] [Module ℂ E] (π : Representation ℂ G E) (hπ : IsSmooth π)
    (β : CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hβ : ∀ g x e, β (compactInduced N (characterRepresentation θ) g x) (π g e) = β x e) :
    ∃ Φ : π.IntertwiningMap (Whittaker.functionRepresentation N θ⁻¹),
      ∀ x e, ∃ hf : IsInverseEquivariant θ (Φ e).val,
        β x e = ∫ q, pairingFun x hf q ∂ν := by
  classical
  -- a compact open subgroup fixing each vector
  have hK : ∀ e : E, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ (K : Subgroup G), π k e = e := by
    intro e
    obtain ⟨U, hU⟩ := hπ e
    obtain ⟨K, hKc, hKU⟩ := exists_compact_le hcof U
    exact ⟨K, hKc, fun k hk => hU ⟨k, hKU hk⟩⟩
  choose Ke hKec hKe using hK
  let Le : E → CompactFunctions N (characterRepresentation θ) →ₗ[ℂ] ℂ := fun e => β.flip e
  have hLe : ∀ e, ∀ k ∈ (Ke e : Subgroup G), ∀ x,
      Le e (compactInduced N (characterRepresentation θ) k x) = Le e x := by
    intro e k hk x
    change β _ e = β x e
    conv_lhs => rw [← hKe e k hk]
    exact hβ k x e
  let fe : E → G → ℂ := fun e => reprFun ν (Le e) (Ke e) (hKec e)
  have hfe : ∀ e, IsInverseEquivariant θ (fe e) := fun e =>
    reprFun_isInverseEquivariant ν (Le e) (Ke e) (hKec e)
  have hfeK : ∀ e, ∀ y, ∀ k ∈ (Ke e : Subgroup G), fe e (y * k) = fe e y := fun e y k hk =>
    reprFun_right ν (Le e) (Ke e) (hKec e) y hk
  -- the representing property
  have hrep : ∀ e x, β x e = ∫ q, pairingFun x (hfe e) q ∂ν := fun e x =>
    eq_pairingFunctional_reprFun ν hν0 hνinv hcof (Le e) (Ke e) (hKec e) (hLe e) x
  -- uniqueness in the form used below
  have huniq : ∀ {f₁ f₂ : G → ℂ} (h₁ : IsInverseEquivariant θ f₁)
      (h₂ : IsInverseEquivariant θ f₂) (K₁ K₂ : OpenSubgroup G),
      (∀ y, ∀ k ∈ (K₁ : Subgroup G), f₁ (y * k) = f₁ y) →
      (∀ y, ∀ k ∈ (K₂ : Subgroup G), f₂ (y * k) = f₂ y) →
      (∀ x, ∫ q, pairingFun x h₁ q ∂ν = ∫ q, pairingFun x h₂ q ∂ν) → f₁ = f₂ := by
    intro f₁ f₂ h₁ h₂ K₁ K₂ hK₁ hK₂ h
    exact eq_of_pairingFunctional_eq ν hν0 hνinv hcof hθ h₁ h₂ K₁ K₂ hK₁ hK₂ h
  have hadd : ∀ e₁ e₂, fe (e₁ + e₂) = fe e₁ + fe e₂ := by
    intro e₁ e₂
    apply huniq (hfe (e₁ + e₂)) ((hfe e₁).add (hfe e₂)) (Ke (e₁ + e₂)) (Ke e₁ ⊓ Ke e₂)
      (hfeK (e₁ + e₂))
    · intro y k hk
      simp only [Pi.add_apply, hfeK e₁ y k hk.1, hfeK e₂ y k hk.2]
    · intro x
      rw [← hrep, pairingFun_add_fun x (hfe e₁) (hfe e₂), integral_add'
        (integrable_pairingFun ν hcof x (hfe e₁) (Ke e₁) (hfeK e₁))
        (integrable_pairingFun ν hcof x (hfe e₂) (Ke e₂) (hfeK e₂)), ← hrep, ← hrep, map_add]
  have hsmul : ∀ (c : ℂ) e, fe (c • e) = c • fe e := by
    intro c e
    apply huniq (hfe (c • e)) ((hfe e).smul c) (Ke (c • e)) (Ke e) (hfeK (c • e))
    · intro y k hk
      simp only [Pi.smul_apply, hfeK e y k hk]
    · intro x
      rw [← hrep, pairingFun_smul_fun x (hfe e) c]
      change β x (c • e) = ∫ q, c • pairingFun x (hfe e) q ∂ν
      rw [integral_smul, ← hrep, map_smul, smul_eq_mul]
  have htrans : ∀ g e, fe (π g e) = fun y => fe e (y * g) := by
    intro g e
    let Kg : OpenSubgroup G := OpenSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom
      (by
        change Continuous (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹)
        exact (continuous_const.mul continuous_id).mul continuous_const) (Ke e)
    apply huniq (hfe (π g e)) ((hfe e).translate g) (Ke (π g e)) Kg (hfeK (π g e))
    · intro y k hk
      have hk' : g⁻¹ * k * g ∈ (Ke e : Subgroup G) := by
        have h1 : (MulAut.conj g⁻¹) k ∈ (Ke e : Subgroup G) := hk
        rwa [MulAut.conj_apply, inv_inv] at h1
      change fe e (y * k * g) = fe e (y * g)
      have : y * k * g = y * g * (g⁻¹ * k * g) := by group
      rw [this, hfeK e _ _ hk']
    · intro x
      rw [← hrep, pairingFun_translate_fun x (hfe e) g]
      change β x (π g e) = ∫ q, pairingFun (compactInduced N (characterRepresentation θ) g⁻¹ x)
        (hfe e) (rightTranslate N g q) ∂ν
      rw [(hνinv g).integral_comp (rightTranslate N g).measurableEmbedding, ← hrep]
      rw [← hβ g⁻¹ x (π g e), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
  let Φ : π.IntertwiningMap (Whittaker.functionRepresentation N θ⁻¹) :=
    { toFun := fun e => ⟨fe e, fun n y => by
        rw [hfe e n y]
        rfl⟩
      map_add' := fun e₁ e₂ => Subtype.ext (hadd e₁ e₂)
      map_smul' := fun c e => Subtype.ext (hsmul c e)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro e
        apply Subtype.ext
        exact htrans g e }
  exact ⟨Φ, fun x e => ⟨hfe e, hrep e x⟩⟩

end Main

end Langlands.RankinSelberg.SupercuspidalCompleteness
