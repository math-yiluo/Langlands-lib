import Langlands.LocalFactor.Ramification.Herbrand.LocalArithmeticStatement
import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof

/-!
# Herbrand's quotient theorem for finite Galois extensions over a general base

The ported Anthropic FLT theorems on lower ramification groups of a finite
group acting on a discrete valuation ring are specialized to the supplied
integer ring of a finite Galois extension `L/K`, realized over an arbitrary base
`K₀` by `T : LocalField.TopologicalData K₀ L`. The results prove the Library
propositions `LowerSubgroupCompatibility`, `HerbrandNormalSubgroup` and
`UpperQuotientCompatibility` of `Herbrand.LocalArithmeticStatement`, and the phi
tower law for the actual fixed field of a normal subgroup. No characteristic
hypothesis occurs, and `K₀` is not assumed to be a local field.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Ramification.Local

open Filter ValuativeRel
open scoped Topology

namespace QuotientBridge

universe u₀ uE uK uL

/-! ## Relative integer rings through the module topologies -/

private theorem valuation_lt_one_iff_pow_tendsto
    {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : L) :
    valuation L x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  constructor
  · intro hx
    let := IsTopologicalAddGroup.rightUniformSpace L
    have := isUniformAddGroup_of_addCommGroup (G := L)
    have : MulArchimedean (ValueGroupWithZero L) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    exact Valued.tendsto_zero_pow_of_v_lt_one hx
  · intro h
    have hball : {z : L | valuation L z < 1} ∈ 𝓝 (0 : L) :=
      (IsValuativeTopology.hasBasis_nhds_zero' L).mem_of_mem (by simp)
    obtain ⟨n, hn⟩ := (h.eventually hball).exists
    contrapose! hn
    exact one_le_pow₀ (a := valuation L x) hn |>.trans_eq (map_pow _ _ _).symm

section Relative

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {E : Type uE} [Field E] [Algebra K₀ E] {L : Type uL} [Field L] [Algebra K₀ L]
  (S : LocalField.TopologicalData K₀ E) (T : LocalField.TopologicalData K₀ L)

/-- A `K₀`-algebra map between two realizations over the same base identifies
the supplied integer ring of the source with the preimage of the supplied integer
ring of the target. Both the map and a `K₀`-linear left inverse are continuous
for the module topologies, so `x ^ n → 0` exactly when `f x ^ n → 0`. -/
theorem algHom_mem_integers_iff (f : E →ₐ[K₀] L) (x : E) :
    f x ∈ T.Integers ↔ x ∈ S.Integers := by
  let := S.topology
  let := T.topology
  let := S.valuativeRel
  let := T.valuativeRel
  let := S.moduleTopology
  let := T.moduleTopology
  let := S.localField
  let := T.localField
  obtain ⟨g, hg⟩ := f.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr f.injective)
  have hgf : ∀ y : E, g (f y) = y := fun y => LinearMap.congr_fun hg y
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have hg' : Continuous g := IsModuleTopology.continuous_of_linearMap g
  have key : ∀ y : E, valuation L (f y) < 1 ↔ valuation E y < 1 := by
    intro y
    rw [valuation_lt_one_iff_pow_tendsto, valuation_lt_one_iff_pow_tendsto]
    constructor
    · intro h
      have h' := (hg'.tendsto 0).comp h
      have heq : (g ∘ fun n : ℕ => f y ^ n) = fun n : ℕ => y ^ n :=
        funext fun n => by rw [Function.comp_apply, ← map_pow, hgf]
      rwa [heq, map_zero] at h'
    · intro h
      have h' := (hf.tendsto 0).comp h
      have heq : (f ∘ fun n : ℕ => y ^ n) = fun n : ℕ => f y ^ n :=
        funext fun n => by rw [Function.comp_apply, map_pow]
      rwa [heq, map_zero] at h'
  change valuation L (f x) ≤ 1 ↔ valuation E x ≤ 1
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpos : 0 < valuation E x := by simpa only [zero_lt_iff, map_ne_zero] using hx
  have hfpos : 0 < valuation L (f x) := by
    simpa only [zero_lt_iff, map_ne_zero] using (map_ne_zero f).mpr hx
  have hinv := key x⁻¹
  simp only [map_inv₀] at hinv
  rw [inv_lt_one₀ hfpos, inv_lt_one₀ hpos] at hinv
  rw [← not_lt, ← not_lt, hinv]

end Relative

section FixedField

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L : Type uL} [Field L] [Algebra K₀ L] (T : LocalField.TopologicalData K₀ L)
  {K : Type uK} [Field K] [Algebra K₀ K] [Algebra K L] [IsScalarTower K₀ K L]

/-- An element of the actual fixed field lies in the supplied integer ring of a
realization of the fixed field exactly when it lies in the supplied integer ring
of `L`. -/
theorem fixedField_mem_integers_iff (H : Subgroup (L ≃ₐ[K] L))
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H))
    (x : IntermediateField.fixedField H) :
    (x : L) ∈ T.Integers ↔ x ∈ S.Integers :=
  algHom_mem_integers_iff S T (IsScalarTower.toAlgHom K₀ (IntermediateField.fixedField H) L) x

end FixedField

/-! ## The Library Herbrand function at rational arguments -/

section Phi

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L : Type uL} [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
  (T : LocalField.TopologicalData K₀ L) (K : Type uK) [Field K] [Algebra K₀ K]
  [Algebra K L] [IsScalarTower K₀ K L]
  {A : Type*} [CommRing A] [IsLocalRing A] {Γ : Type*} [Group Γ] [MulSemiringAction Γ A]

/-- If the orders of the lower groups agree, the Library real Herbrand function
agrees at nonnegative rational arguments with the source rational one. -/
theorem herbrandPhi_ratCast
    (hcard : ∀ i, lowerGroupOrder T K i = lowerGroupCard A Γ i)
    {u : ℚ} (hu : 0 ≤ u) :
    herbrandPhi T K (u : ℝ) = (herbrandPhiRat A Γ u : ℝ) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  rw [herbrandPhi_floor T K (by exact_mod_cast hu.le),
    herbrandPhiRat_of_pos hu, HerbrandBridge.natFloor_ratCast]
  push_cast
  simp only [hcard]
  rw [HerbrandBridge.sum_Icc_one_eq_sum_range]

theorem herbrandPhi_natCast_eq
    (hcard : ∀ i, lowerGroupOrder T K i = lowerGroupCard A Γ i)
    (n : ℕ) :
    herbrandPhi T K (n : ℝ) = (herbrandPhiRat A Γ (n : ℚ) : ℝ) := by
  have h := herbrandPhi_ratCast T K hcard (Nat.cast_nonneg n : (0 : ℚ) ≤ n)
  rwa [Rat.cast_natCast] at h

/-- The integer index of the Library upper group at a nonnegative rational
argument is the source upper index. -/
theorem ceil_herbrandPsi_ratCast [Finite Γ]
    (hcard : ∀ i, lowerGroupOrder T K i = lowerGroupCard A Γ i)
    {w : ℚ} (hw : 0 ≤ w) :
    ⌈herbrandPsi T K (w : ℝ)⌉ = (upperGroupRatIndex A Γ w : ℤ) := by
  set N := upperGroupRatIndex A Γ w
  have key : ∀ n : ℕ, herbrandPsi T K (w : ℝ) ≤ n ↔
      w ≤ herbrandPhiRat A Γ (n : ℚ) := by
    intro n
    rw [← (herbrandPhi_strictMono T K).le_iff_le, herbrandPhi_herbrandPsi,
      herbrandPhi_natCast_eq T K hcard]
    exact Rat.cast_le
  rw [Int.ceil_eq_iff]
  constructor
  · rcases Nat.eq_zero_or_pos N with h0 | hpos
    · have : 0 ≤ herbrandPsi T K (w : ℝ) := by
        rw [← herbrandPsi_zero T K]
        exact (herbrandPsi_strictMono T K).monotone (by exact_mod_cast hw)
      rw [h0]
      push_cast
      linarith
    · by_contra hlt
      rw [not_lt] at hlt
      have h1 : herbrandPsi T K (w : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpos]
        push_cast at hlt ⊢
        exact hlt
      have := upperGroupRatIndex_le ((key _).mp h1)
      omega
  · push_cast
    exact (key N).mpr (le_herbrandPhiRat_upperGroupRatIndex w)

theorem upperRamificationGroup_ratCast [Finite Γ]
    (hcard : ∀ i, lowerGroupOrder T K i = lowerGroupCard A Γ i)
    {w : ℚ} (hw : 0 ≤ w) :
    upperRamificationGroup T K (w : ℝ) =
      lowerRamificationGroup T K (upperGroupRatIndex A Γ w) := by
  rw [upperRamificationGroup_eq_lower, ceil_herbrandPsi_ratCast T K hcard hw,
    ← lowerRamificationGroupReal_int, Int.cast_natCast, lowerRamificationGroupReal_nat]

/-- The value of the Library Herbrand function at a natural number is rational. -/
theorem herbrandPhi_natCast_rat (n : ℕ) :
    ∃ q : ℚ, herbrandPhi T K (n : ℝ) = q := by
  refine ⟨(∑ i ∈ Finset.range n, (lowerGroupOrder T K (i + 1) : ℚ)) /
    lowerGroupOrder T K 0, ?_⟩
  rw [herbrandPhi_floor T K (Nat.cast_nonneg n), Nat.floor_natCast]
  push_cast
  simp

/-- The Library upper group is constant from `v` up to the Herbrand value of
the integer index of `v`. -/
theorem upperRamificationGroup_eq_of_le {v w : ℝ} (hvw : v ≤ w)
    (hw : w ≤ herbrandPhi T K (⌈herbrandPsi T K v⌉ : ℝ)) :
    upperRamificationGroup T K w = upperRamificationGroup T K v := by
  rw [upperRamificationGroup_eq_lower, upperRamificationGroup_eq_lower]
  congr 1
  rw [Int.ceil_eq_iff]
  constructor
  · have h1 := Int.ceil_lt_add_one (herbrandPsi T K v)
    have h2 := (herbrandPsi_strictMono T K).monotone hvw
    linarith
  · have h := (herbrandPsi_strictMono T K).monotone hw
    rwa [herbrandPsi_herbrandPhi] at h

omit [FiniteDimensional K₀ L] in
theorem lowerRamificationGroupReal_of_ceil_eq {u : ℝ} {n : ℕ} (h : ⌈u⌉ = n) :
    lowerRamificationGroupReal T K u = lowerRamificationGroup T K n := by
  rw [← lowerRamificationGroupReal_nat]
  unfold lowerRamificationGroupReal
  rw [h, Int.ceil_natCast]

/-- Above `-1`, every Library upper group is constant on an interval from `v`
to a nonnegative rational number. -/
theorem exists_rat_upperRamificationGroup_eq {v : ℝ} (hv : -1 < v) :
    ∃ q : ℚ, 0 ≤ q ∧ v ≤ q ∧ ∀ w : ℝ, v ≤ w → w ≤ q →
      upperRamificationGroup T K w = upperRamificationGroup T K v := by
  have hpsi : -1 < herbrandPsi T K v := by
    rw [← herbrandPsi_neg_one T K]
    exact herbrandPsi_strictMono T K hv
  have hc : (-1 : ℤ) < ⌈herbrandPsi T K v⌉ :=
    Int.lt_ceil.mpr (by push_cast; exact hpsi)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌈herbrandPsi T K v⌉ = n :=
    ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn' : ((⌈herbrandPsi T K v⌉ : ℤ) : ℝ) = (n : ℝ) := by
    rw [hn]
    exact Int.cast_natCast n
  obtain ⟨q, hq⟩ := herbrandPhi_natCast_rat T K n
  refine ⟨q, ?_, ?_, fun w hvw hwq =>
    upperRamificationGroup_eq_of_le T K hvw (by rw [hn', hq]; exact hwq)⟩
  · have h0 : herbrandPhi T K 0 ≤ herbrandPhi T K n :=
      (herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg n)
    rw [herbrandPhi_zero, hq] at h0
    exact_mod_cast h0
  · have h1 : herbrandPsi T K v ≤ n := by
      rw [← hn']
      exact Int.le_ceil _
    have h2 := (herbrandPhi_strictMono T K).monotone h1
    rwa [herbrandPhi_herbrandPsi, hq] at h2

end Phi

/-! ## The source hypotheses for the supplied integer ring -/

section Source

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  {L : Type uL} [Field L] [Algebra K₀ L]
  (T : LocalField.TopologicalData K₀ L) (K : Type uK) [Field K] [Algebra K₀ K]
  [Algebra K L] [IsScalarTower K₀ K L]

/-- The automorphisms act faithfully on the supplied integer ring, by
fraction-ring extensionality. -/
theorem integerAction_faithful :
    letI := integerAction T K
    FaithfulSMul (L ≃ₐ[K] L) T.Integers := by
  letI := integerAction T K
  letI := T.valuativeRel
  haveI : IsFractionRing T.Integers L :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation L).valuationSubring L)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : L)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

/-- The Library lower groups are the source lower groups of the integer action. -/
theorem lowerRamificationGroup_eq_source (i : ℕ) :
    letI := integerAction T K
    lowerRamificationGroup T K i =
      lowerGroup T.Integers (L ≃ₐ[K] L) i := rfl

theorem lowerGroupOrder_eq_source (i : ℕ) :
    letI := integerAction T K
    lowerGroupOrder T K i =
      lowerGroupCard T.Integers (L ≃ₐ[K] L) i := rfl

end Source

/-! ## The actual fixed field of a subgroup -/

section Galois

open IsLocalRing

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (L : Type uL) [Field L] [Algebra K₀ L] [FiniteDimensional K₀ L]
  [Algebra K L] [IsScalarTower K₀ K L]
  (T : LocalField.TopologicalData K₀ L)

/-- The ported Herbrand theorem in lower numbering, for the supplied integer
ring and the full automorphism group. -/
theorem source_map_lowerRamificationGroup_mk (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (n : ℕ) :
    letI := integerAction T K
    (lowerGroup T.Integers (L ≃ₐ[K] L) n).map
        (QuotientGroup.mk' H) =
      lowerGroup (FixedPoints.subring T.Integers H)
        ((L ≃ₐ[K] L) ⧸ H) ⌈herbrandPhiRat T.Integers H (n : ℚ)⌉₊ := by
  letI := integerAction T K
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  haveI : IsDiscreteValuationRing T.Integers := inferInstance
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  haveI := integerAction_faithful T K
  haveI : Finite T.ResidueField := inferInstance
  haveI : Finite (T.Integers ⧸ maximalIdeal T.Integers) :=
    inferInstanceAs (Finite T.ResidueField)
  haveI : (maximalIdeal T.Integers).LiesOver
      (maximalIdeal (FixedPoints.subring T.Integers (L ≃ₐ[K] L))) :=
    ⟨maximalIdeal_fixedSubring_eq_comap⟩
  letI : Field (T.Integers ⧸ maximalIdeal T.Integers) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring T.Integers (L ≃ₐ[K] L) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (L ≃ₐ[K] L))) :=
    Ideal.Quotient.field _
  haveI : Finite (FixedPoints.subring T.Integers (L ≃ₐ[K] L) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (L ≃ₐ[K] L))) :=
    Finite.of_injective (algebraMap _ (T.Integers ⧸ maximalIdeal T.Integers))
      (algebraMap
        (FixedPoints.subring T.Integers (L ≃ₐ[K] L) ⧸
          maximalIdeal (FixedPoints.subring T.Integers (L ≃ₐ[K] L)))
        (T.Integers ⧸ maximalIdeal T.Integers)).injective
  exact map_lowerGroup_mk_eq_of_isSeparable_residueField n

/-- The Library lower-group orders of `L` over the actual fixed field of `H`
are the source orders for the subgroup `H`. -/
theorem lowerGroupOrder_fixedField (H : Subgroup (L ≃ₐ[K] L)) (i : ℕ) :
    letI := integerAction T K
    lowerGroupOrder T (IntermediateField.fixedField H) i =
      lowerGroupCard T.Integers H i := by
  letI := integerAction T K
  letI := integerAction T (IntermediateField.fixedField H)
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  exact (HerbrandBridge.lowerRamificationCard_of_equivariant (RingEquiv.refl T.Integers)
    (IntermediateField.subgroupEquivAlgEquiv H).symm (fun _ _ => Subtype.ext rfl) i).symm

omit [FiniteDimensional K₀ L] in
/-- The fixed subring of `H` in the supplied integer ring of `L` is the
supplied integer ring of any realization of the actual fixed field. -/
def fixedSubringEquiv (H : Subgroup (L ≃ₐ[K] L))
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) :
    letI := integerAction T K
    FixedPoints.subring T.Integers H ≃+* S.Integers := by
  letI := integerAction T K
  exact
  { toFun x := ⟨⟨((x : T.Integers) : L), fun h => congrArg Subtype.val (x.2 h)⟩,
      (fixedField_mem_integers_iff T H S _).mp (x : T.Integers).2⟩
    invFun y := ⟨⟨((y : IntermediateField.fixedField H) : L),
      (fixedField_mem_integers_iff T H S _).mpr y.2⟩,
      fun h => Subtype.ext ((y : IntermediateField.fixedField H).2 h)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }

omit [FiniteDimensional K₀ L] in
@[simp] theorem fixedSubringEquiv_coe (H : Subgroup (L ≃ₐ[K] L))
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H))
    (x : letI := integerAction T K; FixedPoints.subring T.Integers H) :
    ((fixedSubringEquiv K L T H S x : IntermediateField.fixedField H) : L) =
      ((x : T.Integers) : L) := rfl

omit [FiniteDimensional K₀ L] in
/-- The fixed-subring identification intertwines the quotient action with the
actual normal restriction. -/
theorem fixedSubringEquiv_smul [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) (g : L ≃ₐ[K] L)
    (a : letI := integerAction T K; FixedPoints.subring T.Integers H) :
    letI := integerAction T K
    letI := integerAction S K
    fixedSubringEquiv K L T H S ((QuotientGroup.mk g : (L ≃ₐ[K] L) ⧸ H) • a) =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L)
          (IntermediateField.fixedField H) g) •
        fixedSubringEquiv K L T H S a := by
  letI := integerAction T K
  letI := integerAction S K
  apply Subtype.ext
  apply Subtype.ext
  change g ((a : T.Integers) : L) =
    ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) g
      ⟨((a : T.Integers) : L), fun h => congrArg Subtype.val (a.2 h)⟩ :
        IntermediateField.fixedField H) : L)
  exact (AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField H) g
    ⟨((a : T.Integers) : L), fun h => congrArg Subtype.val (a.2 h)⟩).symm

/-- A subgroup whose image in the quotient is a source lower group of the
fixed subring restricts to the corresponding Library lower group of the actual
fixed field. -/
theorem map_restrictNormalHom_eq [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H))
    (X : Subgroup (L ≃ₐ[K] L)) (i : ℕ)
    (hX : letI := integerAction T K
      X.map (QuotientGroup.mk' H) =
        lowerGroup (FixedPoints.subring T.Integers H)
          ((L ≃ₐ[K] L) ⧸ H) i) :
    X.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L)
        (IntermediateField.fixedField H)) =
      lowerRamificationGroup S K i := by
  letI := integerAction T K
  letI := integerAction S K
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  let f : ((L ≃ₐ[K] L) ⧸ H) ≃*
      (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H) :=
    IsGalois.normalAutEquivQuotient H
  have hf : AlgEquiv.restrictNormalHom (F := K) (K₁ := L)
      (IntermediateField.fixedField H) = (f : _ →* _).comp (QuotientGroup.mk' H) :=
    MonoidHom.ext fun g => (IsGalois.normalAutEquivQuotient_apply H g).symm
  have he : ∀ (g : (L ≃ₐ[K] L) ⧸ H) (a : FixedPoints.subring T.Integers H),
      fixedSubringEquiv K L T H S (g • a) = f g • fixedSubringEquiv K L T H S a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g => exact fixedSubringEquiv_smul K L T H S g a
  rw [hf, ← Subgroup.map_map, hX]
  exact HerbrandBridge.map_lowerRamificationGroup_of_equivariant
    (fixedSubringEquiv K L T H S) f he i

/-- The Library lower-group orders of the actual fixed field over `K` are the
source orders of the quotient acting on the fixed subring. -/
theorem lowerGroupOrder_fixedField_quotient [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) (i : ℕ) :
    letI := integerAction T K
    lowerGroupOrder S K i =
      lowerGroupCard (FixedPoints.subring T.Integers H)
        ((L ≃ₐ[K] L) ⧸ H) i := by
  letI := integerAction T K
  letI := integerAction S K
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  let f : ((L ≃ₐ[K] L) ⧸ H) ≃*
      (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H) :=
    IsGalois.normalAutEquivQuotient H
  have he : ∀ (g : (L ≃ₐ[K] L) ⧸ H) (a : FixedPoints.subring T.Integers H),
      fixedSubringEquiv K L T H S (g • a) = f g • fixedSubringEquiv K L T H S a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g => exact fixedSubringEquiv_smul K L T H S g a
  exact HerbrandBridge.lowerRamificationCard_of_equivariant (fixedSubringEquiv K L T H S) f he i

/-- The automorphisms over the actual fixed field are exactly the subgroup. -/
theorem range_restrictScalarsHom_fixedField [FiniteDimensional K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (AlgEquiv.restrictScalarsHom K :
      (L ≃ₐ[IntermediateField.fixedField H] L) →* (L ≃ₐ[K] L)).range = H := by
  conv_rhs => rw [← IntermediateField.fixingSubgroup_fixedField H]
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    exact ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm τ).2
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv _ ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

omit [FiniteDimensional K₀ L] in
theorem restrictScalars_mem_lowerRamificationGroup_iff (H : Subgroup (L ≃ₐ[K] L))
    (τ : L ≃ₐ[IntermediateField.fixedField H] L) (i : ℕ) :
    τ.restrictScalars K ∈ lowerRamificationGroup T K i ↔
      τ ∈ lowerRamificationGroup T (IntermediateField.fixedField H) i :=
  Iff.rfl

end Galois

end QuotientBridge

/-! ## The Library propositions -/

section Main

open QuotientBridge

universe u₀ uK uL

/-- Herbrand's theorem in upper numbering for the actual normal restriction,
over any base `K₀` (Serre, *Local Fields*, IV §3, Proposition 14). -/
theorem upperQuotientCompatibility {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀]
    [TopologicalSpace K₀] (K : Type uK) [Field K] [Algebra K₀ K] (L : Type uL) [Field L]
    [Algebra K₀ L] [FiniteDimensional K₀ L] [Algebra K L] [IsScalarTower K₀ K L]
    [IsGalois K L] (T : LocalField.TopologicalData K₀ L) :
    UpperQuotientCompatibility K L T := by
  intro H _ S v hv
  letI := integerAction T K
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  rcases hv.eq_or_lt with rfl | hv
  · rw [upperRamificationGroup_neg_one, upperRamificationGroup_neg_one,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨qT, hqT0, hvqT, hT⟩ := exists_rat_upperRamificationGroup_eq T K hv
  obtain ⟨qS, hqS0, hvqS, hS⟩ := exists_rat_upperRamificationGroup_eq S K hv
  have hw0 : (0 : ℚ) ≤ min qT qS := le_min hqT0 hqS0
  have hvw : v ≤ ((min qT qS : ℚ) : ℝ) := by
    push_cast
    exact le_min hvqT hvqS
  rw [← hT _ hvw (by push_cast; exact min_le_left _ _),
    ← hS _ hvw (by push_cast; exact min_le_right _ _),
    upperRamificationGroup_ratCast T K (lowerGroupOrder_eq_source T K) hw0,
    upperRamificationGroup_ratCast S K (lowerGroupOrder_fixedField_quotient K L T H S) hw0]
  exact map_restrictNormalHom_eq K L T H S _ _
    (upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq
      (source_map_lowerRamificationGroup_mk K L T H) _ hw0)

/-- The phi tower law through the actual fixed field of a normal subgroup
(Serre, *Local Fields*, IV §3, Proposition 15, first formula). -/
theorem herbrandPhi_fixedField_tower {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀]
    [TopologicalSpace K₀] (K : Type uK) [Field K] [Algebra K₀ K] (L : Type uL) [Field L]
    [Algebra K₀ L] [FiniteDimensional K₀ L] [Algebra K L] [IsScalarTower K₀ K L]
    [IsGalois K L] (T : LocalField.TopologicalData K₀ L)
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (S : LocalField.TopologicalData K₀ (IntermediateField.fixedField H)) (u : ℝ) :
    herbrandPhi T K u =
      herbrandPhi S K (herbrandPhi T (IntermediateField.fixedField H) u) := by
  letI := integerAction T K
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  have hrat : ∀ q : ℚ, herbrandPhi T K q =
      herbrandPhi S K (herbrandPhi T (IntermediateField.fixedField H) q) := by
    intro q
    rcases le_or_gt q 0 with hq | hq
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      rw [herbrandPhi_of_nonpos T _ hq', herbrandPhi_of_nonpos T _ hq',
        herbrandPhi_of_nonpos S _ hq']
    · have hH := herbrandPhi_ratCast T (IntermediateField.fixedField H)
        (lowerGroupOrder_fixedField K L T H) hq.le
      have hφ0 : 0 ≤ herbrandPhiRat T.Integers H q := by
        have h := herbrandPhi_pos T (IntermediateField.fixedField H)
          (by exact_mod_cast hq : (0 : ℝ) < q)
        rw [hH] at h
        exact_mod_cast h.le
      rw [herbrandPhi_ratCast T K (lowerGroupOrder_eq_source T K) hq.le, hH,
        herbrandPhi_ratCast S K (lowerGroupOrder_fixedField_quotient K L T H S) hφ0,
        herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq
          (source_map_lowerRamificationGroup_mk K L T H) hq.le]
  have hcont : Continuous fun u => herbrandPhi S K
      (herbrandPhi T (IntermediateField.fixedField H) u) :=
    (herbrandPhi_continuous S K).comp (herbrandPhi_continuous T _)
  exact congrFun (Continuous.ext_on Rat.denseRange_cast
    (herbrandPhi_continuous T K) hcont (by rintro _ ⟨q, rfl⟩; exact hrat q)) u

/-- Herbrand's theorem in lower numbering for the actual normal restriction,
over any base `K₀` (Serre, *Local Fields*, IV §3, Lemma 5). -/
theorem herbrandNormalSubgroup {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀]
    [TopologicalSpace K₀] (K : Type uK) [Field K] [Algebra K₀ K] (L : Type uL) [Field L]
    [Algebra K₀ L] [FiniteDimensional K₀ L] [Algebra K L] [IsScalarTower K₀ K L]
    [IsGalois K L] (T : LocalField.TopologicalData K₀ L) :
    HerbrandNormalSubgroup K L T := by
  intro H _ S u hu
  have hv : -1 ≤ herbrandPhi T K u := by
    rw [← herbrandPhi_neg_one T K]
    exact (herbrandPhi_strictMono T K).monotone hu
  rw [← upperRamificationGroup_phi T K u,
    upperQuotientCompatibility K L T H S _ hv, herbrandPhi_fixedField_tower K L T H S u,
    upperRamificationGroup_phi]

/-- Lower numbering of an actual subgroup is the intersection with the lower
filtration of the full group (Serre, *Local Fields*, IV §1, Proposition 2). -/
theorem lowerSubgroupCompatibility {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀]
    [TopologicalSpace K₀] (K : Type uK) [Field K] [Algebra K₀ K] (L : Type uL) [Field L]
    [Algebra K₀ L] [FiniteDimensional K₀ L] [Algebra K L] [IsScalarTower K₀ K L]
    [IsGalois K L] (T : LocalField.TopologicalData K₀ L) :
    LowerSubgroupCompatibility K L T := by
  intro H u hu
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite K₀ K L
  rcases hu.eq_or_lt with rfl | hu
  · rw [lowerRamificationGroupReal_neg_one, lowerRamificationGroupReal_neg_one,
      ← MonoidHom.range_eq_map, top_inf_eq]
    exact range_restrictScalarsHom_fixedField K L H
  have hc : (-1 : ℤ) < ⌈u⌉ := Int.lt_ceil.mpr (by push_cast; exact hu)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌈u⌉ = n := ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [lowerRamificationGroupReal_of_ceil_eq T _ hn, lowerRamificationGroupReal_of_ceil_eq T _ hn]
  ext σ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, AlgEquiv.restrictScalarsHom_apply]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(restrictScalars_mem_lowerRamificationGroup_iff K L T H τ n).mpr hτ, ?_⟩
    exact (SetLike.ext_iff.mp (range_restrictScalarsHom_fixedField K L H) _).mp ⟨τ, rfl⟩
  · rintro ⟨hσ, hH⟩
    rw [← range_restrictScalarsHom_fixedField K L H] at hH
    obtain ⟨τ, rfl⟩ := hH
    exact ⟨τ, (restrictScalars_mem_lowerRamificationGroup_iff K L T H τ n).mp hσ, rfl⟩

end Main

end Langlands.Ramification.Local
