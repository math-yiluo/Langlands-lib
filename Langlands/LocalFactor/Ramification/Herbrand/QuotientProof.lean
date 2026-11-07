import Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement
import Langlands.LocalField.RelativeIntegers
import Langlands.AnthropicFLT.Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq

/-!
# Herbrand's quotient theorem for actual finite p-adic Galois extensions

The ported Anthropic FLT theorems on lower ramification groups of a finite
group acting on a discrete valuation ring are specialized to the supplied
integer ring of a finite p-adic Galois extension. The results prove the
Library propositions `LowerSubgroupCompatibility`, `HerbrandNormalSubgroup`
and `UpperQuotientCompatibility`, and the phi tower law for the actual fixed
field of a normal subgroup.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Ramification.HerbrandBridge

/-! ## Transport along equivariant ring isomorphisms -/

section Transport

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  {G G' : Type*} [Group G] [Group G'] [MulSemiringAction G A] [MulSemiringAction G' B]

theorem ringEquiv_mem_maximalIdeal_pow_iff (e : A ≃+* B) (n : ℕ) (a : A) :
    e a ∈ IsLocalRing.maximalIdeal B ^ n ↔ a ∈ IsLocalRing.maximalIdeal A ^ n := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff

theorem mem_lowerRamificationGroup_iff_of_equivariant (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (i : ℕ) (g : G) :
    f g ∈ IsLocalRing.lowerRamificationGroup B G' i ↔
      g ∈ IsLocalRing.lowerRamificationGroup A G i := by
  simp only [IsLocalRing.mem_lowerRamificationGroup]
  constructor
  · intro h a
    rw [← ringEquiv_mem_maximalIdeal_pow_iff e, map_sub, he]
    exact h (e a)
  · intro h b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← he, ← map_sub, ringEquiv_mem_maximalIdeal_pow_iff]
    exact h a

/-- An equivariant ring isomorphism carries lower ramification groups onto
lower ramification groups. -/
theorem map_lowerRamificationGroup_of_equivariant (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A G i).map (f : G →* G') =
      IsLocalRing.lowerRamificationGroup B G' i := by
  ext σ
  obtain ⟨g, rfl⟩ := f.surjective σ
  rw [mem_lowerRamificationGroup_iff_of_equivariant e f he]
  exact Subgroup.mem_map_iff_mem f.injective

theorem lowerRamificationCard_of_equivariant (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (i : ℕ) :
    IsLocalRing.lowerRamificationCard B G' i = IsLocalRing.lowerRamificationCard A G i := by
  unfold IsLocalRing.lowerRamificationCard
  rw [← map_lowerRamificationGroup_of_equivariant e f he i]
  exact Subgroup.card_map_of_injective f.injective

end Transport

/-! ## The Library Herbrand function at rational arguments -/

section Phi

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
  {A : Type*} [CommRing A] [IsLocalRing A] {Γ : Type*} [Group Γ] [MulSemiringAction Γ A]

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, f j = ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem natFloor_ratCast (u : ℚ) : ⌊(u : ℝ)⌋₊ = ⌊u⌋₊ := by
  rw [← Int.floor_toNat, Rat.floor_cast, Int.floor_toNat]

/-- If the orders of the lower groups agree, the Library real Herbrand function
agrees at nonnegative rational arguments with the source rational one. -/
theorem herbrandPhi_ratCast
    (hcard : ∀ i, Padic.lowerGroupOrder T K i = IsLocalRing.lowerRamificationCard A Γ i)
    {u : ℚ} (hu : 0 ≤ u) :
    Padic.herbrandPhi T K (u : ℝ) = (IsLocalRing.herbrandPhi A Γ u : ℝ) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  rw [Padic.herbrandPhi_floor T K (by exact_mod_cast hu.le),
    IsLocalRing.herbrandPhi_of_pos hu, natFloor_ratCast]
  push_cast
  simp only [hcard]
  rw [sum_Icc_one_eq_sum_range]

theorem herbrandPhi_natCast_eq
    (hcard : ∀ i, Padic.lowerGroupOrder T K i = IsLocalRing.lowerRamificationCard A Γ i)
    (n : ℕ) :
    Padic.herbrandPhi T K (n : ℝ) = (IsLocalRing.herbrandPhi A Γ (n : ℚ) : ℝ) := by
  have h := herbrandPhi_ratCast T K hcard (Nat.cast_nonneg n : (0 : ℚ) ≤ n)
  rwa [Rat.cast_natCast] at h

/-- The integer index of the Library upper group at a nonnegative rational
argument is the source upper index. -/
theorem ceil_herbrandPsi_ratCast [Finite Γ]
    (hcard : ∀ i, Padic.lowerGroupOrder T K i = IsLocalRing.lowerRamificationCard A Γ i)
    {w : ℚ} (hw : 0 ≤ w) :
    ⌈Padic.herbrandPsi T K (w : ℝ)⌉ = (IsLocalRing.upperRamificationIndex A Γ w : ℤ) := by
  set N := IsLocalRing.upperRamificationIndex A Γ w
  have key : ∀ n : ℕ, Padic.herbrandPsi T K (w : ℝ) ≤ n ↔
      w ≤ IsLocalRing.herbrandPhi A Γ (n : ℚ) := by
    intro n
    rw [← (Padic.herbrandPhi_strictMono T K).le_iff_le, Padic.herbrandPhi_herbrandPsi,
      herbrandPhi_natCast_eq T K hcard]
    exact Rat.cast_le
  rw [Int.ceil_eq_iff]
  constructor
  · rcases Nat.eq_zero_or_pos N with h0 | hpos
    · have : 0 ≤ Padic.herbrandPsi T K (w : ℝ) := by
        rw [← Padic.herbrandPsi_zero T K]
        exact (Padic.herbrandPsi_strictMono T K).monotone (by exact_mod_cast hw)
      rw [h0]
      push_cast
      linarith
    · by_contra hlt
      rw [not_lt] at hlt
      have h1 : Padic.herbrandPsi T K (w : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpos]
        push_cast at hlt ⊢
        exact hlt
      have := IsLocalRing.upperRamificationIndex_le ((key _).mp h1)
      omega
  · push_cast
    exact (key N).mpr (IsLocalRing.le_herbrandPhi_upperRamificationIndex w)

theorem upperRamificationGroup_ratCast [Finite Γ]
    (hcard : ∀ i, Padic.lowerGroupOrder T K i = IsLocalRing.lowerRamificationCard A Γ i)
    {w : ℚ} (hw : 0 ≤ w) :
    Padic.upperRamificationGroup T K (w : ℝ) =
      Padic.lowerRamificationGroup T K (IsLocalRing.upperRamificationIndex A Γ w) := by
  rw [Padic.upperRamificationGroup_eq_lower, ceil_herbrandPsi_ratCast T K hcard hw,
    ← Padic.lowerRamificationGroupReal_int, Int.cast_natCast,
    Padic.lowerRamificationGroupReal_nat]

/-- The value of the Library Herbrand function at a natural number is rational. -/
theorem herbrandPhi_natCast_rat (n : ℕ) :
    ∃ q : ℚ, Padic.herbrandPhi T K (n : ℝ) = q := by
  refine ⟨(∑ i ∈ Finset.range n, (Padic.lowerGroupOrder T K (i + 1) : ℚ)) /
    Padic.lowerGroupOrder T K 0, ?_⟩
  rw [Padic.herbrandPhi_floor T K (Nat.cast_nonneg n), Nat.floor_natCast]
  push_cast
  simp

/-- The Library upper group is constant from `v` up to the Herbrand value of
the integer index of `v`. -/
theorem upperRamificationGroup_eq_of_le {v w : ℝ} (hvw : v ≤ w)
    (hw : w ≤ Padic.herbrandPhi T K (⌈Padic.herbrandPsi T K v⌉ : ℝ)) :
    Padic.upperRamificationGroup T K w = Padic.upperRamificationGroup T K v := by
  rw [Padic.upperRamificationGroup_eq_lower, Padic.upperRamificationGroup_eq_lower]
  congr 1
  rw [Int.ceil_eq_iff]
  constructor
  · have h1 := Int.ceil_lt_add_one (Padic.herbrandPsi T K v)
    have h2 := (Padic.herbrandPsi_strictMono T K).monotone hvw
    linarith
  · have h := (Padic.herbrandPsi_strictMono T K).monotone hw
    rwa [Padic.herbrandPsi_herbrandPhi] at h

theorem lowerRamificationGroupReal_of_ceil_eq {u : ℝ} {n : ℕ} (h : ⌈u⌉ = n) :
    Padic.lowerRamificationGroupReal T K u = Padic.lowerRamificationGroup T K n := by
  rw [← Padic.lowerRamificationGroupReal_nat]
  unfold Padic.lowerRamificationGroupReal
  rw [h, Int.ceil_natCast]

/-- Above `-1`, every Library upper group is constant on an interval from `v`
to a nonnegative rational number. -/
theorem exists_rat_upperRamificationGroup_eq {v : ℝ} (hv : -1 < v) :
    ∃ q : ℚ, 0 ≤ q ∧ v ≤ q ∧ ∀ w : ℝ, v ≤ w → w ≤ q →
      Padic.upperRamificationGroup T K w = Padic.upperRamificationGroup T K v := by
  have hpsi : -1 < Padic.herbrandPsi T K v := by
    rw [← Padic.herbrandPsi_neg_one T K]
    exact Padic.herbrandPsi_strictMono T K hv
  have hc : (-1 : ℤ) < ⌈Padic.herbrandPsi T K v⌉ :=
    Int.lt_ceil.mpr (by push_cast; exact hpsi)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌈Padic.herbrandPsi T K v⌉ = n :=
    ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn' : ((⌈Padic.herbrandPsi T K v⌉ : ℤ) : ℝ) = (n : ℝ) := by
    rw [hn]
    exact Int.cast_natCast n
  obtain ⟨q, hq⟩ := herbrandPhi_natCast_rat T K n
  refine ⟨q, ?_, ?_, fun w hvw hwq =>
    upperRamificationGroup_eq_of_le T K hvw (by rw [hn', hq]; exact hwq)⟩
  · have h0 : Padic.herbrandPhi T K 0 ≤ Padic.herbrandPhi T K n :=
      (Padic.herbrandPhi_strictMono T K).monotone (Nat.cast_nonneg n)
    rw [Padic.herbrandPhi_zero, hq] at h0
    exact_mod_cast h0
  · have h1 : Padic.herbrandPsi T K v ≤ n := by
      rw [← hn']
      exact Int.le_ceil _
    have h2 := (Padic.herbrandPhi_strictMono T K).monotone h1
    rwa [Padic.herbrandPhi_herbrandPsi, hq] at h2

end Phi

/-! ## The source hypotheses for the supplied integer ring -/

section Source

open IsLocalRing

universe uK uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- The automorphisms act faithfully on the supplied integer ring, by
fraction-ring extensionality. -/
theorem integerAction_faithful :
    letI := Padic.integerAction T K
    FaithfulSMul (F.Carrier ≃ₐ[K] F.Carrier) T.Integers := by
  letI := Padic.integerAction T K
  letI := T.valuativeRel
  haveI : IsFractionRing T.Integers F.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation F.Carrier).valuationSubring F.Carrier)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : F.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

/-- The Library lower groups are the source lower groups of the integer action. -/
theorem lowerRamificationGroup_eq_source (i : ℕ) :
    letI := Padic.integerAction T K
    Padic.lowerRamificationGroup T K i =
      IsLocalRing.lowerRamificationGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) i := rfl

theorem lowerGroupOrder_eq_source (i : ℕ) :
    letI := Padic.integerAction T K
    Padic.lowerGroupOrder T K i =
      IsLocalRing.lowerRamificationCard T.Integers (F.Carrier ≃ₐ[K] F.Carrier) i := rfl

end Source

section Galois

open IsLocalRing

universe uK uL

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (L : PadicField.{uL} p)
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  (T : L.TopologicalData)

theorem finiteDimensional_carrier : FiniteDimensional K.Carrier L.Carrier :=
  Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier L.Carrier

/-- The ported Herbrand theorem in lower numbering, for the supplied integer
ring and the full automorphism group. -/
theorem source_map_lowerRamificationGroup_mk (H : Subgroup Gal(L.Carrier/K.Carrier))
    [H.Normal] (n : ℕ) :
    letI := Padic.integerAction T K.Carrier
    (IsLocalRing.lowerRamificationGroup T.Integers Gal(L.Carrier/K.Carrier) n).map
        (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring T.Integers H)
        (Gal(L.Carrier/K.Carrier) ⧸ H) ⌈IsLocalRing.herbrandPhi T.Integers H (n : ℚ)⌉₊ := by
  letI := Padic.integerAction T K.Carrier
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  haveI : IsDiscreteValuationRing T.Integers := inferInstance
  haveI := finiteDimensional_carrier K L
  haveI := integerAction_faithful T K.Carrier
  haveI : Finite T.ResidueField := inferInstance
  haveI : Finite (T.Integers ⧸ maximalIdeal T.Integers) :=
    inferInstanceAs (Finite T.ResidueField)
  haveI : (maximalIdeal T.Integers).LiesOver
      (maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    ⟨FixedPoints.maximalIdeal_subring_eq_comap⟩
  letI : Field (T.Integers ⧸ maximalIdeal T.Integers) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    Ideal.Quotient.field _
  haveI : Finite (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    Finite.of_injective (algebraMap _ (T.Integers ⧸ maximalIdeal T.Integers))
      (algebraMap
        (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
          maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier)))
        (T.Integers ⧸ maximalIdeal T.Integers)).injective
  exact IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField n

/-- The Library lower-group orders of `L` over the actual fixed field of `H`
are the source orders for the subgroup `H`. -/
theorem lowerGroupOrder_fixedField (H : Subgroup Gal(L.Carrier/K.Carrier)) (i : ℕ) :
    letI := Padic.integerAction T K.Carrier
    Padic.lowerGroupOrder T (IntermediateField.fixedField H) i =
      IsLocalRing.lowerRamificationCard T.Integers H i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction T (IntermediateField.fixedField H)
  haveI := finiteDimensional_carrier K L
  exact (lowerRamificationCard_of_equivariant (RingEquiv.refl T.Integers)
    (IntermediateField.subgroupEquivAlgEquiv H).symm (fun _ _ => Subtype.ext rfl) i).symm

/-- The fixed subring of `H` in the supplied integer ring of `L` is the
supplied integer ring of the actual fixed field. -/
def fixedSubringEquiv (H : Subgroup Gal(L.Carrier/K.Carrier))
    (S : (Padic.fixedPadicField K L H).TopologicalData) :
    letI := Padic.integerAction T K.Carrier
    FixedPoints.subring T.Integers H ≃+* S.Integers := by
  letI := Padic.integerAction T K.Carrier
  exact
  { toFun x := ⟨⟨((x : T.Integers) : L.Carrier), fun h => congrArg Subtype.val (x.2 h)⟩,
      (PadicField.TopologicalData.relative_mem_integers_iff S T _).mp (x : T.Integers).2⟩
    invFun y := ⟨⟨(((y : (Padic.fixedPadicField K L H).Carrier) :
        IntermediateField.fixedField H) : L.Carrier),
      (PadicField.TopologicalData.relative_mem_integers_iff S T _).mpr y.2⟩,
      fun h => Subtype.ext ((y : IntermediateField.fixedField H).2 h)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }

@[simp] theorem fixedSubringEquiv_coe (H : Subgroup Gal(L.Carrier/K.Carrier))
    (S : (Padic.fixedPadicField K L H).TopologicalData)
    (x : letI := Padic.integerAction T K.Carrier; FixedPoints.subring T.Integers H) :
    (((fixedSubringEquiv K L T H S x : (Padic.fixedPadicField K L H).Carrier) :
      IntermediateField.fixedField H) : L.Carrier) = ((x : T.Integers) : L.Carrier) := rfl

/-- The fixed-subring identification intertwines the quotient action with the
actual normal restriction. -/
theorem fixedSubringEquiv_smul [IsGalois K.Carrier L.Carrier]
    (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (Padic.fixedPadicField K L H).TopologicalData) (g : Gal(L.Carrier/K.Carrier))
    (a : letI := Padic.integerAction T K.Carrier; FixedPoints.subring T.Integers H) :
    letI := Padic.integerAction T K.Carrier
    letI := Padic.integerAction S K.Carrier
    fixedSubringEquiv K L T H S ((QuotientGroup.mk g : Gal(L.Carrier/K.Carrier) ⧸ H) • a) =
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier)
          (IntermediateField.fixedField H) g :
          (Padic.fixedPadicField K L H).Carrier ≃ₐ[K.Carrier]
            (Padic.fixedPadicField K L H).Carrier) •
        fixedSubringEquiv K L T H S a := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  apply Subtype.ext
  apply Subtype.ext
  change g ((a : T.Integers) : L.Carrier) =
    ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) g
      ⟨((a : T.Integers) : L.Carrier), fun h => congrArg Subtype.val (a.2 h)⟩ :
        IntermediateField.fixedField H) : L.Carrier)
  exact (AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField H) g
    ⟨((a : T.Integers) : L.Carrier), fun h => congrArg Subtype.val (a.2 h)⟩).symm

/-- A subgroup whose image in the quotient is a source lower group of the
fixed subring restricts to the corresponding Library lower group of the actual
fixed field. -/
theorem map_restrictNormalHom_eq [IsGalois K.Carrier L.Carrier]
    (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (Padic.fixedPadicField K L H).TopologicalData)
    (X : Subgroup Gal(L.Carrier/K.Carrier)) (i : ℕ)
    (hX : letI := Padic.integerAction T K.Carrier
      X.map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup (FixedPoints.subring T.Integers H)
          (Gal(L.Carrier/K.Carrier) ⧸ H) i) :
    X.map (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier)
        (IntermediateField.fixedField H)) =
      Padic.lowerRamificationGroup S K.Carrier i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  haveI := finiteDimensional_carrier K L
  let f : (Gal(L.Carrier/K.Carrier) ⧸ H) ≃*
      ((Padic.fixedPadicField K L H).Carrier ≃ₐ[K.Carrier]
        (Padic.fixedPadicField K L H).Carrier) :=
    IsGalois.normalAutEquivQuotient H
  have hf : AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier)
      (IntermediateField.fixedField H) = (f : _ →* _).comp (QuotientGroup.mk' H) :=
    MonoidHom.ext fun g => (IsGalois.normalAutEquivQuotient_apply H g).symm
  have he : ∀ (g : Gal(L.Carrier/K.Carrier) ⧸ H) (a : FixedPoints.subring T.Integers H),
      fixedSubringEquiv K L T H S (g • a) = f g • fixedSubringEquiv K L T H S a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g => exact fixedSubringEquiv_smul K L T H S g a
  rw [hf, ← Subgroup.map_map, hX]
  exact map_lowerRamificationGroup_of_equivariant (fixedSubringEquiv K L T H S) f he i

/-- The Library lower-group orders of the actual fixed field over `K` are the
source orders of the quotient acting on the fixed subring. -/
theorem lowerGroupOrder_fixedPadicField [IsGalois K.Carrier L.Carrier]
    (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (Padic.fixedPadicField K L H).TopologicalData) (i : ℕ) :
    letI := Padic.integerAction T K.Carrier
    Padic.lowerGroupOrder S K.Carrier i =
      IsLocalRing.lowerRamificationCard (FixedPoints.subring T.Integers H)
        (Gal(L.Carrier/K.Carrier) ⧸ H) i := by
  letI := Padic.integerAction T K.Carrier
  letI := Padic.integerAction S K.Carrier
  haveI := finiteDimensional_carrier K L
  let f : (Gal(L.Carrier/K.Carrier) ⧸ H) ≃*
      ((Padic.fixedPadicField K L H).Carrier ≃ₐ[K.Carrier]
        (Padic.fixedPadicField K L H).Carrier) :=
    IsGalois.normalAutEquivQuotient H
  have he : ∀ (g : Gal(L.Carrier/K.Carrier) ⧸ H) (a : FixedPoints.subring T.Integers H),
      fixedSubringEquiv K L T H S (g • a) = f g • fixedSubringEquiv K L T H S a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g => exact fixedSubringEquiv_smul K L T H S g a
  exact lowerRamificationCard_of_equivariant (fixedSubringEquiv K L T H S) f he i

/-! ## The Library propositions -/

/-- Herbrand's theorem in upper numbering for the actual normal restriction. -/
theorem upperQuotientCompatibility [IsGalois K.Carrier L.Carrier] :
    Padic.UpperQuotientCompatibility K L T := by
  intro H _ S v hv
  letI := Padic.integerAction T K.Carrier
  haveI := finiteDimensional_carrier K L
  rcases hv.eq_or_lt with rfl | hv
  · rw [Padic.upperRamificationGroup_neg_one, Padic.upperRamificationGroup_neg_one,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨qT, hqT0, hvqT, hT⟩ := exists_rat_upperRamificationGroup_eq T K.Carrier hv
  obtain ⟨qS, hqS0, hvqS, hS⟩ := exists_rat_upperRamificationGroup_eq S K.Carrier hv
  have hw0 : (0 : ℚ) ≤ min qT qS := le_min hqT0 hqS0
  have hvw : v ≤ ((min qT qS : ℚ) : ℝ) := by
    push_cast
    exact le_min hvqT hvqS
  rw [← hT _ hvw (by push_cast; exact min_le_left _ _),
    ← hS _ hvw (by push_cast; exact min_le_right _ _),
    upperRamificationGroup_ratCast T K.Carrier (lowerGroupOrder_eq_source T K.Carrier) hw0,
    upperRamificationGroup_ratCast S K.Carrier (lowerGroupOrder_fixedPadicField K L T H S) hw0]
  exact map_restrictNormalHom_eq K L T H S _ _
    (IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
      (source_map_lowerRamificationGroup_mk K L T H) _ hw0)

/-- The phi tower law through the actual fixed field of a normal subgroup. -/
theorem herbrandPhi_fixedField_tower [IsGalois K.Carrier L.Carrier]
    (H : Subgroup Gal(L.Carrier/K.Carrier)) [H.Normal]
    (S : (Padic.fixedPadicField K L H).TopologicalData) (u : ℝ) :
    Padic.herbrandPhi T K.Carrier u =
      Padic.herbrandPhi S K.Carrier
        (Padic.herbrandPhi T (IntermediateField.fixedField H) u) := by
  letI := Padic.integerAction T K.Carrier
  haveI := finiteDimensional_carrier K L
  have hrat : ∀ q : ℚ, Padic.herbrandPhi T K.Carrier q =
      Padic.herbrandPhi S K.Carrier
        (Padic.herbrandPhi T (IntermediateField.fixedField H) q) := by
    intro q
    rcases le_or_gt q 0 with hq | hq
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
      rw [Padic.herbrandPhi_of_nonpos T _ hq', Padic.herbrandPhi_of_nonpos T _ hq',
        Padic.herbrandPhi_of_nonpos S _ hq']
    · have hH := herbrandPhi_ratCast T (IntermediateField.fixedField H)
        (lowerGroupOrder_fixedField K L T H) hq.le
      have hφ0 : 0 ≤ IsLocalRing.herbrandPhi T.Integers H q := by
        have h := Padic.herbrandPhi_pos T (IntermediateField.fixedField H)
          (by exact_mod_cast hq : (0 : ℝ) < q)
        rw [hH] at h
        exact_mod_cast h.le
      rw [herbrandPhi_ratCast T K.Carrier (lowerGroupOrder_eq_source T K.Carrier) hq.le, hH,
        herbrandPhi_ratCast S K.Carrier (lowerGroupOrder_fixedPadicField K L T H S) hφ0,
        IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
          (source_map_lowerRamificationGroup_mk K L T H) hq.le]
  have hcont : Continuous fun u => Padic.herbrandPhi S K.Carrier
      (Padic.herbrandPhi T (IntermediateField.fixedField H) u) :=
    (Padic.herbrandPhi_continuous S K.Carrier).comp (Padic.herbrandPhi_continuous T _)
  exact congrFun (Continuous.ext_on Rat.denseRange_cast
    (Padic.herbrandPhi_continuous T K.Carrier) hcont (by rintro _ ⟨q, rfl⟩; exact hrat q)) u

/-- Herbrand's theorem in lower numbering for the actual normal restriction. -/
theorem herbrandNormalSubgroup [IsGalois K.Carrier L.Carrier] :
    Padic.HerbrandNormalSubgroup K L T := by
  intro H _ S u hu
  have hv : -1 ≤ Padic.herbrandPhi T K.Carrier u := by
    rw [← Padic.herbrandPhi_neg_one T K.Carrier]
    exact (Padic.herbrandPhi_strictMono T K.Carrier).monotone hu
  rw [← Padic.upperRamificationGroup_phi T K.Carrier u,
    upperQuotientCompatibility K L T H S _ hv, herbrandPhi_fixedField_tower K L T H S u,
    Padic.upperRamificationGroup_phi]

/-- The automorphisms over the actual fixed field are exactly the subgroup. -/
theorem range_restrictScalarsHom_fixedField (H : Subgroup Gal(L.Carrier/K.Carrier)) :
    (AlgEquiv.restrictScalarsHom K.Carrier :
      (L.Carrier ≃ₐ[IntermediateField.fixedField H] L.Carrier) →*
        (L.Carrier ≃ₐ[K.Carrier] L.Carrier)).range = H := by
  haveI := finiteDimensional_carrier K L
  conv_rhs => rw [← IntermediateField.fixingSubgroup_fixedField H]
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    exact ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm τ).2
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv _ ⟨σ, hσ⟩, AlgEquiv.ext fun _ => rfl⟩

theorem restrictScalars_mem_lowerRamificationGroup_iff (H : Subgroup Gal(L.Carrier/K.Carrier))
    (τ : L.Carrier ≃ₐ[IntermediateField.fixedField H] L.Carrier) (i : ℕ) :
    τ.restrictScalars K.Carrier ∈ Padic.lowerRamificationGroup T K.Carrier i ↔
      τ ∈ Padic.lowerRamificationGroup T (IntermediateField.fixedField H) i :=
  Iff.rfl

/-- Lower numbering of an actual subgroup is the intersection with the lower
filtration of the full group. -/
theorem lowerSubgroupCompatibility [IsGalois K.Carrier L.Carrier] :
    Padic.LowerSubgroupCompatibility K L T := by
  intro H u hu
  rcases hu.eq_or_lt with rfl | hu
  · rw [Padic.lowerRamificationGroupReal_neg_one, Padic.lowerRamificationGroupReal_neg_one,
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

end Galois

end Langlands.Ramification.HerbrandBridge
