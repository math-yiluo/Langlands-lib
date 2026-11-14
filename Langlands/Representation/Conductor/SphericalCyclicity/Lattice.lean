import Langlands.Representation.Conductor.SphericalCyclicity.Extension

/-!
# Translates of extensions by zero

For `h` in `GL_(n+1)(F)` the extension of the translate `ρ'(h) ψ` is a finite linear
combination of right translates of the extension of `ψ`.  Consequently the preimage of a
subrepresentation under the extension map is a subrepresentation.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.Induction
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

variable {n : ℕ}

/-! ### The lattice of small vectors -/

/-- The additive subgroup of vectors all of whose coordinates have valuation `< 1`. -/
def smallSubgroup (m : ℕ) : AddSubgroup (Fin m → F) where
  carrier := {v | IsSmall v}
  add_mem' {a b} ha hb i := by
    change 𝒱 (a i + b i) < 1
    exact Valuation.map_add_lt _ (ha i) (hb i)
  zero_mem' i := by
    change 𝒱 (0 : F) < 1
    rw [map_zero]
    exact zero_lt_one
  neg_mem' {a} ha i := by
    change 𝒱 (-a i) < 1
    rw [Valuation.map_neg]
    exact ha i

theorem mem_smallSubgroup {m : ℕ} (v : Fin m → F) : v ∈ smallSubgroup m ↔ IsSmall v :=
  Iff.rfl

include hϖ in
theorem exists_pow_mul_le_one (x : F) : ∃ N : ℕ, 𝒱 ((ϖ : F) ^ N * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨k, hk⟩ := hϖ.2 x hx
  refine ⟨k.natAbs, ?_⟩
  have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation F) ϖ
  rw [map_mul, map_pow, hk, ← zpow_natCast, ← zpow_add₀ hpos.ne']
  exact zpow_le_one₀ hpos hϖ.1.le (by omega)

include hϖ in
theorem val_pow_mul_antitone {N M : ℕ} (hNM : N ≤ M) (x : F) :
    𝒱 ((ϖ : F) ^ M * x) ≤ 𝒱 ((ϖ : F) ^ N * x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  have h : (ϖ : F) ^ (N + k) * x = (ϖ : F) ^ k * ((ϖ : F) ^ N * x) := by ring
  rw [h, map_mul (𝒱) ((ϖ : F) ^ k)]
  exact mul_le_of_le_one_left zero_le (by rw [map_pow]; exact pow_le_one₀ zero_le hϖ.1.le)

include hϖ in
/-- Some power of the uniformizer times a given matrix is integral. -/
theorem exists_pow_mul_integral {m : ℕ} (A : Matrix (Fin m) (Fin m) F) :
    ∃ N : ℕ, ∀ i j, 𝒱 ((ϖ : F) ^ N * A i j) ≤ 1 := by
  choose N hN using fun p : Fin m × Fin m => exists_pow_mul_le_one hϖ (A p.1 p.2)
  refine ⟨Finset.univ.sup N, fun i j => ?_⟩
  exact (val_pow_mul_antitone hϖ (Finset.le_sup (Finset.mem_univ (i, j))) _).trans (hN (i, j))

/-! ### Topology of the lattice -/

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem ball_eq_preimage :
    {x : F | 𝒱 x < 1} = (fun x => (ϖ : F)⁻¹ * x) ⁻¹' ((𝒪 : Subring F) : Set F) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
  exact ⟨val_inv_uniformizer_mul_le_one hϖ, val_lt_one_of_inv_uniformizer_mul_le_one hϖ⟩

include hϖ in
theorem isOpen_ball_one : IsOpen {x : F | 𝒱 x < 1} := by
  rw [ball_eq_preimage hϖ]
  exact Valuation.isOpen_integer.preimage (continuous_const.mul continuous_id)

include hϖ in
theorem isCompact_ball_one : IsCompact {x : F | 𝒱 x < 1} := by
  have h : {x : F | 𝒱 x < 1} = {x : F | 𝒱 x ≤ 𝒱 (ϖ : F)} := by
    ext x
    exact val_lt_one_iff_le_uniformizer hϖ x
  rw [h]
  exact IsNonarchimedeanLocalField.isCompact_closedBall F _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_smallSubgroup (m : ℕ) :
    ((smallSubgroup m : AddSubgroup (Fin m → F)) : Set (Fin m → F)) =
      Set.univ.pi (fun _ => {x : F | 𝒱 x < 1}) := by
  ext v
  simp only [SetLike.mem_coe, mem_smallSubgroup, IsSmall, Set.mem_pi, Set.mem_univ,
    Set.mem_ofPred_eq, true_imp_iff]

include hϖ in
theorem isOpen_smallSubgroup (m : ℕ) :
    IsOpen ((smallSubgroup m : AddSubgroup (Fin m → F)) : Set (Fin m → F)) := by
  rw [coe_smallSubgroup]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_ball_one hϖ)

include hϖ in
theorem isCompact_smallSubgroup (m : ℕ) :
    IsCompact ((smallSubgroup m : AddSubgroup (Fin m → F)) : Set (Fin m → F)) := by
  rw [coe_smallSubgroup]
  exact isCompact_univ_pi (fun _ => isCompact_ball_one hϖ)

/-! ### A sublattice of finite index -/

/-- The vectors `u` with `A u` small. -/
def preSmall {m : ℕ} (A : Matrix (Fin m) (Fin m) F) : AddSubgroup (Fin m → F) :=
  (smallSubgroup m).comap (Matrix.mulVecLin A).toAddMonoidHom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_preSmall {m : ℕ} (A : Matrix (Fin m) (Fin m) F) (u : Fin m → F) :
    u ∈ preSmall A ↔ IsSmall (A *ᵥ u) :=
  Iff.rfl

include hϖ in
theorem isOpen_preSmall {m : ℕ} (A : Matrix (Fin m) (Fin m) F) :
    IsOpen ((preSmall A : AddSubgroup (Fin m → F)) : Set (Fin m → F)) := by
  rw [preSmall, AddSubgroup.coe_comap]
  exact (isOpen_smallSubgroup hϖ m).preimage
    (Continuous.matrix_mulVec continuous_const continuous_id)

/-- `preSmall A` as a subgroup of the small vectors. -/
def preSmallIn {m : ℕ} (A : Matrix (Fin m) (Fin m) F) : AddSubgroup (smallSubgroup (F := F) m) :=
  (preSmall A).addSubgroupOf (smallSubgroup m)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_preSmallIn {m : ℕ} (A : Matrix (Fin m) (Fin m) F) (u : smallSubgroup (F := F) m) :
    u ∈ preSmallIn A ↔ (u : Fin m → F) ∈ preSmall A :=
  AddSubgroup.mem_addSubgroupOf

include hϖ in
theorem finite_quotient_preSmallIn {m : ℕ} (A : Matrix (Fin m) (Fin m) F) :
    Finite ((smallSubgroup (F := F) m) ⧸ preSmallIn A) := by
  have : CompactSpace (smallSubgroup (F := F) m) :=
    isCompact_iff_compactSpace.mp (isCompact_smallSubgroup hϖ m)
  exact AddSubgroup.quotient_finite_of_isOpen _
    (AddSubgroup.addSubgroupOf_isOpen _ _ (isOpen_preSmall hϖ A))

/-! ### Sums of cell functions -/

/-- A cell function whose condition is partitioned by finitely many conditions is the sum
of the corresponding cell functions. -/
theorem cellFun_sum {ι : Type*} [Fintype ι] {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 2) → ℂˣ) (P : ι → (Fin (n + 1) → F) → Prop) (P0 : (Fin (n + 1) → F) → Prop)
    (φ : GL (Fin (n + 1)) F → ℂ) (x : GL (Fin (n + 2)) F)
    (hsub : ∀ i v, P i v → P0 v) (huniq : ∀ v, P0 v → ∃ i, P i v ∧ ∀ j, P j v → j = i) :
    ∑ i, cellFun hϖ hq z (P i) φ x = cellFun hϖ hq z P0 φ x := by
  by_cases hx : IsUnit (low x.val).det ∧ P0 (cellVec x)
  · obtain ⟨i0, hi0, hu⟩ := huniq _ hx.2
    rw [Finset.sum_eq_single i0, cellFun_of hϖ φ ⟨hx.1, hi0⟩, cellFun_of hϖ φ hx]
    · intro j _ hj
      exact cellFun_of_not hϖ φ (fun h => hj (hu j h.2))
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · rw [cellFun_of_not hϖ φ hx]
    apply Finset.sum_eq_zero
    intro i _
    exact cellFun_of_not hϖ φ (fun h => hx ⟨h.1, hsub i _ h.2⟩)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If `ϖ ^ N h` is integral, then every `u` with `ϖ⁻ᴺ h⁻¹ u` small is small. -/
theorem preSmall_le_smallSubgroup (h : GL (Fin (n + 1)) F) {N : ℕ}
    (hN : ∀ i j, 𝒱 ((ϖ : F) ^ N * h.val i j) ≤ 1) :
    preSmall ((((ϖ ^ N)⁻¹ : Fˣ) : F) • (h⁻¹ : GL (Fin (n + 1)) F).val) ≤
      smallSubgroup (n + 1) := by
  intro u hu
  rw [mem_preSmall] at hu
  rw [mem_smallSubgroup]
  have hinv : (ϖ : F) ^ N * (((ϖ ^ N)⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    exact mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero)
  have e : u = ((ϖ : F) ^ N • h.val) *ᵥ
      (((((ϖ ^ N)⁻¹ : Fˣ) : F) • (h⁻¹ : GL (Fin (n + 1)) F).val) *ᵥ u) := by
    rw [mulVec_mulVec, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv, one_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [e]
  refine mulVec_val_lt_one (fun i j => mem_of_val_le_one ?_) hu
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hN i j

/-! ### Values of finite sums -/

/-- Evaluation at a point, as a linear functional on the principal series. -/
def evalAt {m q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (m + 1) → ℂˣ)
    (x : GL (Fin (m + 1)) F) : PrincipalSeries hϖ m hq z →ₗ[ℂ] ℂ where
  toFun f := value hϖ m f x
  map_add' f g := value_add hϖ f g x
  map_smul' c f := value_smul hϖ c f x

theorem value_sum {m q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (m + 1) → ℂˣ}
    {ι : Type*} (s : Finset ι) (f : ι → PrincipalSeries hϖ m hq z) (x : GL (Fin (m + 1)) F) :
    value hϖ m (∑ i ∈ s, f i) x = ∑ i ∈ s, value hϖ m (f i) x :=
  map_sum (evalAt hϖ hq z x) f s

/-! ### Translates of extensions -/

section Translate

variable {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 2) → ℂˣ)

/-- The extension evaluated at `x L(y) diag(α, h)`. -/
theorem extFun_mul_translate (ψ : PrincipalSeries hϖ n hq (tailParam z))
    (x : GL (Fin (n + 2)) F) (y : Fin (n + 1) → F) (α : Fˣ) (h : GL (Fin (n + 1)) F) :
    extFun hϖ ψ (x * (lowerUnip y * blockDiag α h)) =
      ((z 0 ^ ord hϖ α * sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ α + ordDet hϖ h) : ℂˣ) :
        ℂ) *
        cellFun hϖ hq z (fun v => IsSmall ((α : F) • ((h⁻¹ : GL (Fin (n + 1)) F).val *ᵥ (v + y))))
          (value hϖ n (principalSeries hϖ n hq (tailParam z) h ψ)) x := by
  rw [extFun, ← mul_assoc, cellFun_mul_blockDiag, cellFun_mul_lowerUnip]
  rfl

/-- The extension of a translate `ρ'(h) ψ` is a scalar multiple of a finite sum of right
translates of the extension of `ψ`. -/
theorem exists_extend_translate_eq (ψ : PrincipalSeries hϖ n hq (tailParam z))
    (h : GL (Fin (n + 1)) F) :
    ∃ (ι : Type uF) (_ : Fintype ι) (g : ι → GL (Fin (n + 2)) F) (c : ℂ),
      extend hϖ hq z (principalSeries hϖ n hq (tailParam z) h ψ) =
        c • ∑ i, principalSeries hϖ (n + 1) hq z (g i) (extend hϖ hq z ψ) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_integral hϖ h.val
  set α : Fˣ := (ϖ ^ N)⁻¹ with hα
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F := (α : F) • (h⁻¹ : GL (Fin (n + 1)) F).val
    with hA
  have hle : preSmall A ≤ smallSubgroup (n + 1) := preSmall_le_smallSubgroup h hN
  have := finite_quotient_preSmallIn hϖ A
  let _ : Fintype (smallSubgroup (F := F) (n + 1) ⧸ preSmallIn A) := Fintype.ofFinite _
  let y : (smallSubgroup (F := F) (n + 1) ⧸ preSmallIn A) → Fin (n + 1) → F :=
    fun ξ => ((Quotient.out ξ : smallSubgroup (F := F) (n + 1)) : Fin (n + 1) → F)
  have hy : ∀ ξ, y ξ ∈ smallSubgroup (n + 1) := fun ξ => (Quotient.out ξ).property
  have hPA : ∀ (v w : Fin (n + 1) → F),
      IsSmall ((α : F) • ((h⁻¹ : GL (Fin (n + 1)) F).val *ᵥ (v + w))) ↔ v + w ∈ preSmall A := by
    intro v w
    rw [mem_preSmall, hA, smul_mulVec]
  have hquot : ∀ ξ ξ', y ξ - y ξ' ∈ preSmall A → ξ = ξ' := by
    intro ξ ξ' hm
    rw [← QuotientAddGroup.out_eq' ξ, ← QuotientAddGroup.out_eq' ξ', QuotientAddGroup.eq,
      mem_preSmallIn, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    have := neg_mem hm
    rwa [neg_sub, sub_eq_neg_add] at this
  let cu : ℂˣ :=
    z 0 ^ ord hϖ α * sqrtResidueUnit hq ^ (-((n : ℤ) + 1) * ord hϖ α + ordDet hϖ h)
  refine ⟨_, inferInstance, fun ξ => lowerUnip (y ξ) * blockDiag α h, ((cu⁻¹ : ℂˣ) : ℂ), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change extFun hϖ (principalSeries hϖ n hq (tailParam z) h ψ) x =
    value hϖ (n + 1) (((cu⁻¹ : ℂˣ) : ℂ) • ∑ ξ, principalSeries hϖ (n + 1) hq z
      (lowerUnip (y ξ) * blockDiag α h) (extend hϖ hq z ψ)) x
  rw [value_smul, value_sum]
  have key : ∀ ξ, value hϖ (n + 1) (principalSeries hϖ (n + 1) hq z
      (lowerUnip (y ξ) * blockDiag α h) (extend hϖ hq z ψ)) x =
        (cu : ℂ) * cellFun hϖ hq z
          (fun v => IsSmall ((α : F) • ((h⁻¹ : GL (Fin (n + 1)) F).val *ᵥ (v + y ξ))))
          (value hϖ n (principalSeries hϖ n hq (tailParam z) h ψ)) x :=
    fun ξ => extFun_mul_translate hϖ hq z ψ x (y ξ) α h
  rw [Finset.sum_congr rfl (fun ξ _ => key ξ), ← Finset.mul_sum, ← mul_assoc, Units.inv_mul,
    one_mul, cellFun_sum hϖ hq z _ IsSmall]
  · rfl
  · intro ξ v hv
    rw [hPA] at hv
    have := (smallSubgroup (n + 1)).sub_mem (hle hv) (hy ξ)
    rwa [add_sub_cancel_right] at this
  · intro v hv
    set ξ0 : smallSubgroup (F := F) (n + 1) ⧸ preSmallIn A :=
      QuotientAddGroup.mk (-⟨v, hv⟩ : smallSubgroup (F := F) (n + 1)) with hξ0
    have hex : v + y ξ0 ∈ preSmall A := by
      have h0 := QuotientAddGroup.out_eq' ξ0
      rw [hξ0, QuotientAddGroup.eq, mem_preSmallIn,
        AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_neg] at h0
      have := neg_mem h0
      rw [neg_add, neg_neg, neg_neg] at this
      rw [add_comm v (y ξ0)]
      exact this
    refine ⟨ξ0, (hPA _ _).2 hex, fun ξ hξ => hquot ξ ξ0 ?_⟩
    rw [hPA] at hξ
    have := sub_mem hξ hex
    rwa [add_sub_add_left_eq_sub] at this

/-- Extensions in a subrepresentation stay there after translating the argument. -/
theorem extend_translate_mem (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    {ψ : PrincipalSeries hϖ n hq (tailParam z)} (hψ : extend hϖ hq z ψ ∈ S)
    (h : GL (Fin (n + 1)) F) :
    extend hϖ hq z (principalSeries hϖ n hq (tailParam z) h ψ) ∈ S := by
  obtain ⟨ι, _, g, c, he⟩ := exists_extend_translate_eq hϖ hq z ψ h
  rw [he]
  exact S.toSubmodule.smul_mem c
    (S.toSubmodule.sum_mem fun i _ => S.apply_mem_toSubmodule (g i) hψ)

/-- The preimage of a subrepresentation under the extension map. -/
def pullback (S : Subrepresentation (principalSeries hϖ (n + 1) hq z)) :
    Subrepresentation (principalSeries hϖ n hq (tailParam z)) where
  toSubmodule := S.toSubmodule.comap (extend hϖ hq z)
  apply_mem_toSubmodule h _ hv := extend_translate_mem hϖ hq z S hv h

theorem mem_pullback (S : Subrepresentation (principalSeries hϖ (n + 1) hq z))
    (ψ : PrincipalSeries hϖ n hq (tailParam z)) :
    ψ ∈ pullback hϖ hq z S ↔ extend hϖ hq z ψ ∈ S :=
  Iff.rfl

end Translate

end Langlands.Conductor.SphericalCyclicity
