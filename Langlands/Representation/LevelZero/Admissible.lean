import Langlands.Representation.LevelZero.JacquetVanishing
import Langlands.Group.GL.BlockUnipotentPattern
import Langlands.Group.GL.CartanProof
import Langlands.Representation.Whittaker.UpperUnipotentCoinvariantReduction

/-!
# Admissibility of level-zero induction from a cuspidal representation

Let `σ` be a finite-dimensional cuspidal representation of `GL_{m+1}(k)` and `Λ` its inflation
to `J = ϖ^ℤ GL_{m+1}(𝒪)`. The smooth induced representation of `Λ` from `J` to `GL_{m+1}(F)`
is admissible. For an open subgroup `S`, a function fixed by `S` is determined by its values
at the finitely many points `t r`, where `r` runs over representatives of `K / (K ∩ S)` and
`t` over diagonal matrices of normalized exponents bounded by a constant depending on `S`.
Indeed, by the Cartan decomposition every element is `k₁ ϖ^c t r s` with `t` of monotone
normalized exponent; if `t` has a gap at least the constant between two consecutive
exponents, then the value at `t r` is fixed by `σ` of the unipotent radical of the
corresponding two-block parabolic over `k`, hence is zero by cuspidality.
-/

noncomputable section

open Filter Topology

namespace Langlands.LevelZero

open GeneralLinear ValuativeRel Langlands.Induction
open Langlands.Classification.SupercuspidalDerivativeVanishing (IsBlockUnipotent)

universe u uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ### Small balls -/

section Balls

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)

include hϖ in
/-- Every neighborhood of zero contains all elements of valuation at most `v(ϖ)^M`, for some
`M`. -/
theorem exists_pow_ball {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ M : ℕ, ∀ x : F, valuation F x ≤ valuation F (ϖ : F) ^ M → x ∈ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).mp hs
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero F)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact γ.ne_zero hy.symm
  obtain ⟨e, he⟩ := hϖ.2 y hy0
  have hpos : 0 < valuation F (ϖ : F) := Iwasawa.valuation_pos _ ϖ
  refine ⟨(e + 1).toNat, fun x hx => hγ ?_⟩
  change valuation F x < γ
  rw [← hy, he]
  calc valuation F x ≤ valuation F (ϖ : F) ^ (e + 1).toNat := hx
    _ = valuation F (ϖ : F) ^ (((e + 1).toNat : ℕ) : ℤ) := (zpow_natCast _ _).symm
    _ ≤ valuation F (ϖ : F) ^ (e + 1) :=
        zpow_le_zpow_right_of_le_one₀ hpos hϖ.1.le (Int.self_le_toNat _)
    _ < valuation F (ϖ : F) ^ e := zpow_lt_zpow_right_of_lt_one₀ hpos hϖ.1 (lt_add_one e)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
theorem pow_le_pow_of_le {M M' : ℕ} (h : M ≤ M') :
    valuation F (ϖ : F) ^ M' ≤ valuation F (ϖ : F) ^ M := by
  have hpos : 0 < valuation F (ϖ : F) := Iwasawa.valuation_pos _ ϖ
  have := zpow_le_zpow_right_of_le_one₀ hpos hϖ.1.le (Nat.cast_le.mpr h : (M : ℤ) ≤ M')
  simpa only [zpow_natCast] using this

variable {n a b : ℕ}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem continuous_single (i : Fin a) (j : Fin b) :
    Continuous fun x : F => Matrix.single i j x := by
  refine continuous_matrix fun i' j' => ?_
  simp only [Matrix.single_apply]
  by_cases h : i = i' ∧ j = j'
  · simp only [h, and_self, ite_true]
    exact continuous_id
  · simp only [h, ite_false]
    exact continuous_const

include hϖ in
/-- An open subgroup contains every block upper unipotent matrix with small entries. -/
theorem exists_blockUnipotent_mem (h : a + b = n) (S : Subgroup (GeneralLinear n F))
    (hS : IsOpen (S : Set (GeneralLinear n F))) :
    ∃ M : ℕ, ∀ X : Matrix (Fin a) (Fin b) F,
      (∀ i j, valuation F (X i j) ≤ valuation F (ϖ : F) ^ M) → blockUnipotent h X ∈ S := by
  classical
  have hentry : ∀ p : Fin a × Fin b, ∃ M : ℕ, ∀ x : F,
      valuation F x ≤ valuation F (ϖ : F) ^ M →
        blockUnipotent h (Matrix.single p.1 p.2 x) ∈ S := by
    intro p
    have hc : Continuous fun x : F => blockUnipotent h (Matrix.single p.1 p.2 x) :=
      (continuous_blockUnipotent h).comp (continuous_single p.1 p.2)
    have hmem : (fun x : F => blockUnipotent h (Matrix.single p.1 p.2 x)) ⁻¹'
        (S : Set (GeneralLinear n F)) ∈ 𝓝 (0 : F) := by
      apply hc.continuousAt.preimage_mem_nhds
      rw [Matrix.single_zero, blockUnipotent_zero]
      exact hS.mem_nhds S.one_mem
    exact exists_pow_ball hϖ hmem
  choose Mp hMp using hentry
  refine ⟨Finset.univ.sup Mp, fun X hX => ?_⟩
  have hsum : ∀ T : Finset (Fin a × Fin b),
      blockUnipotent h (∑ p ∈ T, Matrix.single p.1 p.2 (X p.1 p.2)) ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert p T hp ih =>
      rw [Finset.sum_insert hp, blockUnipotent_add]
      refine S.mul_mem (hMp p _ ?_) ih
      exact (hX p.1 p.2).trans
        (pow_le_pow_of_le hϖ (Finset.le_sup (Finset.mem_univ p)))
  have hX' : X = ∑ p : Fin a × Fin b, Matrix.single p.1 p.2 (X p.1 p.2) := by
    rw [Fintype.sum_prod_type]
    exact Matrix.matrix_eq_sum_single X
  rw [hX']
  exact hsum Finset.univ

end Balls

/-! ### Cartan decomposition with monotone exponent -/

section Cartan

variable {m : ℕ} {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hϖ in
/-- Every element is `k₁ · diag(ϖ^μ) · k₂` with integral `k₁, k₂` and monotone `μ`. -/
theorem exists_cartan_monotone (x : GeneralLinear (m + 1) F) :
    ∃ k₁ ∈ maximalCompact (F := F) m, ∃ k₂ ∈ maximalCompact (F := F) m,
      ∃ μ : Fin (m + 1) → ℤ, Monotone μ ∧ x = k₁ * Iwasawa.torus ϖ μ * k₂ := by
  obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hx⟩ := Cartan.exists_cartan hϖ (m + 1) x⁻¹
  refine ⟨k₂⁻¹, (maximalCompact (F := F) m).inv_mem hk₂, k₁⁻¹,
    (maximalCompact (F := F) m).inv_mem hk₁, fun i => -lam i, fun i j hij => neg_le_neg (hlam hij),
    ?_⟩
  have htor : (Iwasawa.torus ϖ lam)⁻¹ = Iwasawa.torus ϖ (fun i => -lam i) := by
    rw [Iwasawa.torus_inv, Iwasawa.torus]
    congr 1
    funext i
    rw [zpow_neg]
  rw [← htor, ← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, ← hx, inv_inv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Splitting off a central power of the uniformizer. -/
theorem torus_eq_zpow_mul (μ : Fin (m + 1) → ℤ) (c : ℤ) :
    Iwasawa.torus ϖ μ = uniformizerScalar m ϖ ^ c * Iwasawa.torus ϖ (fun i => μ i - c) := by
  apply Units.ext
  rw [Units.val_mul, uniformizerScalar_zpow, Iwasawa.torus_val, Iwasawa.torus_val]
  change Matrix.diagonal _ = Matrix.scalar (Fin (m + 1)) ((ϖ ^ c : Fˣ) : F) * Matrix.diagonal _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Units.val_mul, ← zpow_add, add_sub_cancel]

end Cartan

/-! ### Admissibility -/

variable {m : ℕ} {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F))) W)

/-- **Gap lemma.** If the monotone exponent `μ` jumps by at least `M` after position `p`, and
`r⁻¹ U_p(ϖ^M) r ⊆ S`, then every `S`-fixed induced function vanishes at `diag(ϖ^μ) r`. -/
theorem eval_eq_zero_of_gap (hσ : FiniteGeneralLinear.IsCuspidal σ)
    (S : OpenSubgroup (GeneralLinear (m + 1) F))
    (f : SmoothFunctions (inducingSubgroup m ϖ) (inducingRep m hϖ σ))
    (hf : f ∈ fixedVectors (smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ σ))
      (S : Subgroup (GeneralLinear (m + 1) F)))
    (r : GeneralLinear (m + 1) F) {p : ℕ} (hp : 0 < p) (hpN : p < m + 1) (M : ℕ)
    (hM : ∀ X : Matrix (Fin p) (Fin (m + 1 - p)) F,
      (∀ i j, valuation F (X i j) ≤ valuation F (ϖ : F) ^ M) →
        r⁻¹ * blockUnipotent (by omega : p + (m + 1 - p) = m + 1) X * r ∈ S)
    (μ : Fin (m + 1) → ℤ)
    (hμ : ∀ i j : Fin (m + 1), i.val < p → p ≤ j.val → (M : ℤ) ≤ μ j - μ i) :
    eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f (Iwasawa.torus ϖ μ * r) = 0 := by
  classical
  have hh : p + (m + 1 - p) = m + 1 := by omega
  have hpos : 0 < valuation F (ϖ : F) := Iwasawa.valuation_pos _ ϖ
  apply hσ (ProductLeviChamber.twoBlock (m + 1) p hp hpN)
    (Whittaker.UpperUnipotentCoinvariant.cutShape_parabolic_ne_top _ _ hp hpN)
  intro γ hγ
  have hpat : IsBlockUnipotent p γ :=
    Whittaker.UpperUnipotentCoinvariant.isBlockUnipotent_of_mem_cutShape hp hpN hγ
  set γhat := IntegralReduction.lift (integers F) m γ with hγhat
  set t := Iwasawa.torus ϖ μ with ht
  set y : GeneralLinear (m + 1) F := t⁻¹ * (γhat : GeneralLinear (m + 1) F) * t with hy
  have hy_apply : ∀ i j, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      (((ϖ ^ μ i)⁻¹ : Fˣ) : F) * IntegralReduction.residueSection (integers F) (γ i j) *
        ((ϖ ^ μ j : Fˣ) : F) := by
    intro i j
    have := Iwasawa.diagonalUnits_mul_mul_apply (fun i => (ϖ ^ μ i)⁻¹) (fun i => ϖ ^ μ i)
      (γhat : GeneralLinear (m + 1) F) i j
    rw [← Iwasawa.torus_inv] at this
    exact this
  have hy_pat : ∀ i j : Fin (m + 1), (j.val < p ∨ p ≤ i.val) →
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = if i = j then 1 else 0 := by
    intro i j hij
    rw [hy_apply, hpat i j hij]
    by_cases he : i = j
    · subst he
      simp only [ite_true, IntegralReduction.residueSection_one, OneMemClass.coe_one, mul_one]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    · simp [he]
  have hy_eq := eq_blockUnipotent_of_pattern hh y hy_pat
  have hsmall : ∀ i j, valuation F (upperRightBlock hh
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ≤ valuation F (ϖ : F) ^ M := by
    intro i j
    simp only [upperRightBlock, Matrix.of_apply]
    rw [hy_apply]
    set i' := blockCut hh (Sum.inl i) with hi'
    set j' := blockCut hh (Sum.inr j) with hj'
    have hgap := hμ i' j' (by simp [hi']) (by simp [hj'])
    set c := IntegralReduction.residueSection (integers F) (γ i' j')
    have hint : valuation F (c : F) ≤ 1 := (Valuation.mem_integer_iff _ _).mp c.2
    have hval : valuation F ((((ϖ ^ μ i')⁻¹ : Fˣ) : F) * (c : F) * ((ϖ ^ μ j' : Fˣ) : F)) =
        valuation F (ϖ : F) ^ (μ j' - μ i') * valuation F (c : F) := by
      rw [map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
        Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, zpow_sub₀ hpos.ne', div_eq_mul_inv]
      ac_rfl
    rw [hval]
    calc valuation F (ϖ : F) ^ (μ j' - μ i') * valuation F (c : F)
        ≤ valuation F (ϖ : F) ^ (μ j' - μ i') := mul_le_of_le_one_right zero_le hint
      _ ≤ valuation F (ϖ : F) ^ ((M : ℕ) : ℤ) :=
          zpow_le_zpow_right_of_le_one₀ hpos hϖ.1.le hgap
      _ = valuation F (ϖ : F) ^ M := zpow_natCast _ _
  have hyS : r⁻¹ * y * r ∈ S := by
    have := hM _ hsmall
    rwa [← hy_eq] at this
  have hγK : (γhat : GeneralLinear (m + 1) F) ∈ maximalCompact (F := F) m := γhat.2
  have h1 : eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f
      ((γhat : GeneralLinear (m + 1) F) * (t * r)) =
        σ γ (eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f (t * r)) := by
    refine (eval_cov _ _ f ⟨_, maximalCompact_le_inducingSubgroup m ϖ hγK⟩ (t * r)).trans ?_
    rw [inducingRep_of_mem hϖ σ hγK]
    have hred : residueReduction m ⟨(γhat : GeneralLinear (m + 1) F), hγK⟩ = γ :=
      IntegralReduction.reduction_lift (integers F) m γ
    rw [hred]
  have h2 : (γhat : GeneralLinear (m + 1) F) * (t * r) = t * r * (r⁻¹ * y * r) := by
    rw [hy]; group
  have h3 : eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f (t * r * (r⁻¹ * y * r)) =
      eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f (t * r) := by
    have hfix := (mem_fixedVectors_iff (ρ := smoothInduced (inducingSubgroup m ϖ)
      (inducingRep m hϖ σ)) (S : Subgroup (GeneralLinear (m + 1) F)) f).mp hf ⟨_, hyS⟩
    rw [← Langlands.Induction.eval_smoothInduced, hfix]
  rw [← h1, h2, h3]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- With all consecutive gaps below `M`, a monotone exponent starting at `0` is bounded by
`i * M` at position `i`. -/
theorem le_mul_of_gaps_lt {μ : Fin (m + 1) → ℤ} (h0 : μ 0 = 0) {M : ℕ}
    (hgap : ∀ (n : ℕ) (hn : n + 1 < m + 1),
      μ ⟨n + 1, hn⟩ - μ ⟨n, by omega⟩ < M) :
    ∀ (n : ℕ) (hn : n < m + 1), μ ⟨n, hn⟩ ≤ n * M := by
  intro n
  induction n with
  | zero =>
    intro hn
    rw [show (⟨0, hn⟩ : Fin (m + 1)) = 0 from rfl, h0]
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hgap n hn
    push_cast
    linarith

theorem isCompact_maximalCompact :
    IsCompact (maximalCompact (F := F) m : Set (GeneralLinear (m + 1) F)) := by
  have h := Conductor.isCompact_levelOpenSubgroup F m 0
  have he : ((Conductor.levelOpenSubgroup F m 0 : Subgroup (GeneralLinear (m + 1) F)) :
      Set (GeneralLinear (m + 1) F)) = (maximalCompact (F := F) m : Set _) := by
    change ((Conductor.levelSubgroup F m 0 : Subgroup (GeneralLinear (m + 1) F)) :
      Set (GeneralLinear (m + 1) F)) = _
    rw [Conductor.levelSubgroup_zero]
  rw [← he]
  exact h

/-- **Admissibility.** The smooth induced representation of the inflation of a
finite-dimensional cuspidal representation from `J = ϖ^ℤ GL_{m+1}(𝒪)` is admissible. -/
theorem smoothInduced_isAdmissible [FiniteDimensional ℂ W]
    (hσ : FiniteGeneralLinear.IsCuspidal σ) :
    IsAdmissible (smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ σ)) := by
  classical
  refine ⟨smoothInduced_smooth _ _, fun S => ?_⟩
  -- a finite cover of `K` by translates `r S`
  obtain ⟨R, hRcover⟩ := (isCompact_maximalCompact (F := F) (m := m)).elim_finite_subcover
    (fun r : maximalCompact (F := F) m =>
      (fun g : GeneralLinear (m + 1) F => (r : GeneralLinear (m + 1) F)⁻¹ * g) ⁻¹'
        (S : Set (GeneralLinear (m + 1) F)))
    (fun r => S.isOpen.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.mpr ⟨⟨g, hg⟩, by simp⟩)
  -- a uniform bound for the block unipotent neighborhoods
  have hev : ∀ᶠ M in atTop, ∀ r ∈ R, ∀ p : Fin (m + 1), ∀ hp : 0 < p.val,
      ∀ X : Matrix (Fin p.val) (Fin (m + 1 - p.val)) F,
        (∀ i j, valuation F (X i j) ≤ valuation F (ϖ : F) ^ M) →
          (r : GeneralLinear (m + 1) F)⁻¹ *
            blockUnipotent (by omega : p.val + (m + 1 - p.val) = m + 1) X *
              (r : GeneralLinear (m + 1) F) ∈ S := by
    refine (eventually_all_finset R).mpr fun r _ => eventually_all.mpr fun p => ?_
    by_cases hp : 0 < p.val
    · let Sr : Subgroup (GeneralLinear (m + 1) F) :=
        (S : Subgroup (GeneralLinear (m + 1) F)).comap
          (MulAut.conj ((r : GeneralLinear (m + 1) F)⁻¹)).toMonoidHom
      have hSr : IsOpen (Sr : Set (GeneralLinear (m + 1) F)) :=
        S.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
      obtain ⟨M₀, hM₀⟩ := exists_blockUnipotent_mem hϖ
        (by omega : p.val + (m + 1 - p.val) = m + 1) Sr hSr
      refine eventually_atTop.mpr ⟨M₀, fun M hM _ X hX => ?_⟩
      have := hM₀ X fun i j => (hX i j).trans (pow_le_pow_of_le hϖ hM)
      simpa [Sr, MulAut.conj_apply] using this
    · exact Eventually.of_forall fun _ hp' => absurd hp' hp
  obtain ⟨M, hM⟩ := hev.exists
  -- evaluation at the finitely many points `diag(ϖ^c) r`
  let N := (m + 1) * M
  let I := (Fin (m + 1) → Fin (N + 1)) × R
  let E := smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ σ)
  let Φ : fixedVectors E (S : Subgroup (GeneralLinear (m + 1) F)) →ₗ[ℂ] (I → W) :=
    { toFun := fun f c => eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f.1
        (Iwasawa.torus ϖ (fun i => ((c.1 i : ℕ) : ℤ)) *
          ((c.2 : maximalCompact (F := F) m) : GeneralLinear (m + 1) F))
      map_add' := fun f g => by funext c; rfl
      map_smul' := fun a f => by funext c; rfl }
  refine Module.Finite.of_injective Φ ?_
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply Subtype.ext
  apply ext_eval
  intro x
  rw [Submodule.coe_zero, eval_zero]
  obtain ⟨k₁, hk₁, k₂, hk₂, μ, hμ, hx⟩ := exists_cartan_monotone hϖ x
  obtain ⟨r, hrR, hrk⟩ := Set.mem_iUnion₂.mp (hRcover hk₂)
  have hrk' : (r : GeneralLinear (m + 1) F)⁻¹ * k₂ ∈ S := hrk
  set c := μ 0
  set μ' : Fin (m + 1) → ℤ := fun i => μ i - c with hμ'
  set s := uniformizerScalar m ϖ
  have hcomm : k₁ * s ^ c = s ^ c * k₁ :=
    (Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ (uniformizerScalar_mem_center m ϖ) c) k₁)
  have hx' : x = (s ^ c * k₁) * (Iwasawa.torus ϖ μ' * r) *
      ((r : GeneralLinear (m + 1) F)⁻¹ * k₂) := by
    rw [hx, torus_eq_zpow_mul μ c, ← mul_assoc k₁, hcomm]
    group
    rfl
  have hJ : s ^ c * k₁ ∈ inducingSubgroup m ϖ := zpow_mul_mem_powerProduct _ _ _ c hk₁
  have hfix := (mem_fixedVectors_iff (ρ := E) (S : Subgroup (GeneralLinear (m + 1) F))
    f.1).mp f.2 ⟨_, hrk'⟩
  have hval : eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f.1 x =
      inducingRep m hϖ σ ⟨_, hJ⟩ (eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f.1
        (Iwasawa.torus ϖ μ' * r)) := by
    rw [hx', ← Langlands.Induction.eval_smoothInduced, hfix]
    exact eval_cov _ _ f.1 ⟨_, hJ⟩ _
  rw [hval]
  suffices h : eval (inducingSubgroup m ϖ) (inducingRep m hϖ σ) f.1
      (Iwasawa.torus ϖ μ' * r) = 0 by
    rw [h, map_zero]
  have hμ'0 : μ' 0 = 0 := by simp [hμ', c]
  have hμ'mono : Monotone μ' := fun i j hij => by simpa [hμ'] using hμ hij
  by_cases hgap : ∃ (n : ℕ) (hn : n + 1 < m + 1),
      (M : ℤ) ≤ μ' ⟨n + 1, hn⟩ - μ' ⟨n, by omega⟩
  · obtain ⟨n, hn, hMn⟩ := hgap
    have hMr := hM r hrR ⟨n + 1, hn⟩ (Nat.succ_pos n)
    refine eval_eq_zero_of_gap hϖ σ hσ S f.1 f.2 r (Nat.succ_pos n) hn M hMr μ' ?_
    intro i j hi hj
    have h1 : μ' ⟨n + 1, hn⟩ ≤ μ' j := hμ'mono (Fin.mk_le_mk.mpr (by simpa using hj))
    have h2 : μ' i ≤ μ' ⟨n, by omega⟩ := hμ'mono (Fin.mk_le_mk.mpr (by simp at hi; omega))
    linarith
  · push Not at hgap
    have hbound := le_mul_of_gaps_lt hμ'0 hgap
    have hnonneg : ∀ i, 0 ≤ μ' i := fun i => hμ'0 ▸ hμ'mono (Fin.zero_le i)
    have hle : ∀ i : Fin (m + 1), (μ' i).toNat < N + 1 := by
      intro i
      have h1 := hbound i.val i.isLt
      have h2 : (i.val : ℤ) * M ≤ (m : ℤ) * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) (by positivity)
      have h3 : (μ' i).toNat ≤ m * M := by
        have := Int.toNat_le.mpr (show μ' i ≤ ((m * M : ℕ) : ℤ) by push_cast; linarith)
        exact this
      have h4 : m * M ≤ N := Nat.mul_le_mul_right M (Nat.le_succ m)
      omega
    let cc : Fin (m + 1) → Fin (N + 1) := fun i => ⟨(μ' i).toNat, hle i⟩
    have hcc : (fun i => ((cc i : ℕ) : ℤ)) = μ' := by
      funext i
      exact Int.toNat_of_nonneg (hnonneg i)
    have := congrFun hf (cc, ⟨r, hrR⟩)
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hcc] at this
    exact this

end Langlands.LevelZero
