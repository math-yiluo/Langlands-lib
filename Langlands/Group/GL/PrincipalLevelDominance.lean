import Langlands.Group.GL.PrincipalBlockFactorizationProof
import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Representation.Whittaker.Iwasawa

/-!
# Principal levels in every rank and dominant torus sandwiches

For a valued field `k`, `rankPrincipalLevel k m a` is the image in `GL_m(k)` of the kernel of
reduction modulo the `a`-th power of the maximal ideal on `GL_m(O)`. For `m = n + 1` it is the
existing `Conductor.principalLevelSubgroup k n a`; at rank zero it is the trivial group.

The main result is the dominant sandwich property: for a positive level, an element `g` of the
principal level and antitone exponents `lam₁, lam₂`, one has
`ϖ^lam₁ g ϖ^lam₂ = x (ϖ^lam₁ ϖ^lam₂) y` with `x, y` in the same principal level. The proof
factors `g⁻¹` by the published principal-level Iwahori factorization for the singleton block
shape and conjugates the upper and lower factors by the dominant diagonal matrices.
-/

noncomputable section

namespace Langlands.GeneralLinear

open Matrix Langlands.Conductor Topology

universe u

/-! ### Conjugation of principal congruence factors by block scalars

These are copies of private lemmas of `Langlands.Group.GL.BlockIwahoriBasis`. -/

section Conjugation

private def EntryIdeal {k : Type*} [Field k] {n : ℕ}
    (O : Subring k) (I : Ideal O) (g : GeneralLinear n k) : Prop :=
  ∀ i j, ∃ x : O, x ∈ I ∧ (x : k) = g i j - (1 : Matrix (Fin n) (Fin n) k) i j

private theorem entryIdeal_upper_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.unipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨((a i * (a j)⁻¹ : kˣ) : k), ha i j hij⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change (((a i * (a j)⁻¹ : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => (((a i * (a j)⁻¹ : kˣ) : k) * z)) he
  · subst j
    simpa only [mul_inv_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hzero := (B.mem_parabolic_iff k g).mp
      ((B.mem_unipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩

private theorem entryIdeal_lower_inv_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_inv_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    have hzero := (B.mem_oppositeParabolic_iff k g).mp
      ((B.mem_oppositeUnipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩
  · subst j
    simpa only [inv_mul_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hratio : (((a i)⁻¹ * a j : kˣ) : k) ∈ O := by
      simpa only [mul_comm] using ha j i hij
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨(((a i)⁻¹ * a j : kˣ) : k), hratio⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change ((((a i)⁻¹ * a j : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => ((((a i)⁻¹ * a j : kˣ) : k) * z)) he

theorem principal_upper_conj
    {k : Type u} [Field k] {n : ℕ} (B : GeneralLinear.BlockShape (n + 1))
    (O : Subring k) (I : Ideal O) (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear (n + 1) k} (hg : g ∈ B.unipotentSubgroup k)
    (hK : g ∈ Conductor.principalCongruenceSubgroup O n I) :
    B.blockScalar k a * g * (B.blockScalar k a)⁻¹ ∈
      Conductor.principalCongruenceSubgroup O n I := by
  obtain ⟨hforward, hinverse⟩ :=
    (Conductor.mem_principalCongruenceSubgroup_iff O n I g).mp hK
  apply (Conductor.mem_principalCongruenceSubgroup_iff O n I _).mpr
  constructor
  · exact entryIdeal_upper_conj B O I a ha hg hforward
  · simpa only [EntryIdeal, _root_.mul_inv_rev, inv_inv, mul_assoc] using
      entryIdeal_upper_conj B O I a ha
        ((B.unipotentSubgroup k).inv_mem hg) hinverse

theorem principal_lower_inv_conj
    {k : Type u} [Field k] {n : ℕ} (B : GeneralLinear.BlockShape (n + 1))
    (O : Subring k) (I : Ideal O) (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear (n + 1) k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hK : g ∈ Conductor.principalCongruenceSubgroup O n I) :
    (B.blockScalar k a)⁻¹ * g * B.blockScalar k a ∈
      Conductor.principalCongruenceSubgroup O n I := by
  obtain ⟨hforward, hinverse⟩ :=
    (Conductor.mem_principalCongruenceSubgroup_iff O n I g).mp hK
  apply (Conductor.mem_principalCongruenceSubgroup_iff O n I _).mpr
  constructor
  · exact entryIdeal_lower_inv_conj B O I a ha hg hforward
  · simpa only [EntryIdeal, _root_.mul_inv_rev, inv_inv, mul_assoc] using
      entryIdeal_lower_inv_conj B O I a ha
        ((B.oppositeUnipotentSubgroup k).inv_mem hg) hinverse

end Conjugation

/-! ### Principal levels in every rank -/

section Algebraic

variable (k : Type u) [Field k] [ValuativeRel k]

omit [ValuativeRel k] in
/-- In rank zero every invertible matrix is the identity. -/
theorem eq_one_of_rank_zero (g : GeneralLinear 0 k) : g = 1 := by
  apply Units.ext
  ext i
  exact Fin.elim0 i

/-- The principal congruence subgroup of level `a` in rank `m`: the image of the kernel of
reduction modulo `𝔪 ^ a` on integral invertible matrices. -/
def rankPrincipalLevel (m a : ℕ) : Subgroup (GeneralLinear m k) :=
  (GeneralLinearGroup.map (n := Fin m)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer ^ a))).ker.map
    (GeneralLinearGroup.map (ValuativeRel.valuation k).integer.subtype)

/-- In positive rank this is the existing principal level subgroup. -/
theorem rankPrincipalLevel_succ (n a : ℕ) :
    rankPrincipalLevel k (n + 1) a = principalLevelSubgroup k n a :=
  rfl

/-- Principal levels consist of integral matrices. -/
theorem rankPrincipalLevel_le_integralRange (m a : ℕ) :
    rankPrincipalLevel k m a ≤ Iwasawa.integralRange (ValuativeRel.valuation k) m :=
  Subgroup.map_le_range _ _

/-- Higher principal levels are smaller. -/
theorem rankPrincipalLevel_antitone (m : ℕ) : Antitone (rankPrincipalLevel k m) := by
  intro a b hab
  cases m with
  | zero =>
    intro g _
    rw [eq_one_of_rank_zero k g]
    exact one_mem _
  | succ n => exact principalLevelSubgroup_antitone k n hab

variable {k}

/-- Integral matrices normalize every principal level. -/
theorem conj_mem_rankPrincipalLevel {m a : ℕ} {γ x : GeneralLinear m k}
    (hγ : γ ∈ Iwasawa.integralRange (ValuativeRel.valuation k) m)
    (hx : x ∈ rankPrincipalLevel k m a) : γ * x * γ⁻¹ ∈ rankPrincipalLevel k m a := by
  obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨γ₀ * x₀ * γ₀⁻¹, (MonoidHom.normal_ker _).conj_mem x₀ hx₀ γ₀, ?_⟩
  simp only [map_mul, map_inv]

theorem conj_mem_rankPrincipalLevel_iff {m a : ℕ} {γ : GeneralLinear m k}
    (hγ : γ ∈ Iwasawa.integralRange (ValuativeRel.valuation k) m) (x : GeneralLinear m k) :
    γ * x * γ⁻¹ ∈ rankPrincipalLevel k m a ↔ x ∈ rankPrincipalLevel k m a := by
  refine ⟨fun h => ?_, conj_mem_rankPrincipalLevel hγ⟩
  have := conj_mem_rankPrincipalLevel (inv_mem hγ) h
  rwa [show γ⁻¹ * (γ * x * γ⁻¹) * γ⁻¹⁻¹ = x by group] at this

omit [ValuativeRel k] in
/-- The torus is additive in the exponent. -/
theorem torus_add {m : ℕ} (ϖ : kˣ) (lam mu : Fin m → ℤ) :
    Iwasawa.torus ϖ (lam + mu) = Iwasawa.torus ϖ lam * Iwasawa.torus ϖ mu := by
  rw [Iwasawa.torus, Iwasawa.torus, Iwasawa.torus, ← map_mul]
  congr 1
  funext i
  simp [zpow_add]

omit [ValuativeRel k] in
theorem torus_zero {m : ℕ} (ϖ : kˣ) : Iwasawa.torus ϖ (0 : Fin m → ℤ) = 1 := by
  rw [Iwasawa.torus, ← map_one Iwasawa.diagonalUnits]
  congr 1
  funext i
  simp

omit [ValuativeRel k] in
/-- Torus elements commute. -/
theorem torus_commute {m : ℕ} (ϖ : kˣ) (lam mu : Fin m → ℤ) :
    Commute (Iwasawa.torus ϖ lam) (Iwasawa.torus ϖ mu) := by
  change _ * _ = _ * _
  rw [← torus_add, ← torus_add, add_comm]

omit [ValuativeRel k] in
/-- The torus element as a block scalar of the singleton shape. -/
theorem torus_eq_blockScalar {n : ℕ} (ϖ : kˣ) (lam : Fin (n + 1) → ℤ) :
    Iwasawa.torus ϖ lam =
      (BlockShape.singletons (n + 1)).blockScalar k (fun i => ϖ ^ lam i) := by
  apply Units.ext
  rw [Iwasawa.torus_val]
  exact (BlockShape.leviEmbedding_singletonLevi_val k (fun i => ϖ ^ lam i)).symm

/-- Antitone exponents give integral forward ratios. -/
theorem ratio_mem_integer {n : ℕ} {ϖ : kˣ} (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) (i j : Fin (n + 1)) (hij : i < j) :
    ((ϖ ^ lam i * (ϖ ^ lam j)⁻¹ : kˣ) : k) ∈ (ValuativeRel.valuation k).integer := by
  rw [← zpow_neg, ← zpow_add, Valuation.mem_integer_iff, Units.val_zpow_eq_zpow_val,
    map_zpow₀]
  exact zpow_le_one₀ (Iwasawa.valuation_pos _ ϖ) hϖ
    (by linarith [hlam hij.le])

/-- **Dominant sandwich.** For a positive principal level and antitone exponents,
`ϖ^lam₁ g ϖ^lam₂ ∈ P (ϖ^lam₁ ϖ^lam₂) P` for every `g` in the principal level `P`. -/
theorem exists_dominant_sandwich {m a : ℕ} (ha : 0 < a) {ϖ : kˣ}
    (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) {lam₁ lam₂ : Fin m → ℤ}
    (h₁ : Antitone lam₁) (h₂ : Antitone lam₂) {g : GeneralLinear m k}
    (hg : g ∈ rankPrincipalLevel k m a) :
    ∃ x ∈ rankPrincipalLevel k m a, ∃ y ∈ rankPrincipalLevel k m a,
      Iwasawa.torus ϖ lam₁ * g * Iwasawa.torus ϖ lam₂ =
        x * (Iwasawa.torus ϖ lam₁ * Iwasawa.torus ϖ lam₂) * y := by
  cases m with
  | zero =>
    refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
    rw [eq_one_of_rank_zero k g]
    group
  | succ n =>
    set S := BlockShape.singletons (n + 1)
    set P := principalLevelSubgroup k n a
    change g ∈ P at hg
    change ∃ x ∈ P, ∃ y ∈ P, _
    obtain ⟨⟨l, d, u⟩, hldu⟩ :=
      BlockShape.principalLevelSubgroup_iwahoriProduct_surjective k n S a ha ⟨g⁻¹, inv_mem hg⟩
    have hval := congrArg Subtype.val hldu
    rw [BlockShape.iwahoriProduct_val] at hval
    have hgeq : g = u.val⁻¹ * d.val⁻¹ * l.val⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, hval, inv_inv]
    obtain ⟨hlP, hlS⟩ := Subgroup.mem_inf.mp l.property
    obtain ⟨hdP, hdS⟩ := Subgroup.mem_inf.mp d.property
    obtain ⟨huP, huS⟩ := Subgroup.mem_inf.mp u.property
    rw [torus_eq_blockScalar, torus_eq_blockScalar]
    set δ₁ := S.blockScalar k (fun i => ϖ ^ lam₁ i)
    set δ₂ := S.blockScalar k (fun i => ϖ ^ lam₂ i)
    -- the Levi factor commutes with the block scalar `δ₁`
    have hcomm : δ₁ * d.val⁻¹ = d.val⁻¹ * δ₁ := by
      obtain ⟨m₀, hm₀⟩ := (S.leviSubgroup k).inv_mem hdS
      rw [← hm₀]
      change S.leviEmbedding k (S.blockScalarLevi k _) * _ =
        _ * S.leviEmbedding k (S.blockScalarLevi k _)
      rw [← map_mul, ← map_mul, S.blockScalarLevi_commute]
    refine ⟨δ₁ * u.val⁻¹ * δ₁⁻¹ * d.val⁻¹, ?_, δ₂⁻¹ * l.val⁻¹ * δ₂, ?_, ?_⟩
    · refine mul_mem ?_ (inv_mem hdP)
      exact principal_upper_conj S _ _ _ (ratio_mem_integer hϖ h₁)
        ((S.unipotentSubgroup k).inv_mem huS) (inv_mem huP)
    · exact principal_lower_inv_conj S _ _ _ (ratio_mem_integer hϖ h₂)
        ((S.oppositeUnipotentSubgroup k).inv_mem hlS) (inv_mem hlP)
    · calc
        δ₁ * g * δ₂ = δ₁ * u.val⁻¹ * δ₁⁻¹ * (δ₁ * d.val⁻¹) * l.val⁻¹ * δ₂ := by
          rw [hgeq]
          group
        _ = δ₁ * u.val⁻¹ * δ₁⁻¹ * (d.val⁻¹ * δ₁) * l.val⁻¹ * δ₂ := by rw [hcomm]
        _ = _ := by group

end Algebraic

/-! ### Topology over a nonarchimedean local field -/

section Topological

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem rank_zero_set_eq_univ (H : Subgroup (GeneralLinear 0 k)) :
    (H : Set (GeneralLinear 0 k)) = Set.univ :=
  Set.eq_univ_of_forall fun g => by
    rw [SetLike.mem_coe, eq_one_of_rank_zero k g]
    exact one_mem _

theorem isOpen_rankPrincipalLevel (m a : ℕ) :
    IsOpen (rankPrincipalLevel k m a : Set (GeneralLinear m k)) := by
  cases m with
  | zero =>
    rw [rank_zero_set_eq_univ]
    exact isOpen_univ
  | succ n => exact (principalLevelOpenSubgroup k n a).isOpen

theorem isCompact_rankPrincipalLevel (m a : ℕ) :
    IsCompact (rankPrincipalLevel k m a : Set (GeneralLinear m k)) := by
  cases m with
  | zero =>
    apply Set.Subsingleton.isCompact
    intro x _ y _
    rw [eq_one_of_rank_zero k x, eq_one_of_rank_zero k y]
  | succ n => exact isCompact_principalLevelOpenSubgroup k n a

theorem isCompact_integralRange (m : ℕ) :
    IsCompact (Iwasawa.integralRange (ValuativeRel.valuation k) m :
      Set (GeneralLinear m k)) := by
  cases m with
  | zero =>
    apply Set.Subsingleton.isCompact
    intro x _ y _
    rw [eq_one_of_rank_zero k x, eq_one_of_rank_zero k y]
  | succ n =>
    have h := isCompact_principalLevelOpenSubgroup k n 0
    change IsCompact (principalLevelSubgroup k n 0 : Set (GeneralLinear (n + 1) k)) at h
    rwa [principalLevelSubgroup_zero] at h

/-- Positive principal levels are cofinal among identity neighborhoods, in every rank. -/
theorem exists_pos_rankPrincipalLevel_subset (m : ℕ) {U : Set (GeneralLinear m k)}
    (hU : U ∈ 𝓝 (1 : GeneralLinear m k)) :
    ∃ a : ℕ, 0 < a ∧ (rankPrincipalLevel k m a : Set (GeneralLinear m k)) ⊆ U := by
  cases m with
  | zero =>
    refine ⟨1, Nat.one_pos, fun g _ => ?_⟩
    rw [eq_one_of_rank_zero k g]
    exact mem_of_mem_nhds hU
  | succ n => exact exists_pos_principalLevelOpenSubgroup_subset k n hU

end Topological

end Langlands.GeneralLinear
