import Langlands.Analysis.Local.ModularCompactAverage
import Langlands.Group.GL.Blocks
import Langlands.Representation.Conductor.Congruence
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-!
# The modular character of a standard block parabolic

Over a nonarchimedean local field, Mathlib's modular character of the standard block
parabolic `P = N ⋊ M` of `GL_(n+1)` is the inflation of any Levi character `δ` that
scales Haar measure on the unipotent radical `N` under Levi conjugation by `δ⁻¹`.
-/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open MeasureTheory Measure Set
open scoped NNReal ENNReal

universe u

section Parts

variable {𝕜 : Type u} [Field 𝕜]
variable {n : ℕ} (B : BlockShape (n + 1))

theorem unipotentPart_val (p : B.parabolic 𝕜) :
    (B.unipotentPart 𝕜 p : B.parabolic 𝕜) =
      p * (B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p))⁻¹ :=
  rfl

theorem unipotentPart_mul_leviInParabolic (p : B.parabolic 𝕜) :
    (B.unipotentPart 𝕜 p : B.parabolic 𝕜) * B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p) = p := by
  rw [unipotentPart_val, inv_mul_cancel_right]

/-- Left translation by the radical preserves the Levi projection. -/
theorem leviProjection_radical_mul (u : B.unipotentRadical 𝕜) (p : B.parabolic 𝕜) :
    B.leviProjection 𝕜 ((u : B.parabolic 𝕜) * p) = B.leviProjection 𝕜 p := by
  rw [map_mul, show B.leviProjection 𝕜 u = 1 from u.property, one_mul]

/-- Left translation by the radical acts on the radical part by left translation. -/
theorem unipotentPart_radical_mul (u : B.unipotentRadical 𝕜) (p : B.parabolic 𝕜) :
    B.unipotentPart 𝕜 ((u : B.parabolic 𝕜) * p) = u * B.unipotentPart 𝕜 p := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, unipotentPart_val, unipotentPart_val, B.leviProjection_radical_mul,
    mul_assoc]

/-- Conjugation by a central Levi element preserves the Levi projection. -/
theorem leviProjection_conj_of_commute (m : B.Levi 𝕜) (hm : ∀ m' : B.Levi 𝕜, m * m' = m' * m)
    (p : B.parabolic 𝕜) :
    B.leviProjection 𝕜 ((B.leviInParabolic 𝕜 m)⁻¹ * p * B.leviInParabolic 𝕜 m) =
      B.leviProjection 𝕜 p := by
  rw [map_mul, map_mul, map_inv, leviProjection_section, mul_assoc, ← hm, inv_mul_cancel_left]

/-- Conjugation by a central Levi element acts on the radical part by the Levi action. -/
theorem unipotentPart_conj_of_commute (m : B.Levi 𝕜) (hm : ∀ m' : B.Levi 𝕜, m * m' = m' * m)
    (p : B.parabolic 𝕜) :
    B.unipotentPart 𝕜 ((B.leviInParabolic 𝕜 m)⁻¹ * p * B.leviInParabolic 𝕜 m) =
      B.leviAction 𝕜 m⁻¹ (B.unipotentPart 𝕜 p) := by
  have hc : B.leviInParabolic 𝕜 m * (B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p))⁻¹ =
      (B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p))⁻¹ * B.leviInParabolic 𝕜 m := by
    rw [← map_inv, ← map_mul, ← map_mul, hm]
  apply Subtype.ext
  rw [leviAction, MonoidHom.comp_apply, MulAut.conjNormal_apply, unipotentPart_val,
    unipotentPart_val, B.leviProjection_conj_of_commute m hm, map_inv (B.leviInParabolic 𝕜) m,
    inv_inv, mul_assoc _ (B.leviInParabolic 𝕜 m), hc]
  simp only [mul_assoc]

end Parts

section Integral

variable {𝕜 : Type u} [Field 𝕜] [ValuativeRel 𝕜]
variable {n : ℕ} (B : BlockShape (n + 1))

/-- A unit `t` making `t` and every `t * f i` integral. -/
theorem exists_unit_valuation_mul_le_one {ι : Type*} [Fintype ι] (f : ι → 𝕜) :
    ∃ t : 𝕜ˣ, ValuativeRel.valuation 𝕜 (t : 𝕜) ≤ 1 ∧
      ∀ i, ValuativeRel.valuation 𝕜 ((t : 𝕜) * f i) ≤ 1 := by
  classical
  let v := ValuativeRel.valuation 𝕜
  have hne (a : 𝕜) (h : ¬ v a ≤ 1) : a ≠ 0 := by
    rintro rfl
    exact h (by simp)
  let c : 𝕜 → 𝕜ˣ := fun a => if h : v a ≤ 1 then 1 else (Units.mk0 a (hne a h))⁻¹
  have hc1 (a : 𝕜) : v (c a : 𝕜) ≤ 1 := by
    simp only [c]
    split_ifs with h
    · simp
    · simp only [Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
      exact inv_le_one_of_one_le₀ (not_le.mp h).le
  have hca (a : 𝕜) : v ((c a : 𝕜) * a) ≤ 1 := by
    simp only [c]
    split_ifs with h
    · simpa using h
    · simp [hne a h]
  refine ⟨∏ i, c (f i), ?_, fun i => ?_⟩
  · rw [Units.coe_prod, map_prod]
    exact Finset.prod_le_one fun i _ => hc1 _
  · rw [Units.coe_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have he : (c (f i) : 𝕜) * (∏ j ∈ Finset.univ.erase i, (c (f j) : 𝕜)) * f i =
        ((c (f i) : 𝕜) * f i) * ∏ j ∈ Finset.univ.erase i, (c (f j) : 𝕜) := by ring
    rw [he, map_mul, map_prod]
    exact mul_le_one' (hca _) (Finset.prod_le_one fun j _ => hc1 _)

/-- The block-scalar Levi element with `t ^ i` on the `i`-th diagonal block. -/
def powBlockScalar : 𝕜ˣ →* B.Levi 𝕜 :=
  MonoidHom.pi fun i => (GeneralLinear.scalar (n := B.size i)).comp (powMonoidHom (i : ℕ))

omit [ValuativeRel 𝕜] in
/-- The block-scalar element is the diagonal matrix with entry `t ^ i` in block `i`. -/
theorem leviEmbedding_powBlockScalar (t : 𝕜ˣ) :
    ((B.leviEmbedding 𝕜 (B.powBlockScalar t) : GeneralLinear (n + 1) 𝕜) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) =
      Matrix.diagonal fun x => ((t ^ ((B.indexEquiv.symm x).1 : ℕ) : 𝕜ˣ) : 𝕜) := by
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding 𝕜 (B.powBlockScalar t) (B.index i a) (B.index j b) = _
  by_cases hij : i = j
  · subst hij
    rw [leviEmbedding_apply_same]
    change (GeneralLinear.scalar (n := B.size i) (t ^ (i : ℕ))).val a b = _
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_pow,
      Matrix.diagonal_apply]
  · rw [B.leviEmbedding_apply_ne 𝕜 _ a b hij, Matrix.diagonal_apply_ne]
    intro h
    exact hij (congrArg Sigma.fst (B.indexEquiv.injective h))

omit [ValuativeRel 𝕜] in
/-- Entries of a matrix conjugated by a block-scalar element. -/
theorem conj_powBlockScalar_apply (t : 𝕜ˣ) (g : GeneralLinear (n + 1) 𝕜) (x y : Fin (n + 1)) :
    ((B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ * g * B.leviEmbedding 𝕜 (B.powBlockScalar t) :
      GeneralLinear (n + 1) 𝕜) x y =
      ((t⁻¹ ^ ((B.indexEquiv.symm x).1 : ℕ) : 𝕜ˣ) : 𝕜) * g x y *
        ((t ^ ((B.indexEquiv.symm y).1 : ℕ) : 𝕜ˣ) : 𝕜) := by
  rw [show (B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ =
      B.leviEmbedding 𝕜 (B.powBlockScalar t⁻¹) by simp only [map_inv]]
  rw [Units.val_mul, Units.val_mul, leviEmbedding_powBlockScalar, leviEmbedding_powBlockScalar,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Conjugating a unipotent radical element by a sufficiently contracting block scalar
makes all of its entries integral. -/
theorem valuation_conj_powBlockScalar_le_one (t : 𝕜ˣ)
    (ht : ValuativeRel.valuation 𝕜 (t : 𝕜) ≤ 1)
    (g : GeneralLinear (n + 1) 𝕜) (hg : g ∈ B.unipotentSubgroup 𝕜)
    (hgt : ∀ x y, ValuativeRel.valuation 𝕜 ((t : 𝕜) * g x y) ≤ 1) (x y : Fin (n + 1)) :
    ValuativeRel.valuation 𝕜
      (((B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ * g * B.leviEmbedding 𝕜 (B.powBlockScalar t) :
        GeneralLinear (n + 1) 𝕜) x y) ≤ 1 := by
  rw [conj_powBlockScalar_apply]
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  simp only [Equiv.symm_apply_apply]
  rw [mem_unipotentSubgroup_iff] at hg
  obtain ⟨hP, hdiag⟩ := hg
  rw [mem_parabolic_iff] at hP
  have ht0 : (t : 𝕜) ≠ 0 := t.ne_zero
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = i + (k + 1) := ⟨j - i - 1, by omega⟩
    set c := g (B.indexEquiv ⟨i, a⟩) (B.indexEquiv ⟨j, b⟩)
    have he : ((t⁻¹ ^ (i : ℕ) : 𝕜ˣ) : 𝕜) * c * ((t ^ (j : ℕ) : 𝕜ˣ) : 𝕜) =
        ((t : 𝕜) * c) * (t : 𝕜) ^ k := by
      rw [hk]
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      have h1 : ((t : 𝕜)⁻¹) ^ (i : ℕ) * (t : 𝕜) ^ (i : ℕ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ ht0, one_pow]
      linear_combination (c * (t : 𝕜) ^ (k + 1)) * h1
    rw [he, map_mul, map_pow]
    exact mul_le_one' (hgt _ _) (pow_le_one' ht k)
  · have hd := hdiag i a b
    change g (B.indexEquiv ⟨i, a⟩) (B.indexEquiv ⟨i, b⟩) = _ at hd
    rw [hd]
    have he : ((t⁻¹ ^ (i : ℕ) : 𝕜ˣ) : 𝕜) * (if a = b then 1 else 0) *
        ((t ^ (i : ℕ) : 𝕜ˣ) : 𝕜) = if a = b then 1 else 0 := by
      rw [mul_right_comm, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one,
        one_mul]
    rw [he]
    split_ifs <;> simp
  · have hz := hP i j a b hji
    change g (B.indexEquiv ⟨i, a⟩) (B.indexEquiv ⟨j, b⟩) = 0 at hz
    rw [hz]
    simp

/-- Membership in the level-zero subgroup is integrality of the entries of the matrix
and of its inverse. -/
theorem mem_levelSubgroup_zero_iff (g : GeneralLinear (n + 1) 𝕜) :
    g ∈ Conductor.levelSubgroup 𝕜 n 0 ↔
      (∀ x y, ValuativeRel.valuation 𝕜 (g x y) ≤ 1) ∧
        ∀ x y, ValuativeRel.valuation 𝕜 (g⁻¹ x y) ≤ 1 := by
  rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
  simp only [Valuation.mem_integer_iff]

/-- Every element of the unipotent radical is conjugated into the level-zero subgroup by
some block scalar. -/
theorem exists_conj_powBlockScalar_mem (g : GeneralLinear (n + 1) 𝕜)
    (hg : g ∈ B.unipotentSubgroup 𝕜) :
    ∃ t : 𝕜ˣ, (B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ * g *
      B.leviEmbedding 𝕜 (B.powBlockScalar t) ∈ Conductor.levelSubgroup 𝕜 n 0 := by
  obtain ⟨t, ht, hft⟩ := exists_unit_valuation_mul_le_one
    (Sum.elim (fun xy : Fin (n + 1) × Fin (n + 1) => g xy.1 xy.2)
      (fun xy : Fin (n + 1) × Fin (n + 1) => g⁻¹ xy.1 xy.2))
  refine ⟨t, (mem_levelSubgroup_zero_iff _).mpr ⟨fun x y => ?_, fun x y => ?_⟩⟩
  · exact B.valuation_conj_powBlockScalar_le_one t ht g hg (fun x y => hft (Sum.inl (x, y))) x y
  · have he : ((B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ * g *
        B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ =
        (B.leviEmbedding 𝕜 (B.powBlockScalar t))⁻¹ * g⁻¹ *
          B.leviEmbedding 𝕜 (B.powBlockScalar t) := by
      group
    rw [he]
    exact B.valuation_conj_powBlockScalar_le_one t ht g⁻¹ (inv_mem hg)
      (fun x y => hft (Sum.inr (x, y))) x y

/-- The block diagonal part of an integral parabolic matrix is integral. -/
theorem leviEmbedding_leviProjection_mem (q : B.parabolic 𝕜)
    (hq : (q : GeneralLinear (n + 1) 𝕜) ∈ Conductor.levelSubgroup 𝕜 n 0) :
    B.leviEmbedding 𝕜 (B.leviProjection 𝕜 q) ∈ Conductor.levelSubgroup 𝕜 n 0 := by
  have hent (r : B.parabolic 𝕜)
      (hr : ∀ x y, ValuativeRel.valuation 𝕜 ((r : GeneralLinear (n + 1) 𝕜) x y) ≤ 1)
      (x y : Fin (n + 1)) :
      ValuativeRel.valuation 𝕜 (B.leviEmbedding 𝕜 (B.leviProjection 𝕜 r) x y) ≤ 1 := by
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    change ValuativeRel.valuation 𝕜
      (B.leviEmbedding 𝕜 (B.leviProjection 𝕜 r) (B.index i a) (B.index j b)) ≤ 1
    by_cases hij : i = j
    · subst hij
      rw [leviEmbedding_apply_same, leviProjection_apply]
      exact hr _ _
    · rw [B.leviEmbedding_apply_ne 𝕜 _ a b hij]
      simp
  rw [mem_levelSubgroup_zero_iff] at hq ⊢
  refine ⟨hent q hq.1, ?_⟩
  rw [← map_inv (B.leviEmbedding 𝕜), ← map_inv (B.leviProjection 𝕜)]
  exact hent q⁻¹ hq.2

/-- A parabolic matrix is integral exactly when its block diagonal part and its unipotent
part are integral. -/
theorem mem_levelSubgroup_iff_parts (q : B.parabolic 𝕜) :
    (q : GeneralLinear (n + 1) 𝕜) ∈ Conductor.levelSubgroup 𝕜 n 0 ↔
      B.leviEmbedding 𝕜 (B.leviProjection 𝕜 q) ∈ Conductor.levelSubgroup 𝕜 n 0 ∧
        ((B.unipotentPart 𝕜 q : B.parabolic 𝕜) : GeneralLinear (n + 1) 𝕜) ∈
          Conductor.levelSubgroup 𝕜 n 0 := by
  have hup : ((B.unipotentPart 𝕜 q : B.parabolic 𝕜) : GeneralLinear (n + 1) 𝕜) =
      (q : GeneralLinear (n + 1) 𝕜) * (B.leviEmbedding 𝕜 (B.leviProjection 𝕜 q))⁻¹ := rfl
  constructor
  · intro hq
    have h1 := B.leviEmbedding_leviProjection_mem q hq
    refine ⟨h1, ?_⟩
    rw [hup]
    exact mul_mem hq (inv_mem h1)
  · rintro ⟨h1, h2⟩
    have hq : (q : GeneralLinear (n + 1) 𝕜) =
        ((B.unipotentPart 𝕜 q : B.parabolic 𝕜) : GeneralLinear (n + 1) 𝕜) *
          B.leviEmbedding 𝕜 (B.leviProjection 𝕜 q) := by
      rw [hup, inv_mul_cancel_right]
    rw [hq]
    exact mul_mem h2 h1

/-- The integral elements of the parabolic, as a subgroup of the parabolic. -/
abbrev integralParabolic : Subgroup (B.parabolic 𝕜) :=
  (Conductor.levelSubgroup 𝕜 n 0).comap (B.parabolic 𝕜).subtype

/-- Parabolic elements whose block diagonal part is integral. -/
def leviIntegral : Set (B.parabolic 𝕜) :=
  {p | B.leviEmbedding 𝕜 (B.leviProjection 𝕜 p) ∈ Conductor.levelSubgroup 𝕜 n 0}

/-- Integral elements of the unipotent radical. -/
def radicalIntegral : Set (B.unipotentRadical 𝕜) :=
  {u | ((u : B.parabolic 𝕜) : GeneralLinear (n + 1) 𝕜) ∈ Conductor.levelSubgroup 𝕜 n 0}

theorem mem_leviIntegral (p : B.parabolic 𝕜) :
    p ∈ B.leviIntegral ↔
      B.leviEmbedding 𝕜 (B.leviProjection 𝕜 p) ∈ Conductor.levelSubgroup 𝕜 n 0 :=
  Iff.rfl

theorem mem_radicalIntegral (u : B.unipotentRadical 𝕜) :
    u ∈ B.radicalIntegral ↔
      ((u : B.parabolic 𝕜) : GeneralLinear (n + 1) 𝕜) ∈ Conductor.levelSubgroup 𝕜 n 0 :=
  Iff.rfl

/-- The integral parabolic is the set of elements with integral Levi part and integral
radical part. -/
theorem coe_integralParabolic :
    (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)) =
      B.leviIntegral ∩ B.unipotentPart 𝕜 ⁻¹' B.radicalIntegral := by
  ext q
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype, mem_inter_iff, mem_preimage,
    mem_leviIntegral, mem_radicalIntegral]
  exact B.mem_levelSubgroup_iff_parts q

/-- The conjugate of the integral parabolic by a central Levi element. -/
theorem conj_preimage_integralParabolic (m : B.Levi 𝕜)
    (hm : ∀ m' : B.Levi 𝕜, m * m' = m' * m) :
    (fun p => (B.leviInParabolic 𝕜 m)⁻¹ * p * B.leviInParabolic 𝕜 m) ⁻¹'
        (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)) =
      B.leviIntegral ∩ B.unipotentPart 𝕜 ⁻¹' (B.leviAction 𝕜 m⁻¹ ⁻¹' B.radicalIntegral) := by
  rw [coe_integralParabolic]
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_leviIntegral,
    B.unipotentPart_conj_of_commute m hm, B.leviProjection_conj_of_commute m hm]

end Integral

section Modular

variable {𝕜 : Type u} [Field 𝕜] [ValuativeRel 𝕜] [TopologicalSpace 𝕜]
  [IsNonarchimedeanLocalField 𝕜]
variable {n : ℕ} (B : BlockShape (n + 1))

theorem continuous_unipotentPart : Continuous (B.unipotentPart 𝕜) :=
  continuous_fst.comp (B.decompositionHomeomorph 𝕜).continuous

/-- Conjugation by a fixed Levi element is continuous on the unipotent radical. -/
theorem continuous_leviAction_apply (m : B.Levi 𝕜) :
    Continuous (fun u : B.unipotentRadical 𝕜 => B.leviAction 𝕜 m u) := by
  have h : Continuous (fun u : B.unipotentRadical 𝕜 =>
      B.leviInParabolic 𝕜 m * (u : B.parabolic 𝕜) * (B.leviInParabolic 𝕜 m)⁻¹) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine continuous_induced_rng.mpr ?_
  convert h using 1
  funext u
  rw [Function.comp_apply, leviAction, MonoidHom.comp_apply, MulAut.conjNormal_apply]

theorem isOpen_integralParabolic : IsOpen (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)) :=
  (Conductor.levelOpenSubgroup 𝕜 n 0).isOpen.preimage continuous_subtype_val

theorem isOpen_leviIntegral : IsOpen (B.leviIntegral (𝕜 := 𝕜)) :=
  (Conductor.levelOpenSubgroup 𝕜 n 0).isOpen.preimage
    ((B.leviEmbeddingContinuous 𝕜).continuous.comp (B.leviProjectionContinuous 𝕜).continuous)

theorem isOpen_radicalIntegral : IsOpen (B.radicalIntegral (𝕜 := 𝕜)) :=
  (Conductor.levelOpenSubgroup 𝕜 n 0).isOpen.preimage
    (continuous_subtype_val.comp continuous_subtype_val)

variable [T2Space 𝕜]

theorem isCompact_integralParabolic :
    IsCompact (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)) :=
  (B.isClosed_parabolic 𝕜).isClosedEmbedding_subtypeVal.isCompact_preimage
    (Conductor.isCompact_levelOpenSubgroup 𝕜 n 0)

variable [SecondCountableTopology (GeneralLinear (n + 1) 𝕜)]
  [LocallyCompactSpace (B.parabolic 𝕜)]

/-- The modular character of the parabolic is trivial on the unipotent radical. -/
theorem modularCharacter_unipotent (u : B.parabolic 𝕜) (hu : u ∈ B.unipotentRadical 𝕜) :
    modularCharacter u = 1 := by
  have : SecondCountableTopology (B.parabolic 𝕜) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨t, ht⟩ := B.exists_conj_powBlockScalar_mem (u : GeneralLinear (n + 1) 𝕜) ⟨u, hu, rfl⟩
  let s : B.parabolic 𝕜 := B.leviInParabolic 𝕜 (B.powBlockScalar t)
  have hmem : s⁻¹ * u * s ∈ B.integralParabolic (𝕜 := 𝕜) := ht
  have hconj : modularCharacter (s⁻¹ * u * s) = modularCharacter u := by
    rw [map_mul, map_mul, mul_right_comm, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [← hconj]
  exact ModularCompactAverage.modularCharacter_eq_one_of_mem _ B.isOpen_integralParabolic
    B.isCompact_integralParabolic hmem

/-- Pushing a Haar measure of the parabolic, restricted to the elements with integral Levi
part, forward to the radical part gives a multiple of Haar measure on the radical. -/
theorem map_unipotentPart_restrict_eq_smul [MeasurableSpace (B.parabolic 𝕜)]
    [BorelSpace (B.parabolic 𝕜)] [MeasurableSpace (B.unipotentRadical 𝕜)]
    [BorelSpace (B.unipotentRadical 𝕜)] (ν : Measure (B.parabolic 𝕜)) [IsHaarMeasure ν]
    (μN : Measure (B.unipotentRadical 𝕜)) [IsHaarMeasure μN] :
    ∃ c : ℝ≥0, (ν.restrict B.leviIntegral).map (B.unipotentPart 𝕜) = c • μN := by
  have : SecondCountableTopology (B.parabolic 𝕜) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (B.unipotentRadical 𝕜) :=
    (B.isClosed_unipotentRadical 𝕜).locallyCompactSpace
  have : SecondCountableTopology (B.unipotentRadical 𝕜) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hup : Continuous (B.unipotentPart 𝕜) := B.continuous_unipotentPart
  have hPO : MeasurableSet (B.leviIntegral (𝕜 := 𝕜)) := B.isOpen_leviIntegral.measurableSet
  have hPO_inv (u : B.unipotentRadical 𝕜) :
      (fun p : B.parabolic 𝕜 => (u : B.parabolic 𝕜) * p) ⁻¹' B.leviIntegral =
        B.leviIntegral := by
    ext p
    rw [mem_preimage, mem_leviIntegral, mem_leviIntegral, B.leviProjection_radical_mul]
  have : IsMulLeftInvariant ((ν.restrict B.leviIntegral).map (B.unipotentPart 𝕜)) := by
    constructor
    intro u
    rw [Measure.map_map (measurable_const_mul u) hup.measurable]
    have hcomp : (fun v => u * v) ∘ B.unipotentPart 𝕜 =
        B.unipotentPart 𝕜 ∘ (fun p => (u : B.parabolic 𝕜) * p) := by
      funext p
      exact (B.unipotentPart_radical_mul u p).symm
    rw [hcomp, ← Measure.map_map hup.measurable (measurable_const_mul (u : B.parabolic 𝕜))]
    congr 1
    have h1 := Measure.restrict_map (μ := ν) (measurable_const_mul (u : B.parabolic 𝕜)) hPO
    rw [map_mul_left_eq_self, hPO_inv u] at h1
    exact h1.symm
  have : IsFiniteMeasureOnCompacts ((ν.restrict B.leviIntegral).map (B.unipotentPart 𝕜)) := by
    refine ⟨fun E hE => ?_⟩
    rw [Measure.map_apply hup.measurable hE.measurableSet,
      Measure.restrict_apply (hup.measurable hE.measurableSet)]
    let S : Set (B.parabolic 𝕜) :=
      (fun pq : B.parabolic 𝕜 × B.parabolic 𝕜 => pq.1 * pq.2) ''
        ((Subtype.val '' E) ×ˢ (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)))
    have hS : IsCompact S :=
      ((hE.image continuous_subtype_val).prod B.isCompact_integralParabolic).image
        continuous_mul
    refine lt_of_le_of_lt (measure_mono ?_) (hS.measure_lt_top (μ := ν))
    rintro p ⟨hpE, hpPO⟩
    have hl : B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p) ∈ B.integralParabolic (𝕜 := 𝕜) := by
      rw [Subgroup.mem_comap, Subgroup.coe_subtype, leviInParabolic_val]
      exact hpPO
    exact ⟨((B.unipotentPart 𝕜 p : B.parabolic 𝕜), B.leviInParabolic 𝕜 (B.leviProjection 𝕜 p)),
      ⟨⟨_, hpE, rfl⟩, hl⟩, B.unipotentPart_mul_leviInParabolic p⟩
  exact ⟨_, isMulLeftInvariant_eq_smul _ μN⟩

/-- For a Levi element commuting with the whole Levi factor, the modular character of the
parabolic is the Haar module `δ` of conjugation on the unipotent radical. -/
theorem modularCharacter_leviInParabolic_of_commute (δ : B.Levi 𝕜 →* ℝ≥0ˣ)
    (hδ : ∀ [MeasurableSpace (B.unipotentRadical 𝕜)] [BorelSpace (B.unipotentRadical 𝕜)]
      (μ : Measure (B.unipotentRadical 𝕜)) [IsHaarMeasure μ] (m : B.Levi 𝕜),
      μ.map (B.leviAction 𝕜 m) = ((δ m : ℝ≥0)⁻¹) • μ)
    (m : B.Levi 𝕜) (hm : ∀ m' : B.Levi 𝕜, m * m' = m' * m) :
    modularCharacter (B.leviInParabolic 𝕜 m) = (δ m : ℝ≥0) := by
  have : SecondCountableTopology (B.parabolic 𝕜) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (B.unipotentRadical 𝕜) :=
    (B.isClosed_unipotentRadical 𝕜).locallyCompactSpace
  let _ : MeasurableSpace (B.parabolic 𝕜) := borel _
  have : BorelSpace (B.parabolic 𝕜) := ⟨rfl⟩
  let _ : MeasurableSpace (B.unipotentRadical 𝕜) := borel _
  have : BorelSpace (B.unipotentRadical 𝕜) := ⟨rfl⟩
  let ν : Measure (B.parabolic 𝕜) := haar
  let μN : Measure (B.unipotentRadical 𝕜) := haar
  have hup : Continuous (B.unipotentPart 𝕜) := B.continuous_unipotentPart
  have hact : Continuous fun u => B.leviAction 𝕜 m⁻¹ u := B.continuous_leviAction_apply m⁻¹
  have hNO : MeasurableSet (B.radicalIntegral (𝕜 := 𝕜)) := B.isOpen_radicalIntegral.measurableSet
  obtain ⟨c, hc⟩ := B.map_unipotentPart_restrict_eq_smul ν μN
  have hρ (E : Set (B.unipotentRadical 𝕜)) (hE : MeasurableSet E) :
      ν (B.leviIntegral ∩ B.unipotentPart 𝕜 ⁻¹' E) = c * μN E := by
    have h := congrArg (fun ρ : Measure (B.unipotentRadical 𝕜) => ρ E) hc
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h
    rw [Measure.map_apply hup.measurable hE, Measure.restrict_apply (hup.measurable hE),
      inter_comm] at h
    exact h
  have e1 : ν (B.integralParabolic (𝕜 := 𝕜) : Set (B.parabolic 𝕜)) =
      c * μN B.radicalIntegral := by
    rw [coe_integralParabolic, hρ _ hNO]
  have e2 := ModularCompactAverage.measure_preimage_conj ν (B.leviInParabolic 𝕜 m)
    B.isOpen_integralParabolic.measurableSet
  rw [B.conj_preimage_integralParabolic m hm, hρ _ (hact.measurable hNO),
    ← Measure.map_apply hact.measurable hNO, hδ μN m⁻¹, Measure.smul_apply,
    nnreal_smul_coe_apply, map_inv δ m, Units.val_inv_eq_inv_val, inv_inv, e1] at e2
  have hpos : (c : ℝ≥0∞) * μN B.radicalIntegral ≠ 0 := by
    rw [← e1]
    exact (B.isOpen_integralParabolic.measure_pos ν ⟨1, one_mem _⟩).ne'
  have hfin : (c : ℝ≥0∞) * μN B.radicalIntegral ≠ ∞ := by
    rw [← e1]
    exact B.isCompact_integralParabolic.measure_lt_top.ne
  have key : ((δ m : ℝ≥0) : ℝ≥0∞) * ((c : ℝ≥0∞) * μN B.radicalIntegral) =
      (modularCharacter (B.leviInParabolic 𝕜 m) : ℝ≥0∞) *
        ((c : ℝ≥0∞) * μN B.radicalIntegral) := by
    rw [← e2]
    ring
  exact (ENNReal.coe_injective ((ENNReal.mul_left_inj hpos hfin).mp key)).symm

/-- The modular character of the parabolic restricted to the Levi factor is `δ`. -/
theorem modularCharacter_leviInParabolic (δ : B.Levi 𝕜 →* ℝ≥0ˣ)
    (hδ : ∀ [MeasurableSpace (B.unipotentRadical 𝕜)] [BorelSpace (B.unipotentRadical 𝕜)]
      (μ : Measure (B.unipotentRadical 𝕜)) [IsHaarMeasure μ] (m : B.Levi 𝕜),
      μ.map (B.leviAction 𝕜 m) = ((δ m : ℝ≥0)⁻¹) • μ)
    (m : B.Levi 𝕜) :
    modularCharacter (B.leviInParabolic 𝕜 m) = (δ m : ℝ≥0) := by
  classical
  have hext : (modularCharacter (G := B.parabolic 𝕜)).comp (B.leviInParabolic 𝕜) =
      (Units.coeHom ℝ≥0).comp δ := by
    refine MonoidHom.pi_ext (ι := Fin B.length) fun j g => ?_
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    let χ : GeneralLinear (B.size j) 𝕜 →* ℝ≥0 :=
      (modularCharacter.comp ((B.leviInParabolic 𝕜).comp (MonoidHom.mulSingle _ j))) *
        (Units.coeHom ℝ≥0).comp (δ.comp (MonoidHom.mulSingle _ j))⁻¹
    have hχ (x : GeneralLinear (B.size j) 𝕜) :
        χ x = modularCharacter (B.leviInParabolic 𝕜 (Pi.mulSingle j x)) *
          ((δ (Pi.mulSingle j x) : ℝ≥0))⁻¹ := by
      simp only [χ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply,
        Units.coeHom_apply, Units.val_inv_eq_inv_val, MonoidHom.mulSingle_apply]
    have hscalar (a : 𝕜ˣ) : χ (Matrix.GeneralLinearGroup.scalar (Fin (B.size j)) a) = 1 := by
      rw [hχ, B.modularCharacter_leviInParabolic_of_commute δ hδ _ ?_,
        mul_inv_cancel₀ (Units.ne_zero _)]
      intro m'
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
        exact Matrix.GeneralLinearGroup.scalar_commute a (m' i)
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hij, one_mul, mul_one]
    have h1 := RankinSelberg.GeneralLinearUnimodularity.character_eq_one χ hscalar g
    rwa [hχ, mul_inv_eq_one₀ (Units.ne_zero _)] at h1
  exact DFunLike.congr_fun hext m

/-- **The modular character of a standard block parabolic.** If `δ` is the Haar module of
Levi conjugation on the unipotent radical, in the sense that every Haar measure `μ` on the
radical satisfies `(Ad m)_* μ = δ(m)⁻¹ μ`, then Mathlib's modular character of the
parabolic is `δ` composed with the Levi projection. -/
theorem modularCharacter_eq (δ : B.Levi 𝕜 →* ℝ≥0ˣ)
    (hδ : ∀ [MeasurableSpace (B.unipotentRadical 𝕜)] [BorelSpace (B.unipotentRadical 𝕜)]
      (μ : Measure (B.unipotentRadical 𝕜)) [IsHaarMeasure μ] (m : B.Levi 𝕜),
      μ.map (B.leviAction 𝕜 m) = ((δ m : ℝ≥0)⁻¹) • μ)
    (q : B.parabolic 𝕜) :
    modularCharacter q = (δ (B.leviProjection 𝕜 q) : ℝ≥0) := by
  have hq : (B.unipotentPart 𝕜 q : B.parabolic 𝕜) *
      B.leviInParabolic 𝕜 (B.leviProjection 𝕜 q) = q := inv_mul_cancel_right q _
  calc modularCharacter q
      = modularCharacter ((B.unipotentPart 𝕜 q : B.parabolic 𝕜) *
          B.leviInParabolic 𝕜 (B.leviProjection 𝕜 q)) := by rw [hq]
    _ = (δ (B.leviProjection 𝕜 q) : ℝ≥0) := by
      rw [map_mul, B.modularCharacter_unipotent _ (B.unipotentPart 𝕜 q).property, one_mul,
        B.modularCharacter_leviInParabolic δ hδ]

end Modular

end Langlands.GeneralLinear.BlockShape
