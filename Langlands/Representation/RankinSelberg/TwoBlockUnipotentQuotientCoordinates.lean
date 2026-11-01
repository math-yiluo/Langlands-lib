import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# Radical coordinates on the upper-unipotent group and Haar transport

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, every upper
unipotent matrix factors uniquely as `n = b u(x)` with `b` in the block-diagonal unipotent
subgroup `H` and `u(x)` the complementary upper radical. This module proves that the
coordinates `(b, x) ↦ b u(x)` form a homeomorphism `H × R ≃ₜ N`, that they carry the
product of a left-invariant measure on `H` of mass one on its integral points and any
rectangular additive Haar measure `μR` to `c • unipotentHaar`, where `c` is the `μR`-mass
of the integral rectangle, and that the transported block Haar measure gives mass one to
the integral points of `H`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration

open MeasureTheory Measure GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockUnipotentQuotient
open scoped ENNReal NNReal

universe uK

section Algebra

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {K : Type uK} [Field K]

/-- The radical coordinate `n₀⁻¹ β` of an upper unipotent matrix with diagonal blocks
`n₀, n₁` and upper-right block `β`: the published shift `unipotentShift` at `x = 0`. -/
def radicalCoord (n : upperUnipotent (t + 1) K) : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K :=
  unipotentShift h n 0

/-- The block-diagonal part `diag(n₀, n₁) ∈ H` of an upper unipotent matrix. -/
def blockPart (n : upperUnipotent (t + 1) K) : blockUnipotent h K :=
  blockUnipotentEquiv h K (fun i => ⟨unipotentLevi h n i, unipotentLevi_mem h n i⟩)

theorem blockPart_val (n : upperUnipotent (t + 1) K) :
    (blockPart h n).val = (succBlockShape m h).leviEmbedding K (unipotentLevi h n) :=
  rfl

/-- The factorization `n = diag(n₀, n₁) u(n₀⁻¹ β)`. -/
theorem blockPart_mul_upperRadical (n : upperUnipotent (t + 1) K) :
    (blockPart h n).val * upperRadical h K (radicalCoord h n) = n.val := by
  have e := upperRadical_mul_upperUnipotent h
    (0 : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) n
  rw [upperRadical_zero, one_mul] at e
  exact e.symm

/-- The radical meets `H` only in the identity. -/
theorem upperRadical_mem_blockUnipotent_iff (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    upperRadical h K x ∈ blockUnipotent h K ↔ x = 0 := by
  constructor
  · intro hx
    ext a b
    have e := ((mem_blockUnipotent_iff_corner h K _).mp hx).2 a b
    rwa [upperRadical_index_zero_one] at e
  · rintro rfl
    rw [upperRadical_zero]
    exact one_mem _

/-- The coordinates `(b, x) ↦ b u(x)` of the upper unipotent group. -/
def coordinates (p : blockUnipotent h K × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    upperUnipotent (t + 1) K :=
  ⟨p.1.val * upperRadical h K p.2,
    mul_mem (blockUnipotent_le_upperUnipotent h K p.1.property)
      (upperRadical_mem_upperUnipotent h K p.2)⟩

@[simp]
theorem coordinates_val (b : blockUnipotent h K) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    (coordinates h (b, x)).val = b.val * upperRadical h K x :=
  rfl

theorem coordinates_injective : Function.Injective (coordinates (K := K) h) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ hab
  have hv : a.val * upperRadical h K x = b.val * upperRadical h K y := congrArg Subtype.val hab
  have hxy : upperRadical h K (x - y) ∈ blockUnipotent h K := by
    rw [upperRadical_sub]
    have e : upperRadical h K x * (upperRadical h K y)⁻¹ = a.val⁻¹ * b.val := by
      calc upperRadical h K x * (upperRadical h K y)⁻¹
          = a.val⁻¹ * (a.val * upperRadical h K x) * (upperRadical h K y)⁻¹ := by
            rw [inv_mul_cancel_left]
        _ = a.val⁻¹ * b.val := by rw [hv, mul_assoc, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (inv_mem a.property) b.property
  rw [upperRadical_mem_blockUnipotent_iff, sub_eq_zero] at hxy
  subst hxy
  exact Prod.ext (Subtype.ext (mul_right_cancel hv)) rfl

theorem coordinates_blockPart_radicalCoord (n : upperUnipotent (t + 1) K) :
    coordinates h (blockPart h n, radicalCoord h n) = n :=
  Subtype.ext (blockPart_mul_upperRadical h n)

/-- The coordinates as an equivalence `H × R ≃ N`. -/
def coordinatesEquiv :
    blockUnipotent h K × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K ≃ upperUnipotent (t + 1) K where
  toFun := coordinates h
  invFun n := (blockPart h n, radicalCoord h n)
  left_inv p := coordinates_injective h (coordinates_blockPart_radicalCoord h (coordinates h p))
  right_inv := coordinates_blockPart_radicalCoord h

@[simp]
theorem radicalCoord_coordinates (b : blockUnipotent h K)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    radicalCoord h (coordinates h (b, x)) = x :=
  congrArg Prod.snd ((coordinatesEquiv h).left_inv (b, x))

/-- The diagonal blocks of an element of `H` recover it. -/
theorem leviEmbedding_unipotentLevi (b : blockUnipotent h K) :
    (succBlockShape m h).leviEmbedding K
        (unipotentLevi h ⟨b.val, blockUnipotent_le_upperUnipotent h K b.property⟩) = b.val := by
  obtain ⟨_, nb, rfl⟩ := b
  change (succBlockShape m h).leviEmbedding K _ =
    (succBlockShape m h).leviEmbedding K (fun i => (nb i).val)
  congr 1
  funext i
  exact unipotentLevi_blockEmbedding h K nb i

/-- Left multiplication in coordinates: `n b u(x) = (diag(n₀, n₁) b) u(s + x)`, where `s` is
the shift of the radical coordinate of `n` by `b`. -/
theorem mul_coordinates (n : upperUnipotent (t + 1) K) (b : blockUnipotent h K)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    n * coordinates h (b, x) =
      coordinates h (blockPart h n * b,
        unipotentShift h ⟨b.val, blockUnipotent_le_upperUnipotent h K b.property⟩
          (radicalCoord h n) + x) := by
  apply Subtype.ext
  have hb := upperRadical_mul_upperUnipotent h (radicalCoord h n)
    ⟨b.val, blockUnipotent_le_upperUnipotent h K b.property⟩
  rw [leviEmbedding_unipotentLevi] at hb
  change n.val * (b.val * upperRadical h K x) =
    ((blockPart h n).val * b.val) * upperRadical h K
      (unipotentShift h ⟨b.val, blockUnipotent_le_upperUnipotent h K b.property⟩
        (radicalCoord h n) + x)
  calc n.val * (b.val * upperRadical h K x)
      = (blockPart h n).val * (upperRadical h K (radicalCoord h n) * b.val) *
          upperRadical h K x := by
        rw [← blockPart_mul_upperRadical h n]
        simp only [mul_assoc]
    _ = _ := by
        rw [hb, upperRadical_add]
        simp only [mul_assoc]

end Algebra

section Topology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {K : Type uK} [Field K]
  [TopologicalSpace K] [IsTopologicalRing K]

omit [IsTopologicalRing K] in
theorem continuous_unipotentCorner :
    Continuous (fun n : upperUnipotent (t + 1) K => unipotentCorner h n) :=
  continuous_pi fun _ => continuous_pi fun _ =>
    (GeneralLinear.entry (R := K) _ _).continuous.comp continuous_subtype_val

theorem continuous_unipotentLevi_inv_zero :
    Continuous fun n : upperUnipotent (t + 1) K =>
      ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) K).val :=
  Units.continuous_coe_inv.comp
    ((continuous_apply (0 : Fin 2)).comp (continuous_unipotentLevi h K))

theorem continuous_unipotentLevi_one :
    Continuous fun n : upperUnipotent (t + 1) K =>
      (unipotentLevi h n 1).val :=
  Units.continuous_val.comp ((continuous_apply (1 : Fin 2)).comp (continuous_unipotentLevi h K))

/-- The shift `(n, x) ↦ n₀⁻¹ (β + x n₁)` is jointly continuous. -/
theorem continuous_unipotentShift :
    Continuous (fun p : upperUnipotent (t + 1) K × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K =>
      unipotentShift h p.1 p.2) :=
  ((continuous_unipotentLevi_inv_zero h).comp continuous_fst).matrix_mul
    (((continuous_unipotentCorner h).comp continuous_fst).add
      (continuous_snd.matrix_mul ((continuous_unipotentLevi_one h).comp continuous_fst)))

/-- For a fixed radical coordinate `y`, the shift `n ↦ n₀⁻¹ (β + y n₁)` is continuous along
any continuous family of upper unipotent matrices. -/
theorem continuous_unipotentShift_left (y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)
    {X : Type*} [TopologicalSpace X] {f : X → upperUnipotent (t + 1) K} (hf : Continuous f) :
    Continuous fun x => unipotentShift h (f x) y :=
  ((continuous_unipotentLevi_inv_zero h).comp hf).matrix_mul
    (((continuous_unipotentCorner h).comp hf).add
      ((continuous_const (y := y)).matrix_mul ((continuous_unipotentLevi_one h).comp hf)))

theorem continuous_radicalCoord :
    Continuous (fun n : upperUnipotent (t + 1) K => radicalCoord h n) :=
  (continuous_unipotentLevi_inv_zero h).matrix_mul
    ((continuous_unipotentCorner h).add
      ((continuous_const (y := (0 : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K))).matrix_mul
        (continuous_unipotentLevi_one h)))

theorem continuous_blockPart :
    Continuous (fun n : upperUnipotent (t + 1) K => blockPart h n) :=
  (blockUnipotentHomeomorph h K).continuous.comp
    (continuous_pi fun i => ((continuous_apply i).comp (continuous_unipotentLevi h K)).subtype_mk _)

theorem continuous_coordinates : Continuous (coordinates (K := K) h) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    ((continuous_upperRadical h K).comp continuous_snd)).subtype_mk _

/-- The coordinates as a homeomorphism `H × R ≃ₜ N`. -/
def coordinatesHomeomorph :
    blockUnipotent h K × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K ≃ₜ upperUnipotent (t + 1) K where
  toEquiv := coordinatesEquiv h
  continuous_toFun := continuous_coordinates h
  continuous_invFun := (continuous_blockPart h).prodMk (continuous_radicalCoord h)

@[simp]
theorem coordinatesHomeomorph_apply
    (p : blockUnipotent h K × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    coordinatesHomeomorph h p = coordinates h p :=
  rfl

end Topology

section Integral

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) {K : Type uK} [Field K]

/-- A property of all pairs of coordinates is checked on the four blocks. -/
theorem forall_index (P : Fin (t + 1) → Fin (t + 1) → Prop)
    (h00 : ∀ (a b : Fin (m 0 + 1)), P ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 0 b))
    (h01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)), P ((succBlockShape m h).index 0 a)
      ((succBlockShape m h).index 1 b))
    (h10 : ∀ (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)), P ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 0 b))
    (h11 : ∀ (a b : Fin (m 1 + 1)), P ((succBlockShape m h).index 1 a)
      ((succBlockShape m h).index 1 b)) :
    ∀ k l, P k l := by
  intro k l
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
  change P ((succBlockShape m h).index i a) ((succBlockShape m h).index j b)
  match i, a, j, b with
  | 0, a, 0, b => exact h00 a b
  | 0, a, 1, b => exact h01 a b
  | 1, a, 0, b => exact h10 a b
  | 1, a, 1, b => exact h11 a b

theorem mem_blockUnipotent_index_zero_one {g : GeneralLinear (t + 1) K}
    (hg : g ∈ blockUnipotent h K) (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)) :
    g ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) = 0 :=
  ((mem_blockUnipotent_iff_corner h K g).mp hg).2 a b

theorem mem_blockUnipotent_index_one_zero {g : GeneralLinear (t + 1) K}
    (hg : g ∈ blockUnipotent h K) (a : Fin (m 1 + 1)) (b : Fin (m 0 + 1)) :
    g ((succBlockShape m h).index 1 a) ((succBlockShape m h).index 0 b) = 0 :=
  upperUnipotent_index_one_zero h ⟨g, blockUnipotent_le_upperUnipotent h K hg⟩ a b

/-- Right multiplication by the radical does not change the diagonal blocks of `g ∈ H`. -/
theorem mul_upperRadical_index_same {g : GeneralLinear (t + 1) K}
    (hg : g ∈ blockUnipotent h K) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    ∀ (i : Fin 2) (a b : Fin (m i + 1)),
      (g * upperRadical h K x) ((succBlockShape m h).index i a)
          ((succBlockShape m h).index i b) =
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
  | 0, a, b => by
      rw [mul_apply_index h, sum_mul_radical_zero_zero, sum_mul_radical_one_zero, add_zero]
  | 1, a, b => by
      rw [mul_apply_index h, sum_mul_radical_one_one, sum_mul_radical_zero_one,
        Finset.sum_eq_zero (fun c _ => by rw [mem_blockUnipotent_index_one_zero h hg, zero_mul]),
        zero_add]

/-- Left multiplication by the radical does not change the diagonal blocks of `g ∈ H`. -/
theorem upperRadical_mul_index_same {g : GeneralLinear (t + 1) K}
    (hg : g ∈ blockUnipotent h K) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    ∀ (i : Fin 2) (a b : Fin (m i + 1)),
      (upperRadical h K x * g) ((succBlockShape m h).index i a)
          ((succBlockShape m h).index i b) =
        g ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
  | 0, a, b => by
      rw [mul_apply_index h, sum_radical_zero_zero_mul, sum_radical_zero_one_mul,
        Finset.sum_eq_zero (fun c _ => by rw [mem_blockUnipotent_index_one_zero h hg, mul_zero]),
        add_zero]
  | 1, a, b => by
      rw [mul_apply_index h, sum_radical_one_zero_mul, sum_radical_one_one_mul, zero_add]

variable [ValuativeRel K]

local notation "O" => Valuation.integer (ValuativeRel.valuation K)

theorem upperRadical_mem_integralSubgroup_iff
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    upperRadical h K x ∈ Conductor.integralSubgroup O t ↔ ∀ a b, x a b ∈ O := by
  have key : ∀ y : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K, (∀ a b, y a b ∈ O) →
      ∀ k l, upperRadical h K y k l ∈ O := by
    intro y hy
    apply forall_index h (fun k l => upperRadical h K y k l ∈ O)
    · intro a b
      rw [upperRadical_index_zero_zero]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · intro a b
      rw [upperRadical_index_zero_one]
      exact hy a b
    · intro a b
      rw [upperRadical_index_one_zero]
      exact zero_mem _
    · intro a b
      rw [upperRadical_index_one_one]
      split_ifs
      exacts [one_mem _, zero_mem _]
  rw [Conductor.mem_integralSubgroup]
  constructor
  · rintro ⟨h1, -⟩ a b
    have e := h1 ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b)
    rwa [upperRadical_index_zero_one] at e
  · intro hx
    refine ⟨key x hx, ?_⟩
    rw [← upperRadical_neg]
    exact key (-x) fun a b => by
      rw [Matrix.neg_apply]
      exact neg_mem (hx a b)

/-- If `g u(x)` is integral for `g ∈ H`, then so is `g`. -/
theorem mem_integralSubgroup_of_mul_upperRadical {g : GeneralLinear (t + 1) K}
    (hg : g ∈ blockUnipotent h K) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K)
    (hgx : g * upperRadical h K x ∈ Conductor.integralSubgroup O t) :
    g ∈ Conductor.integralSubgroup O t := by
  rw [Conductor.mem_integralSubgroup] at hgx ⊢
  obtain ⟨h1, h2⟩ := hgx
  have hg' : g⁻¹ ∈ blockUnipotent h K := inv_mem hg
  have hinv : (g * upperRadical h K x)⁻¹ = upperRadical h K (-x) * g⁻¹ := by
    rw [mul_inv_rev, upperRadical_neg]
  constructor
  · apply forall_index h (fun k l => g k l ∈ O)
    · intro a b
      rw [← mul_upperRadical_index_same h hg x 0]
      exact h1 _ _
    · intro a b
      rw [mem_blockUnipotent_index_zero_one h hg]
      exact zero_mem _
    · intro a b
      rw [mem_blockUnipotent_index_one_zero h hg]
      exact zero_mem _
    · intro a b
      rw [← mul_upperRadical_index_same h hg x 1]
      exact h1 _ _
  · apply forall_index h (fun k l => g⁻¹ k l ∈ O)
    · intro a b
      rw [← upperRadical_mul_index_same h hg' (-x) 0, ← hinv]
      exact h2 _ _
    · intro a b
      rw [mem_blockUnipotent_index_zero_one h hg']
      exact zero_mem _
    · intro a b
      rw [mem_blockUnipotent_index_one_zero h hg']
      exact zero_mem _
    · intro a b
      rw [← upperRadical_mul_index_same h hg' (-x) 1, ← hinv]
      exact h2 _ _

/-- `b u(x)` is integral exactly when `b` and `x` are. -/
theorem coordinates_mem_integralSubgroup_iff (b : blockUnipotent h K)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) K) :
    (coordinates h (b, x)).val ∈ Conductor.integralSubgroup O t ↔
      b.val ∈ Conductor.integralSubgroup O t ∧ ∀ a c, x a c ∈ O := by
  rw [coordinates_val]
  constructor
  · intro hbx
    have hb := mem_integralSubgroup_of_mul_upperRadical h b.property x hbx
    refine ⟨hb, (upperRadical_mem_integralSubgroup_iff h x).mp ?_⟩
    have e : upperRadical h K x = b.val⁻¹ * (b.val * upperRadical h K x) := by
      rw [inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hb) hbx
  · rintro ⟨hb, hx⟩
    exact mul_mem hb ((upperRadical_mem_integralSubgroup_iff h x).mpr hx)

/-- `diag(n₀, n₁)` is integral exactly when each block is. -/
theorem blockEmbedding_mem_integralSubgroup_iff (n : BlockUnipotents m K) :
    blockEmbedding h K n ∈ Conductor.integralSubgroup O t ↔
      ∀ i, (n i).val ∈ Conductor.integralSubgroup O (m i) := by
  have hinv : (blockEmbedding h K n)⁻¹ = blockEmbedding h K n⁻¹ := (map_inv _ n).symm
  simp_rw [Conductor.mem_integralSubgroup]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← blockEmbedding_index_same h K n i a b]
      exact h1 _ _
    · have e := blockEmbedding_index_same h K n⁻¹ i a b
      rw [← hinv] at e
      convert h2 ((succBlockShape m h).index i a) ((succBlockShape m h).index i b) using 1
      exact e.symm
  · intro hn
    have key : ∀ n' : BlockUnipotents m K, (∀ i a b, (n' i).val a b ∈ O) →
        ∀ k l, blockEmbedding h K n' k l ∈ O := by
      intro n' hn'
      apply forall_index h (fun k l => blockEmbedding h K n' k l ∈ O)
      · intro a b
        rw [blockEmbedding_index_same]
        exact hn' 0 a b
      · intro a b
        rw [blockEmbedding_index_zero_one]
        exact zero_mem _
      · intro a b
        rw [blockEmbedding_index_one_zero]
        exact zero_mem _
      · intro a b
        rw [blockEmbedding_index_same]
        exact hn' 1 a b
    refine ⟨key n fun i a b => (hn i).1 a b, ?_⟩
    rw [hinv]
    exact key n⁻¹ fun i a b => (hn i).2 a b

end Integral

section Transport

variable (F : Type uK) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  [MeasurableSpace (blockUnipotent h F)] [BorelSpace (blockUnipotent h F)]
  [MeasurableSpace (upperUnipotent (t + 1) F)] [BorelSpace (upperUnipotent (t + 1) F)]

local notation "O" => Valuation.integer (ValuativeRel.valuation F)

omit [T2Space F] in
/-- Left translation by `n ∈ N` acts on coordinates by the skew product
`(b, x) ↦ (diag(n₀, n₁) b, s_b + x)`, a left translation of `H` followed by fiberwise
translations of `R`. Hence the transported product measure is left invariant. -/
theorem isMulLeftInvariant_map_coordinates (μH : Measure (blockUnipotent h F))
    [μH.IsMulLeftInvariant] [SFinite μH]
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μR.IsAddLeftInvariant]
    [SFinite μR] :
    (Measure.map (coordinates h) (μH.prod μR)).IsMulLeftInvariant := by
  have : SecondCountableTopology (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  refine ⟨fun n => ?_⟩
  have hΦ : Measurable (coordinates (K := F) h) := (continuous_coordinates h).measurable
  have hb : Continuous fun b : blockUnipotent h F =>
      (⟨b.val, blockUnipotent_le_upperUnipotent h F b.property⟩ : upperUnipotent (t + 1) F) :=
    continuous_subtype_val.subtype_mk _
  have hS : MeasurePreserving
      (fun p : blockUnipotent h F × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F =>
        (blockPart h n * p.1, unipotentShift h
          ⟨p.1.val, blockUnipotent_le_upperUnipotent h F p.1.property⟩ (radicalCoord h n) + p.2))
      (μH.prod μR) (μH.prod μR) :=
    (measurePreserving_mul_left μH (blockPart h n)).skew_product
      (g := fun b x => unipotentShift h
          ⟨b.val, blockUnipotent_le_upperUnipotent h F b.property⟩ (radicalCoord h n) + x)
      ((continuous_unipotentShift_left h (radicalCoord h n) (hb.comp continuous_fst)).add
        continuous_snd).measurable
      (Filter.Eventually.of_forall fun _ => map_add_left_eq_self μR _)
  rw [Measure.map_map (measurable_const_mul n) hΦ]
  have he : (fun x => n * x) ∘ coordinates h =
      coordinates h ∘ (fun p : blockUnipotent h F × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F =>
        (blockPart h n * p.1, unipotentShift h
          ⟨p.1.val, blockUnipotent_le_upperUnipotent h F p.1.property⟩ (radicalCoord h n) + p.2)) :=
    funext fun p => mul_coordinates h n p.1 p.2
  rw [he, ← Measure.map_map hΦ hS.measurable, hS.map_eq]

omit [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (blockUnipotent h F)] [BorelSpace (blockUnipotent h F)]
  [MeasurableSpace (upperUnipotent (t + 1) F)] [BorelSpace (upperUnipotent (t + 1) F)] in
/-- The preimage of the integral points of `N` under the coordinates is the product of the
integral points of `H` and the integral rectangle. -/
theorem coordinates_preimage_unipotentIntegralOpen :
    coordinates h ⁻¹' (unipotentIntegralOpen F t : Set (upperUnipotent (t + 1) F)) =
      {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} ×ˢ
        {x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F | ∀ a c, x a c ∈ O} := by
  ext ⟨b, x⟩
  change (coordinates h (b, x)).val ∈ Conductor.levelSubgroup F t 0 ↔ _
  rw [Conductor.levelSubgroup_zero, coordinates_mem_integralSubgroup_iff]
  rfl

/-- **Coordinate transport.** For a left-invariant s-finite measure `μH` on `H`, finite on
compacts and of mass one on the integral points, and any additive Haar measure `μR` on the
rectangular matrices, the coordinates `(b, x) ↦ b u(x)` carry `μH × μR` to
`c • unipotentHaar`, where `c` is the `μR`-mass of the integral rectangle. -/
theorem map_coordinates_prod [SecondCountableTopology (upperUnipotent (t + 1) F)]
    (μH : Measure (blockUnipotent h F)) [μH.IsMulLeftInvariant] [SFinite μH]
    [IsFiniteMeasureOnCompacts μH]
    (hμH : μH {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} = 1)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μR.IsAddHaarMeasure] :
    Measure.map (coordinates h) (μH.prod μR) =
      μR {x | ∀ a c, x a c ∈ O} • unipotentHaar F t := by
  have : SecondCountableTopology (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → F))
  have : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  have : LocallyCompactSpace (upperUnipotent (t + 1) F) := UpperUnipotent.locallyCompactSpace
  have hΦ : Measurable (coordinates (K := F) h) := (continuous_coordinates h).measurable
  have : IsFiniteMeasureOnCompacts (Measure.map (coordinates h) (μH.prod μR)) :=
    Measure.IsFiniteMeasureOnCompacts.map (μH.prod μR) (coordinatesHomeomorph h)
  have := isMulLeftInvariant_map_coordinates F h μH μR
  have key := Measure.isMulLeftInvariant_eq_smul
    (Measure.map (coordinates h) (μH.prod μR)) (unipotentHaar F t)
  have hU : MeasurableSet (unipotentIntegralOpen F t : Set (upperUnipotent (t + 1) F)) :=
    (unipotentIntegralOpen F t).isOpen.measurableSet
  have hc := DFunLike.congr_fun key (unipotentIntegralOpen F t : Set (upperUnipotent (t + 1) F))
  rw [Measure.map_apply hΦ hU, coordinates_preimage_unipotentIntegralOpen, Measure.prod_prod,
    hμH, one_mul, Measure.coe_nnreal_smul_apply, unipotentHaar_integral, mul_one] at hc
  rw [hc, Measure.coe_nnreal_smul]
  exact key

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (upperUnipotent (t + 1) F)] [BorelSpace (upperUnipotent (t + 1) F)] in
/-- The fixed block measure, the transport of the product of the two normalized block
unipotent Haar measures, gives mass one to the integral points of `H`. -/
theorem blockMeasure_integral
    [∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F)]
    [∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F)]
    [∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F)] :
    Measure.map (blockUnipotentEquiv h F) (Measure.pi fun i : Fin 2 => unipotentHaar F (m i))
      {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} = 1 := by
  have : ∀ i : Fin 2, LocallyCompactSpace (upperUnipotent (m i + 1) F) := fun i => by
    have : LocallyCompactSpace (Matrix (Fin (m i + 1)) (Fin (m i + 1)) F) :=
      inferInstanceAs (LocallyCompactSpace (Fin (m i + 1) → Fin (m i + 1) → F))
    exact UpperUnipotent.locallyCompactSpace
  have hmeas : Measurable (blockUnipotentEquiv h F) :=
    (blockUnipotentHomeomorph h F).continuous.measurable
  have hS : MeasurableSet {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} := by
    have ho : IsOpen {b : blockUnipotent h F | b.val ∈ Conductor.levelOpenSubgroup F t 0} :=
      (Conductor.levelOpenSubgroup F t 0).isOpen.preimage continuous_subtype_val
    rw [← Conductor.levelSubgroup_zero]
    exact ho.measurableSet
  rw [Measure.map_apply hmeas hS]
  have hpre : (blockUnipotentEquiv h F) ⁻¹'
      {b : blockUnipotent h F | b.val ∈ Conductor.integralSubgroup O t} =
        Set.univ.pi fun i => (unipotentIntegralOpen F (m i) : Set (upperUnipotent (m i + 1) F)) := by
    ext n
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      blockUnipotentEquiv_apply_val]
    rw [blockEmbedding_mem_integralSubgroup_iff]
    refine forall_congr' fun i => ?_
    change _ ↔ (n i).val ∈ Conductor.levelSubgroup F (m i) 0
    rw [Conductor.levelSubgroup_zero]
  rw [hpre, Measure.pi_pi]
  simp [unipotentHaar_integral]

end Transport

end Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration
