import Langlands.Representation.Archimedean.RealCartanFixedFlag
import Langlands.Representation.Archimedean.RealSignedOrthogonalDifferential

/-! # Support of the real Cartan compact column -/

noncomputable section

open Matrix Filter
open scoped Matrix.Norms.Operator Topology

namespace Langlands.Archimedean.RealCartanCompactSupport

open PrincipalSeriesExtension RealSignedOrthogonalDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Placement

variable {ι α β : Type*} [Finite ι]

/-- The coordinate fiber of a block label. -/
abbrev BlockFiber (a : ι → α) (x : α) := {i : ι // a i = x}

/-- The labels of the two-coordinate blocks. -/
abbrev PairBlock (a : ι → α) := {x : α // Nat.card (BlockFiber a x) = 2}

private theorem card_fiber_le {a : ι → α} {b : ι → β} {f : α → β}
    {π : Equiv.Perm ι} (h : ∀ i, b (π i) = f (a i)) (x : α) :
    Nat.card (BlockFiber a x) ≤ Nat.card (BlockFiber b (f x)) := by
  let map : BlockFiber a x → BlockFiber b (f x) :=
    fun i => ⟨π i.1, (h i.1).trans (congrArg f i.2)⟩
  exact Nat.card_le_card_of_injective map fun i j he =>
    Subtype.ext (π.injective (congrArg Subtype.val he))

private theorem card_fiber_add_le_of_eq {a : ι → α} {b : ι → β} {f : α → β}
    {π : Equiv.Perm ι} (h : ∀ i, b (π i) = f (a i))
    {x z : α} (hxz : x ≠ z) (hf : f x = f z) :
    Nat.card (BlockFiber a x) + Nat.card (BlockFiber a z) ≤ Nat.card (BlockFiber b (f x)) := by
  let map : BlockFiber a x ⊕ BlockFiber a z → BlockFiber b (f x) :=
    Sum.elim
      (fun i => ⟨π i.1, (h i.1).trans (congrArg f i.2)⟩)
      (fun j => ⟨π j.1, (h j.1).trans ((congrArg f j.2).trans hf.symm)⟩)
  rw [← Nat.card_sum]
  apply Nat.card_le_card_of_injective map
  intro i j hmap
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij : i.val = j.val := π.injective (congrArg Subtype.val hmap)
      exact congrArg Sum.inl (Subtype.ext hij)
    | inr j =>
      have hij : i.val = j.val := π.injective (congrArg Subtype.val hmap)
      exact (hxz (i.2.symm.trans ((congrArg a hij).trans j.2))).elim
  | inr i =>
    cases j with
    | inl j =>
      have hij : i.val = j.val := π.injective (congrArg Subtype.val hmap)
      exact (hxz (j.2.symm.trans ((congrArg a hij.symm).trans i.2))).elim
    | inr j =>
      have hij : i.val = j.val := π.injective (congrArg Subtype.val hmap)
      exact congrArg Sum.inr (Subtype.ext hij)

/-- When a permutation places each source block in a single target block of
size at most two, the number of source pairs is bounded by the number of
target pairs. Equality makes the induced block assignment a size-preserving
bijection. -/
theorem pairBlock_le_of_placement [Finite β]
    {a : ι → α} {b : ι → β} {π : Equiv.Perm ι}
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hbsize : ∀ x, Nat.card (BlockFiber b x) ≤ 2)
    (hπ : ∀ i j, a i = a j → b (π i) = b (π j)) :
    Nat.card (PairBlock a) ≤ Nat.card (PairBlock b) ∧
      (Nat.card (PairBlock a) = Nat.card (PairBlock b) →
        ∃ e : α ≃ β, (∀ i, b (π i) = e (a i)) ∧
          ∀ x, Nat.card (BlockFiber a x) = Nat.card (BlockFiber b (e x))) := by
  let f (x : α) : β := b (π (ha x).choose)
  have h (i : ι) : b (π i) = f (a i) :=
    hπ i (ha (a i)).choose ((ha (a i)).choose_spec.symm)
  have hn (x : α) : 0 < Nat.card (BlockFiber a x) := by
    obtain ⟨i, hi⟩ := ha x
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i, hi⟩⟩, inferInstance⟩
  have hsingle {x z : α} (hx : Nat.card (BlockFiber a x) = 2) (he : f x = f z) : x = z := by
    by_contra hne
    have hsum := card_fiber_add_le_of_eq h hne he
    have hpos := hn z
    have hle := hbsize (f x)
    omega
  let pairMap (x : PairBlock a) : PairBlock b :=
    ⟨f x.1, le_antisymm (hbsize _) (x.2.symm.le.trans (card_fiber_le h x.1))⟩
  have hpInj : Function.Injective pairMap := fun x z he =>
    Subtype.ext (hsingle x.2 (congrArg Subtype.val he))
  refine ⟨Nat.card_le_card_of_injective pairMap hpInj, fun heq => ?_⟩
  have hpSurj := ((Nat.bijective_iff_injective_and_card pairMap).mpr ⟨hpInj, heq⟩).2
  have hfInj : Function.Injective f := by
    intro x z he
    by_contra hne
    have hsum := card_fiber_add_le_of_eq h hne he
    have hx := hn x
    have hz := hn z
    have htwo : Nat.card (BlockFiber b (f x)) = 2 :=
      le_antisymm (hbsize _) (by omega)
    obtain ⟨p, hp⟩ := hpSurj ⟨f x, htwo⟩
    have hpx : f p.1 = f x := congrArg Subtype.val hp
    exact hne ((hsingle p.2 hpx).symm.trans (hsingle p.2 (hpx.trans he)))
  have hfSurj : Function.Surjective f := by
    intro t
    obtain ⟨j, hj⟩ := hb t
    obtain ⟨i, rfl⟩ := π.surjective j
    exact ⟨a i, (h i).symm.trans hj⟩
  let e := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  refine ⟨e, h, fun x => ?_⟩
  apply Nat.card_congr (π.subtypeEquiv ?_)
  intro i
  change a i = x ↔ b (π i) = f x
  rw [h i]
  exact hfInj.eq_iff.symm

end Placement

section CompactArgument

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ

private theorem val_inv_eq_transpose (u : K) : ((u⁻¹ : K) : M) = (u : M)ᵀ := by
  change star (u : M) = (u : M)ᵀ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

private theorem val_mul_transpose (u : K) : (u : M) * (u : M)ᵀ = 1 := by
  rw [← val_inv_eq_transpose]
  exact congrArg Subtype.val (mul_inv_cancel u)

private theorem val_transpose_mul (u : K) : (u : M)ᵀ * (u : M) = 1 := by
  rw [← val_inv_eq_transpose]
  exact congrArg Subtype.val (inv_mul_cancel u)

/-- The compact test argument in one column term at a frame `y` with a
product `h` of signs and active rotations. -/
def compactArgument (g : G) (y h : K) : K :=
  (signedOrthogonalPart (Unitary.toUnits y * g))⁻¹ * h⁻¹ * y

theorem continuous_signedOrthogonalPart : Continuous (signedOrthogonalPart : G → K) := by
  refine Continuous.subtype_mk ?_ (signedOrthogonal_mem (n := n))
  rw [continuous_iff_continuousAt]
  intro x
  exact (contDiffAt_signedOrthogonal x.isUnit).continuousAt.comp Units.continuous_val.continuousAt

theorem continuous_compactArgument (g : G) :
    Continuous fun p : K × K => compactArgument g p.1 p.2 := by
  unfold compactArgument
  exact (((continuous_signedOrthogonalPart.comp
    ((continuous_unitary_toUnits.comp continuous_fst).mul continuous_const)).inv).mul
      continuous_snd.inv).mul continuous_fst

/-- At a frame contributing to the identity test, the conjugated Cartan
element is upper triangular by the blocks of the active compact factors. -/
theorem blockTriangular_conj_of_compactArgument_eq_one {β : Type*} [LinearOrder β]
    {g : G} {y h : K} {b : Fin n → β} (hb : Monotone b)
    (hh : ∀ i j, b i ≠ b j → (h : M) i j = 0)
    (hfix : compactArgument g y h = 1) :
    ((y : M) * (g : M) * (y : M)ᵀ).BlockTriangular b := by
  let x : G := Unitary.toUnits y * g
  let k : K := signedOrthogonalPart x
  let B : M := (x : M) * (k : M)ᵀ
  have hB₀ : B.IsUpperTriangular := mul_transpose_signedOrthogonal_upper x.isUnit
  have hB : B.BlockTriangular b := by
    intro i j hij
    exact hB₀ (lt_of_not_ge fun hle => (not_le_of_gt hij) (hb hle))
  have hk : k * y⁻¹ = h⁻¹ := by
    have he : k = h⁻¹ * y := calc
      k = k * compactArgument g y h := by rw [hfix, mul_one]
      _ = h⁻¹ * y := by
        change k * (k⁻¹ * h⁻¹ * y) = h⁻¹ * y
        simp [mul_assoc]
    rw [he, mul_inv_cancel_right]
  have he : (k : M) * (y : M)ᵀ = (h : M)ᵀ := by
    simpa only [Submonoid.coe_mul, val_inv_eq_transpose] using congrArg Subtype.val hk
  have hhtri : (h : M)ᵀ.BlockTriangular b := fun i j hij =>
    hh j i (ne_of_lt hij)
  have hx : (x : M) = B * (k : M) := by
    change (x : M) = (x : M) * (k : M)ᵀ * (k : M)
    rw [mul_assoc, val_transpose_mul, mul_one]
  have hy : ((y : M) * (g : M)) * (y : M)ᵀ = B * (h : M)ᵀ := by
    change (x : M) * (y : M)ᵀ = _
    rw [hx, mul_assoc, he]
  rw [hy]
  exact hB.mul hhtri

/-- A compact family of test arguments that omits the identity admits a
neighborhood of the identity on which all the corresponding columns vanish
for tests supported there. -/
theorem exists_open_neighborhood_of_avoids_one (g : G) {s : Set (K × K)}
    (hs : IsCompact s) (hfix : ∀ p ∈ s, compactArgument g p.1 p.2 ≠ 1) :
    ∃ U : Set K, IsOpen U ∧ 1 ∈ U ∧
      ∀ φ : C(K, ℂ), Function.support φ ⊆ U →
        ∀ p ∈ s, φ (compactArgument g p.1 p.2) = 0 := by
  let image := (fun p : K × K => compactArgument g p.1 p.2) '' s
  have hc : IsClosed image := (hs.image (continuous_compactArgument g)).isClosed
  refine ⟨imageᶜ, hc.isOpen_compl, ?_, ?_⟩
  · rintro ⟨p, hp, he⟩
    exact hfix p hp he
  · intro φ hφ p hp
    by_contra hv
    exact hφ hv ⟨p, hp, rfl⟩

end CompactArgument

/-- A compact column can reach the identity only if there are enough target
two-coordinate blocks for the regular source Cartan planes. At equal counts,
any identity frame matches the source and target blocks by size. -/
def RealCartanCompactSupportStatement : Prop :=
  ∀ (n c t : ℕ) (a : Fin n → Fin c) (b : Fin n → Fin t) (d : Fin c → ℝ)
    (g : Langlands.GeneralLinear n ℝ) (y h : Matrix.unitaryGroup (Fin n) ℝ),
    let C := (g : Matrix (Fin n) (Fin n) ℝ)
    Function.Surjective a → Function.Surjective b → Monotone b →
    (∀ x, Nat.card (BlockFiber b x) ≤ 2) →
    (∀ i j, b i ≠ b j → (h : Matrix (Fin n) (Fin n) ℝ) i j = 0) →
    (∀ ⦃i j k⦄, i ≠ j → a i = a j → a k = a i → k = i ∨ k = j) →
    (∀ ⦃i j⦄, a i ≠ a j → C i j = 0) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j = - C j i) →
    (∀ ⦃i j⦄, i ≠ j → a i = a j → C i j ≠ 0) →
    C * Cᵀ = diagonal (d ∘ a) → Function.Injective d → C * Cᵀ = Cᵀ * C →
    compactArgument g y h = 1 →
    ∃ π : Equiv.Perm (Fin n),
      (∀ i j, a i = a j → b (π i) = b (π j)) ∧
      (∀ u i, b u ≠ b (π i) → (y : Matrix (Fin n) (Fin n) ℝ) u i = 0) ∧
      Nat.card (PairBlock a) ≤ Nat.card (PairBlock b) ∧
      (Nat.card (PairBlock a) = Nat.card (PairBlock b) →
        ∃ e : Fin c ≃ Fin t, (∀ i, b (π i) = e (a i)) ∧
          ∀ x, Nat.card (BlockFiber a x) = Nat.card (BlockFiber b (e x)))

theorem realCartanCompactSupport : RealCartanCompactSupportStatement := by
  intro n c t a b d g y h C ha hb hmono hbsize hh hsize hzero hskew hpair hgram hd hnormal hfix
  have htri := blockTriangular_conj_of_compactArgument_eq_one hmono hh hfix
  obtain ⟨π, hplace, hsupport⟩ := RealCartanFixedFlag.exists_perm_of_fixedFlag a b d
    C (y : Matrix (Fin n) (Fin n) ℝ) hsize hzero hskew hpair hgram hd hnormal
    (val_transpose_mul y) (val_mul_transpose y) htri
  exact ⟨π, hplace, hsupport, pairBlock_le_of_placement ha hb hbsize hplace⟩

end Langlands.Archimedean.RealCartanCompactSupport
