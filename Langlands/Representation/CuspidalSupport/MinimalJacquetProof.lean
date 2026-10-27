import Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.Group.GL.SingleBlock

/-!
# Nonzero quasicuspidal Jacquet descent

A proof of `MinimalNonzeroJacquetTheorem` (BZ77 section 2.14(1)). A block shape
with at most one block has trivial radical, so the Jacquet module of a nonzero
representation along it is nonzero. Among the shapes with nonzero normalized
Jacquet module, take one with the largest number of blocks. If a proper
refinement of it had nonzero inner coinvariants, the flattened shape would have
more blocks and, through a surjection onto those coinvariants, a nonzero Jacquet
module.
-/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Geometric

universe u uV

section Order

/-- The consecutive numbering of a sigma type increases lexicographically. -/
theorem finSigmaFinEquiv_lt_of {m : ℕ} {L : Fin m → ℕ}
    {x y : (i : Fin m) × Fin (L i)}
    (h : x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2.val < y.2.val)) :
    finSigmaFinEquiv x < finSigmaFinEquiv y := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
  dsimp only at h ⊢
  rcases h with hij | ⟨rfl, hab⟩
  · have hij' : i.val < j.val := hij
    have hle : (∑ k : Fin (i.val + 1), L (Fin.castLE (by omega) k)) ≤
        ∑ k : Fin j.val, L (Fin.castLE j.isLt.le k) := by
      exact Finset.sum_le_sum_of_injOn
        (fun k : Fin (i.val + 1) =>
          (Fin.castLE (show i.val + 1 ≤ j.val by omega) k : Fin j.val))
        (by intro a _ b _ h; exact Fin.ext (congrArg (fun z : Fin j.val => z.val) h))
        (by simp) (by intro k _; exact le_rfl) (by intros; exact Nat.zero_le _)
    rw [Fin.sum_univ_castSucc] at hle
    have hlast : Fin.castLE (show i.val + 1 ≤ m by omega) (Fin.last i.val) = i :=
      Fin.ext rfl
    simp only [Fin.castLE_castSucc, hlast] at hle
    have ha := a.isLt
    omega
  · omega

/-- The consecutive numbering of a sigma type is exactly the lexicographic order. -/
theorem finSigmaFinEquiv_lt_iff {m : ℕ} {L : Fin m → ℕ}
    (x y : (i : Fin m) × Fin (L i)) :
    finSigmaFinEquiv x < finSigmaFinEquiv y ↔
      x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2.val < y.2.val) := by
  refine ⟨fun hxy => ?_, finSigmaFinEquiv_lt_of⟩
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp only
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact Or.inl hij
  · rcases lt_trichotomy a.val b.val with hab | hab | hab
    · exact Or.inr ⟨rfl, hab⟩
    · obtain rfl : a = b := Fin.ext hab
      exact absurd hxy (lt_irrefl _)
    · exact absurd hxy (finSigmaFinEquiv_lt_of (L := L) (x := ⟨i, b⟩) (y := ⟨i, a⟩)
        (Or.inr ⟨rfl, hab⟩)).asymm
  · exact absurd hxy (finSigmaFinEquiv_lt_of (L := L) (x := ⟨j, b⟩) (y := ⟨i, a⟩)
      (Or.inl hji)).asymm

variable {n : ℕ} (B : BlockShape n)

/-- Coordinates of a block shape are ordered first by block, then inside the block. -/
theorem index_lt_iff {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.index i a < B.index j b ↔ i < j ∨ (i = j ∧ a.val < b.val) := by
  change (B.indexEquiv ⟨i, a⟩).val < (B.indexEquiv ⟨j, b⟩).val ↔ _
  simp only [indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  exact Fin.lt_def.symm.trans (finSigmaFinEquiv_lt_iff ⟨i, a⟩ ⟨j, b⟩)

end Order

section Flatten

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The ordered concatenation of the refinements of all blocks: first the blocks
of `S 0`, then those of `S 1`, and so on. -/
def flatten : BlockShape n where
  length := ∑ i, (S i).length
  size k := (S (finSigmaFinEquiv.symm k).1).size (finSigmaFinEquiv.symm k).2
  positive k := (S _).positive _
  sum_eq := by
    calc ∑ k, (S (finSigmaFinEquiv.symm k).1).size (finSigmaFinEquiv.symm k).2
        = ∑ q : (i : Fin B.length) × Fin (S i).length, (S q.1).size q.2 :=
          Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
      _ = ∑ i, ∑ j, (S i).size j := Fintype.sum_sigma' fun i j => (S i).size j
      _ = ∑ i, B.size i := Finset.sum_congr rfl fun i _ => (S i).sum_eq
      _ = n := B.sum_eq

/-- The flattened blocks are numbered by pairs of an outer block and one of its
inner blocks, consecutively. -/
def flattenBlockEquiv : ((i : Fin B.length) × Fin (S i).length) ≃ Fin (B.flatten S).length :=
  finSigmaFinEquiv

theorem flattenBlockEquiv_lt_iff (q q' : (i : Fin B.length) × Fin (S i).length) :
    B.flattenBlockEquiv S q < B.flattenBlockEquiv S q' ↔
      q.1 < q'.1 ∨ (q.1 = q'.1 ∧ q.2.val < q'.2.val) :=
  finSigmaFinEquiv_lt_iff q q'

theorem flatten_size_flattenBlockEquiv (q : (i : Fin B.length) × Fin (S i).length) :
    (B.flatten S).size (B.flattenBlockEquiv S q) = (S q.1).size q.2 := by
  change (S ((B.flattenBlockEquiv S).symm (B.flattenBlockEquiv S q)).1).size
    ((B.flattenBlockEquiv S).symm (B.flattenBlockEquiv S q)).2 = (S q.1).size q.2
  rw [Equiv.symm_apply_apply]

/-- Comparison of coordinates given by an inner numbering followed by the outer one. -/
theorem index_index_lt (q q' : (i : Fin B.length) × Fin (S i).length)
    (c : Fin ((S q.1).size q.2)) (c' : Fin ((S q'.1).size q'.2))
    (h : q.1 < q'.1 ∨ (q.1 = q'.1 ∧
      (q.2.val < q'.2.val ∨ (q.2.val = q'.2.val ∧ c.val < c'.val)))) :
    B.index q.1 ((S q.1).index q.2 c) < B.index q'.1 ((S q'.1).index q'.2 c') := by
  rcases q with ⟨i, j⟩
  rcases q' with ⟨i', j'⟩
  dsimp only at h ⊢
  rcases h with h | ⟨rfl, h⟩
  · exact (B.index_lt_iff _ _).mpr (Or.inl h)
  · refine (B.index_lt_iff _ _).mpr (Or.inr ⟨rfl, ?_⟩)
    refine ((S i).index_lt_iff c c').mpr ?_
    rcases h with h | ⟨h, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨Fin.ext h, hc⟩

/-- The flattened numbering of a coordinate is the outer numbering of its inner one. -/
theorem flatten_index (k : Fin (B.flatten S).length) (c : Fin ((B.flatten S).size k)) :
    (B.flatten S).index k c =
      B.index ((B.flattenBlockEquiv S).symm k).1
        ((S ((B.flattenBlockEquiv S).symm k).1).index ((B.flattenBlockEquiv S).symm k).2 c) := by
  let e := B.flattenBlockEquiv S
  let f := (B.flatten S).indexEquiv
  let φ : (B.flatten S).Index → Fin n := fun x =>
    B.index (e.symm x.1).1 ((S (e.symm x.1).1).index (e.symm x.1).2 x.2)
  have hφ : ∀ x y, f x < f y → φ x < φ y := by
    rintro ⟨k, c⟩ ⟨k', c'⟩ hxy
    rcases ((B.flatten S).index_lt_iff c c').mp hxy with hk | ⟨rfl, hc⟩
    · have hq : e (e.symm k) < e (e.symm k') := by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hk
      exact B.index_index_lt S _ _ c c'
        (((B.flattenBlockEquiv_lt_iff S _ _).mp hq).imp_right fun h => ⟨h.1, Or.inl h.2⟩)
    · exact B.index_index_lt S _ _ c c' (Or.inr ⟨rfl, Or.inr ⟨rfl, hc⟩⟩)
  have hmono : StrictMono (φ ∘ f.symm) := by
    intro a b hab
    apply hφ
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  have hfix : (φ ∘ f.symm) (f ⟨k, c⟩) = f ⟨k, c⟩ :=
    le_antisymm hmono.apply_le hmono.le_apply
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hfix
  exact hfix.symm

/-- Every coordinate of an inner block is a coordinate of the corresponding flattened
block, at the same position. -/
theorem index_index_eq_flatten (q : (i : Fin B.length) × Fin (S i).length)
    (c : Fin ((S q.1).size q.2)) :
    B.index q.1 ((S q.1).index q.2 c) =
      (B.flatten S).index (B.flattenBlockEquiv S q)
        (Fin.cast (B.flatten_size_flattenBlockEquiv S q).symm c) := by
  have key : ∀ (k : Fin (B.flatten S).length) (q : (i : Fin B.length) × Fin (S i).length)
      (hq : (B.flattenBlockEquiv S).symm k = q) (c : Fin ((S q.1).size q.2)),
      B.index q.1 ((S q.1).index q.2 c) =
        (B.flatten S).index k (Fin.cast (congrArg
          (fun r : (i : Fin B.length) × Fin (S i).length => (S r.1).size r.2) hq.symm) c) := by
    intro k q hq c
    subst hq
    exact (B.flatten_index S k c).symm
  exact key _ q ((B.flattenBlockEquiv S).symm_apply_apply q) c

/-- Every refinement block is nonempty, since the refined block is. -/
theorem one_le_refinement_length (i : Fin B.length) : 1 ≤ (S i).length := by
  by_contra h
  have h0 : (S i).length = 0 := by omega
  have hs := (S i).sum_eq
  have hp := B.positive i
  have hz : ∑ j, (S i).size j = 0 :=
    Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  omega

variable (R : Type u) [CommRing R]

/-- A proper refinement has strictly more blocks after flattening. -/
theorem length_lt_flatten (hS : refinedParabolic R B S ≠ ⊤) :
    B.length < (B.flatten S).length := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, (S i).length ≠ 1 := by
    by_contra h
    push Not at h
    apply hS
    have htop : ∀ i, (S i).parabolic R = ⊤ :=
      fun i => (S i).singleBlock_parabolic_eq_top (h i) R
    rw [refinedParabolic]
    simp only [htop, Subgroup.pi_top]
  have h1 := B.one_le_refinement_length S
  calc B.length = ∑ _i : Fin B.length, 1 := by simp
    _ < ∑ i, (S i).length :=
      Finset.sum_lt_sum (fun i _ => h1 i)
        ⟨i₀, Finset.mem_univ _, by have := h1 i₀; omega⟩

/-- The radical of the flattened shape lies in the composite radical of `B` and `S`. -/
theorem flatten_unipotentSubgroup_le :
    (B.flatten S).unipotentSubgroup R ≤ Parabolic.composedUnipotent R B S := by
  intro g hg
  rw [(B.flatten S).mem_unipotentSubgroup_iff] at hg
  obtain ⟨hgP, hgD⟩ := hg
  rw [(B.flatten S).mem_parabolic_iff] at hgP
  have hcoord : ∀ (i : Fin B.length) (a : Fin (B.size i)),
      ∃ (j : Fin (S i).length) (c : Fin ((S i).size j)), a = (S i).index j c := by
    intro i a
    obtain ⟨⟨j, c⟩, rfl⟩ := (S i).indexEquiv.surjective a
    exact ⟨j, c, rfl⟩
  have hB : g ∈ B.parabolic R := by
    rw [B.mem_parabolic_iff]
    intro i i' a b hii'
    obtain ⟨j, c, rfl⟩ := hcoord i a
    obtain ⟨j', c', rfl⟩ := hcoord i' b
    rw [B.index_index_eq_flatten S ⟨i, j⟩ c, B.index_index_eq_flatten S ⟨i', j'⟩ c']
    apply hgP
    exact (B.flattenBlockEquiv_lt_iff S _ _).mpr (Or.inl hii')
  refine (Parabolic.mem_leviPreimage_iff R B _ g).mpr ⟨hB, ?_⟩
  rw [refinedUnipotent, Subgroup.mem_pi]
  intro i _
  rw [(S i).mem_unipotentSubgroup_iff, (S i).mem_parabolic_iff]
  refine ⟨fun j j' a b hjj' => ?_, fun j a b => ?_⟩
  · rw [leviProjection_apply]
    dsimp only
    rw [B.index_index_eq_flatten S ⟨i, j⟩ a, B.index_index_eq_flatten S ⟨i, j'⟩ b]
    apply hgP
    exact (B.flattenBlockEquiv_lt_iff S _ _).mpr (Or.inr ⟨rfl, hjj'⟩)
  · rw [leviProjection_apply]
    dsimp only
    rw [B.index_index_eq_flatten S ⟨i, j⟩ a, B.index_index_eq_flatten S ⟨i, j⟩ b, hgD]
    simp only [Fin.cast_inj]

end Flatten

section WholeGroup

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every rank has a shape with at most one block: the empty shape at rank zero and
the single block otherwise. -/
theorem exists_length_le_one (n : ℕ) : ∃ B : BlockShape n, B.length ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩, zero_le_one⟩
  · exact ⟨⟨1, fun _ => n, fun _ => hn, by simp⟩, le_rfl⟩

/-- With at most one block the radical is trivial. -/
theorem unipotentRadical_val_eq_one (hB : B.length ≤ 1) (u : B.unipotentRadical R) :
    ((u : B.parabolic R) : GeneralLinear n R) = 1 := by
  have hu := (B.mem_unipotentRadical_iff R u).mp u.property
  have hx : ∀ x : Fin n, ∃ (i : Fin B.length) (a : Fin (B.size i)), x = B.index i a := by
    intro x
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    exact ⟨i, a, rfl⟩
  apply Units.ext
  ext x y
  obtain ⟨i, a, rfl⟩ := hx x
  obtain ⟨j, b, rfl⟩ := hx y
  obtain rfl : j = i := Fin.ext (by have := i.isLt; have := j.isLt; omega)
  rw [hu _ a b]
  simp only [Units.val_one, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, (B.index _).injective.ne hab]

/-- With at most one block the Jacquet quotient map is injective. -/
theorem jacquetMk_injective_of_length_le_one (hB : B.length ≤ 1)
    (ρ : Representation ℂ (GeneralLinear n R) V) : Function.Injective (B.jacquetMk ρ) := by
  rw [← LinearMap.ker_eq_bot, Jacquet.ker_mk, Jacquet.relations_eq_span,
    Submodule.span_eq_bot]
  rintro _ ⟨⟨u, v⟩, rfl⟩
  simp [B.unipotentRadical_val_eq_one R hB u]

/-- With at most one block the Jacquet module of a nonzero representation is nonzero. -/
theorem nontrivial_jacquetModule_of_length_le_one (hB : B.length ≤ 1)
    (ρ : Representation ℂ (GeneralLinear n R) V) [Nontrivial V] :
    Nontrivial (B.JacquetModule ρ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨⟨B.jacquetMk ρ v, 0, fun h => hv ?_⟩⟩
  exact B.jacquetMk_injective_of_length_le_one R hB ρ (h.trans (map_zero _).symm)

end WholeGroup

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric Parabolic

universe uF uV

namespace MinimalJacquet

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (B : BlockShape n) (S : BlockRefinement B)
  (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)

/-- An element of the composite radical acts trivially on the inner coinvariants of
the outer normalized Jacquet module, since the outer half-modulus is trivial on the
inner radical. -/
theorem mk_jacquetMk_composedUnipotent {g : GeneralLinear n F.Carrier}
    (hg : g ∈ composedUnipotent F.Carrier B S) (v : V) :
    Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S)
        (B.jacquetMk ρ (ρ g v)) =
      Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S)
        (B.jacquetMk ρ v) := by
  obtain ⟨hgP, hm⟩ := (mem_leviPreimage_iff F.Carrier B _ g).mp hg
  let q : B.parabolic F.Carrier := ⟨g, hgP⟩
  let m := B.leviProjection F.Carrier q
  have hq : q = (B.unipotentPart F.Carrier q).val * B.leviInParabolic F.Carrier m :=
    (inv_mul_cancel_right q (B.leviInParabolic F.Carrier m)).symm
  have h1 : B.jacquetMk ρ (ρ g v) = B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
    change B.jacquetMk ρ ((ρ.comp (B.parabolic F.Carrier).subtype) q v) = _
    rw [hq, map_mul, Module.End.mul_apply]
    exact Jacquet.mk_apply_subgroup (ρ.comp (B.parabolic F.Carrier).subtype)
      (B.unipotentRadical F.Carrier) (B.unipotentPart F.Carrier q) _
  have hm1 : T.leviHalfModulus B m = 1 := T.leviHalfModulus_refinedUnipotent B S ⟨m, hm⟩
  have h2 : T.normalizedJacquet B ρ m (B.jacquetMk ρ v) =
      B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) := by
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus, hm1, inv_one, one_smul]
  rw [h1, ← h2]
  exact Jacquet.mk_apply_subgroup (T.normalizedJacquet B ρ)
    (refinedUnipotent F.Carrier B S) ⟨m, hm⟩ _

/-- The flattened Jacquet module maps onto the inner coinvariants of the outer
normalized Jacquet module. -/
def flattenJacquetMap :
    (B.flatten S).JacquetModule ρ →ₗ[ℂ]
      Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S) :=
  Jacquet.lift (ρ.comp ((B.flatten S).parabolic F.Carrier).subtype)
    ((B.flatten S).unipotentRadical F.Carrier)
    (Jacquet.mk (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S) ∘ₗ
      B.jacquetMk ρ)
    (fun u => LinearMap.ext fun v =>
      mk_jacquetMk_composedUnipotent T B S ρ
        (B.flatten_unipotentSubgroup_le S F.Carrier ⟨u, u.property, rfl⟩) v)

theorem flattenJacquetMap_surjective : Function.Surjective (flattenJacquetMap T B S ρ) := by
  intro y
  obtain ⟨x, rfl⟩ := Jacquet.mk_surjective _ _ y
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  exact ⟨(B.flatten S).jacquetMk ρ v, rfl⟩

/-- Nonzero inner coinvariants give a nonzero flattened Jacquet module. -/
theorem nontrivial_flatten
    (h : Nontrivial
      (Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F.Carrier B S))) :
    Nontrivial ((B.flatten S).JacquetModule ρ) :=
  (flattenJacquetMap_surjective T B S ρ).nontrivial

end MinimalJacquet

open MinimalJacquet

/-- Nonzero quasicuspidal Jacquet descent for every rank, including rank zero. -/
theorem minimalNonzeroJacquet : MinimalNonzeroJacquetTheorem.{uF, uV} := by
  intro p _ F T n A hA
  let := T.topology
  let := T.generalLinearTopology n
  classical
  let ρ := A.representation
  let P : ℕ → Prop := fun k =>
    ∃ B : BlockShape n, B.length = k ∧ Nontrivial (B.JacquetModule ρ)
  obtain ⟨B₀, hB₀⟩ := BlockShape.exists_length_le_one n
  have hP₀ : P B₀.length :=
    ⟨B₀, rfl, B₀.nontrivial_jacquetModule_of_length_le_one F.Carrier hB₀ ρ⟩
  obtain ⟨B, hBk, hJ⟩ := Nat.findGreatest_spec (P := P) B₀.length_le hP₀
  refine ⟨B, hJ, fun S hS => ?_⟩
  by_contra hne
  rw [not_subsingleton_iff_nontrivial] at hne
  have hJ' := nontrivial_flatten T B S ρ hne
  have hlt : Nat.findGreatest P n < (B.flatten S).length := by
    rw [← hBk]
    exact B.length_lt_flatten S F.Carrier hS
  exact Nat.findGreatest_is_greatest hlt (B.flatten S).length_le ⟨B.flatten S, rfl, hJ'⟩

end Langlands.CuspidalSupport
