import Langlands.Representation.Jacquet.WeakIwahoriBasis
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Analysis.CountableCellLpProof
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Group.Action

/-! # Volumes of Iwahori double cosets in the central quotient

Let `K` be a compact open subgroup with an Iwahori factorization
`K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`, assume unique factorization in `Nbar * M * N`
and that the full center lies in `M`. For an element `g` of `M`, central in `M`,
with a weak Iwahori contraction, the image of `K g K` in `G ⧸ Z(G)` is the
disjoint union of the translates of the image of `K` by the classes of
`u g`, one for each left coset `u g (K ∩ N) g⁻¹` in `K ∩ N`. Its Haar measure is
the Iwahori index `[K ∩ N : g (K ∩ N) g⁻¹]` times that of the image of `K`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands.Jacquet

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The conjugate `g (K ∩ N) g⁻¹` of the radical piece of `K`. -/
def conjRadicalPiece (K : OpenSubgroup G) (N : Subgroup G) (g : G) : Subgroup G :=
  (K.toSubgroup ⊓ N).map (MulAut.conj g).toMonoidHom

theorem mem_conjRadicalPiece {K : OpenSubgroup G} {N : Subgroup G} {g x : G} :
    x ∈ conjRadicalPiece K N g ↔ ∃ v ∈ K.toSubgroup ⊓ N, g * v * g⁻¹ = x := by
  simp only [conjRadicalPiece, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-- The Iwahori index `[K ∩ N : g (K ∩ N) g⁻¹]`, as a relative index. -/
def iwahoriIndex (K : OpenSubgroup G) (N : Subgroup G) (g : G) : ℕ :=
  (conjRadicalPiece K N g).relIndex (K.toSubgroup ⊓ N)

section Factorization

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}

/-- A weak contraction maps the radical piece into itself. -/
theorem conjRadicalPiece_le (hg : IsWeakIwahoriContraction K N M Nbar g) :
    conjRadicalPiece K N g ≤ K.toSubgroup ⊓ N := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_conjRadicalPiece.mp hx
  exact hg.upper v hv

variable
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (hunique : ∀ l ∈ Nbar, ∀ m ∈ M, ∀ u ∈ N, ∀ l' ∈ Nbar, ∀ m' ∈ M, ∀ u' ∈ N,
      l * m * u = l' * m' * u' → l = l' ∧ m = m' ∧ u = u')
    (hZ : Subgroup.center G ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMNbar : M ≤ Subgroup.normalizer (Nbar : Set G))
    (hcomm : ∀ m ∈ M, m * g = g * m)

include hfactor hunique hZ hMN hMNbar hcomm in
/-- If `u g k` and `u' g k' z` agree for `u, u' ∈ K ∩ N`, `k, k' ∈ K` and a
central `z`, then `u` and `u'` lie in the same left coset of `g (K ∩ N) g⁻¹`. -/
theorem inv_mul_mem_conjRadicalPiece_of_eq (hg : IsWeakIwahoriContraction K N M Nbar g)
    {u u' k k' z : G} (hu : u ∈ K.toSubgroup ⊓ N) (hu' : u' ∈ K.toSubgroup ⊓ N)
    (hk : k ∈ K) (hk' : k' ∈ K) (hz : z ∈ Subgroup.center G)
    (h : u * g * k = u' * g * k' * z) : u'⁻¹ * u ∈ conjRadicalPiece K N g := by
  have hgM := hg.mem_levi
  obtain ⟨l, hl, m, hm, v, hv, hlmv⟩ := hfactor (k' * k⁻¹) (K.mul_mem hk' (K.inv_mem hk))
  have hzc : ∀ y : G, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  have hgl : g * l * g⁻¹ ∈ Nbar := (Subgroup.mem_normalizer_iff.mp (hMNbar hgM) l).mp hl.2
  have hgv : g * v * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN hgM) v).mp hv.2
  have hmz : m * z ∈ M := M.mul_mem hm.2 (hZ hz)
  have huu : u'⁻¹ * u ∈ N := N.mul_mem (N.inv_mem hu'.2) hu.2
  have heq : (g * l * g⁻¹) * (m * z) * (g * v * g⁻¹) = 1 * 1 * (u'⁻¹ * u) := by
    have h1 : u'⁻¹ * u = g * (k' * k⁻¹) * g⁻¹ * z := by
      have h2 : u = u' * g * k' * z * k⁻¹ * g⁻¹ := by
        rw [← h]
        group
      rw [h2, show u'⁻¹ * (u' * g * k' * z * k⁻¹ * g⁻¹) = g * k' * (z * (k⁻¹ * g⁻¹)) by group,
        hzc (k⁻¹ * g⁻¹)]
      group
    rw [h1, hlmv]
    have hmg : m * g = g * m := hcomm m hm.2
    calc g * l * g⁻¹ * (m * z) * (g * v * g⁻¹)
        = g * l * g⁻¹ * m * g * v * g⁻¹ * z := by
          rw [show g * l * g⁻¹ * (m * z) * (g * v * g⁻¹) =
            g * l * g⁻¹ * m * (z * (g * v * g⁻¹)) by group, hzc]
          group
      _ = g * l * g⁻¹ * (g * m) * v * g⁻¹ * z := by
          rw [show g * l * g⁻¹ * m * g * v * g⁻¹ * z =
            g * l * g⁻¹ * (m * g) * v * g⁻¹ * z by group, hmg]
      _ = 1 * 1 * (g * (l * m * v) * g⁻¹ * z) := by group
  obtain ⟨-, -, hv'⟩ := hunique _ hgl _ hmz _ hgv 1 Nbar.one_mem 1 M.one_mem _ huu heq
  exact mem_conjRadicalPiece.mpr ⟨v, hv, hv'⟩

end Factorization

/-- The image of the double coset `K g K` in the quotient by the full center. -/
def centralCell (K : OpenSubgroup G) (g : G) : Set (G ⧸ Subgroup.center G) :=
  QuotientGroup.mk '' DoubleCoset.doubleCoset g K K

section Cells

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (hunique : ∀ l ∈ Nbar, ∀ m ∈ M, ∀ u ∈ N, ∀ l' ∈ Nbar, ∀ m' ∈ M, ∀ u' ∈ N,
      l * m * u = l' * m' * u' → l = l' ∧ m = m' ∧ u = u')
    (hZ : Subgroup.center G ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMNbar : M ≤ Subgroup.normalizer (Nbar : Set G))
    (hcomm : ∀ m ∈ M, m * g = g * m)

/-- The class in `G ⧸ Z(G)` of `r g`, for a representative `r` of a left coset of
`g (K ∩ N) g⁻¹` in `K ∩ N`. -/
abbrev cellTranslate (K : OpenSubgroup G) (N : Subgroup G) (g : G)
    (q : ↥(K.toSubgroup ⊓ N) ⧸ (conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N)) :
    G ⧸ Subgroup.center G :=
  QuotientGroup.mk ((q.out : G) * g)

include hfactor hcomm in
/-- The central cell is the union of the translates of the image of `K` by the
classes `r g`, over the left cosets of `g (K ∩ N) g⁻¹` in `K ∩ N`. -/
theorem centralCell_eq_iUnion (hg : IsWeakIwahoriContraction K N M Nbar g) :
    centralCell K g = ⋃ q, cellTranslate K N g q •
      (QuotientGroup.mk '' (K : Set G) : Set (G ⧸ Subgroup.center G)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    -- reverse factorization `k = u * m * l`
    obtain ⟨l, hl, m, hm, u, hu, hkinv⟩ := hfactor k⁻¹ (K.inv_mem hk)
    have hk_eq : k = u⁻¹ * m⁻¹ * l⁻¹ := by rw [← inv_inv k, hkinv]; group
    let uU : ↥(K.toSubgroup ⊓ N) := ⟨u⁻¹, (K.toSubgroup ⊓ N).inv_mem hu⟩
    let q : ↥(K.toSubgroup ⊓ N) ⧸ (conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N) :=
      QuotientGroup.mk uU
    have hq : (q.out)⁻¹ * uU ∈ (conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N) := by
      rw [← QuotientGroup.eq]
      exact Quotient.out_eq' q
    rw [Subgroup.mem_subgroupOf] at hq
    obtain ⟨v, hv, hvq⟩ := mem_conjRadicalPiece.mp hq
    have hu' : u⁻¹ = (q.out : G) * (g * v * g⁻¹) := by
      rw [hvq]
      simp [uU]
    have hlg : g⁻¹ * l⁻¹ * g ∈ K := (hg.lower l⁻¹ ((K.toSubgroup ⊓ Nbar).inv_mem hl)).1
    have hmg : m⁻¹ * g = g * m⁻¹ := hcomm _ (M.inv_mem hm.2)
    refine Set.mem_iUnion.mpr ⟨q, ⟨(QuotientGroup.mk (v * m⁻¹ * (g⁻¹ * l⁻¹ * g) * k') :
      G ⧸ Subgroup.center G),
      ⟨v * m⁻¹ * (g⁻¹ * l⁻¹ * g) * k', K.mul_mem (K.mul_mem (K.mul_mem hv.1
        (K.inv_mem hm.1)) hlg) hk', rfl⟩, ?_⟩⟩
    change cellTranslate K N g q • (QuotientGroup.mk (v * m⁻¹ * (g⁻¹ * l⁻¹ * g) * k') :
      G ⧸ Subgroup.center G) = QuotientGroup.mk (k * g * k')
    rw [smul_eq_mul, ← QuotientGroup.mk_mul]
    congr 1
    rw [hk_eq, hu']
    calc (q.out : G) * g * (v * m⁻¹ * (g⁻¹ * l⁻¹ * g) * k')
        = (q.out : G) * (g * v * g⁻¹) * g * m⁻¹ * (g⁻¹ * l⁻¹ * g) * k' := by group
      _ = (q.out : G) * (g * v * g⁻¹) * (g * m⁻¹) * (g⁻¹ * l⁻¹ * g) * k' := by group
      _ = (q.out : G) * (g * v * g⁻¹) * (m⁻¹ * g) * (g⁻¹ * l⁻¹ * g) * k' := by rw [hmg]
      _ = (q.out : G) * (g * v * g⁻¹) * m⁻¹ * l⁻¹ * g * k' := by group
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, ⟨k, hk, rfl⟩, rfl⟩ := hq
    refine ⟨(q.out : G) * g * k, DoubleCoset.mem_doubleCoset.mpr
      ⟨q.out, (q.out).2.1, k, hk, rfl⟩, ?_⟩
    change _ = cellTranslate K N g q • (QuotientGroup.mk k : G ⧸ Subgroup.center G)
    rw [smul_eq_mul, ← QuotientGroup.mk_mul]

include hfactor hunique hZ hMN hMNbar hcomm in
/-- Translates by different cosets are disjoint. -/
theorem cellTranslate_disjoint (hg : IsWeakIwahoriContraction K N M Nbar g) :
    Pairwise (Function.onFun Disjoint fun q => cellTranslate K N g q •
      (QuotientGroup.mk '' (K : Set G) : Set (G ⧸ Subgroup.center G))) := by
  intro q q' hqq'
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨y, ⟨k, hk, rfl⟩, hx⟩ ⟨y', ⟨k', hk', rfl⟩, hx'⟩
  apply hqq'
  rw [← hx'] at hx
  change cellTranslate K N g q • (QuotientGroup.mk k : G ⧸ Subgroup.center G) =
    cellTranslate K N g q' • (QuotientGroup.mk k' : G ⧸ Subgroup.center G) at hx
  rw [smul_eq_mul, smul_eq_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    QuotientGroup.eq] at hx
  set z := ((q.out : G) * g * k)⁻¹ * ((q'.out : G) * g * k') with hzdef
  have heq : (q'.out : G) * g * k' = (q.out : G) * g * k * z := by rw [hzdef]; group
  have hmem := inv_mul_mem_conjRadicalPiece_of_eq hfactor hunique hZ hMN hMNbar hcomm hg
    (q'.out).2 (q.out).2 hk' hk hx heq
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  change (QuotientGroup.mk q.out : _ ⧸ (conjRadicalPiece K N g).subgroupOf _) =
    QuotientGroup.mk q'.out
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hmem

end Cells

section Index

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G}

theorem conjRadicalPiece_mul {K : OpenSubgroup G} (a b : G) :
    conjRadicalPiece K N (a * b) =
      (conjRadicalPiece K N b).map (MulAut.conj a).toMonoidHom := by
  rw [conjRadicalPiece, conjRadicalPiece, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The Iwahori index is multiplicative on weakly contracting elements. -/
theorem iwahoriIndex_mul {a b : G} (ha : IsWeakIwahoriContraction K N M Nbar a)
    (hb : IsWeakIwahoriContraction K N M Nbar b) :
    iwahoriIndex K N (a * b) = iwahoriIndex K N b * iwahoriIndex K N a := by
  unfold iwahoriIndex
  have h1 : conjRadicalPiece K N (a * b) ≤ conjRadicalPiece K N a := by
    rw [conjRadicalPiece_mul]
    exact Subgroup.map_mono (conjRadicalPiece_le hb)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 (conjRadicalPiece_le ha)]
  congr 1
  rw [conjRadicalPiece_mul]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj a).injective

/-- The Iwahori index of `a ^ m * b`. -/
theorem iwahoriIndex_pow_mul {a b : G} (ha : IsWeakIwahoriContraction K N M Nbar a)
    (hb : IsWeakIwahoriContraction K N M Nbar b) (m : ℕ) :
    iwahoriIndex K N (a ^ m * b) = iwahoriIndex K N b * iwahoriIndex K N a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hy : IsWeakIwahoriContraction K N M Nbar (a ^ m * b) := (ha.pow m).mul hb
    rw [pow_succ', mul_assoc, iwahoriIndex_mul ha hy, ih, pow_succ', mul_comm (iwahoriIndex K N a),
      mul_assoc]

end Index

/-- Two central cells that meet are equal. -/
theorem centralCell_eq_of_not_disjoint {K : OpenSubgroup G} {x y : G}
    (h : ¬ Disjoint (centralCell K x) (centralCell K y)) :
    centralCell K x = centralCell K y := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨_, ⟨p, hp, rfl⟩, ⟨p', hp', hpp'⟩⟩ := h
  obtain ⟨k1, hk1, k2, hk2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hp
  obtain ⟨k3, hk3, k4, hk4, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hp'
  rw [QuotientGroup.eq] at hpp'
  set z := (k3 * y * k4)⁻¹ * (k1 * x * k2) with hz
  have hzc : ∀ w : G, z * w = w * z := fun w => (Subgroup.mem_center_iff.mp hpp' w).symm
  have hzinv : ∀ w : G, z⁻¹ * w = w * z⁻¹ := by
    intro w
    have := hzc w
    calc z⁻¹ * w = z⁻¹ * (w * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * w) * z⁻¹ := by rw [this]
      _ = w * z⁻¹ := by group
  have hy : y = k3⁻¹ * k1 * x * k2 * k4⁻¹ * z⁻¹ := by
    have : k1 * x * k2 = k3 * y * k4 * z := by rw [hz]; group
    calc y = k3⁻¹ * (k3 * y * k4 * z) * z⁻¹ * k4⁻¹ := by group
      _ = k3⁻¹ * (k1 * x * k2) * z⁻¹ * k4⁻¹ := by rw [this]
      _ = k3⁻¹ * k1 * x * k2 * (z⁻¹ * k4⁻¹) := by group
      _ = k3⁻¹ * k1 * x * k2 * (k4⁻¹ * z⁻¹) := by rw [hzinv k4⁻¹]
      _ = k3⁻¹ * k1 * x * k2 * k4⁻¹ * z⁻¹ := by group
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hr
    refine ⟨k * k1⁻¹ * k3 * y * k4 * k2⁻¹ * k', DoubleCoset.mem_doubleCoset.mpr
      ⟨k * k1⁻¹ * k3, K.mul_mem (K.mul_mem hk (K.inv_mem hk1)) hk3,
        k4 * k2⁻¹ * k', K.mul_mem (K.mul_mem hk4 (K.inv_mem hk2)) hk', by group⟩, ?_⟩
    rw [QuotientGroup.eq]
    have hx : x = k1⁻¹ * k3 * y * k4 * z * k2⁻¹ := by
      have : k1 * x * k2 = k3 * y * k4 * z := by rw [hz]; group
      calc x = k1⁻¹ * (k1 * x * k2) * k2⁻¹ := by group
        _ = k1⁻¹ * (k3 * y * k4 * z) * k2⁻¹ := by rw [this]
        _ = k1⁻¹ * k3 * y * k4 * z * k2⁻¹ := by group
    have : (k * k1⁻¹ * k3 * y * k4 * k2⁻¹ * k')⁻¹ * (k * x * k') =
        k'⁻¹ * (k2 * (k4⁻¹ * (y⁻¹ * (k3⁻¹ * k1 * x)))) * k' := by group
    rw [this, hx]
    have e : k'⁻¹ * (k2 * (k4⁻¹ * (y⁻¹ * (k3⁻¹ * k1 * (k1⁻¹ * k3 * y * k4 * z * k2⁻¹))))) * k' =
        k'⁻¹ * (k2 * (z * k2⁻¹)) * k' := by group
    rw [e, hzc k2⁻¹]
    have e2 : k'⁻¹ * (k2 * (k2⁻¹ * z)) * k' = k'⁻¹ * (z * k') := by group
    rw [e2, hzc k', ← mul_assoc, inv_mul_cancel, one_mul]
    exact hpp'
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hr
    refine ⟨k * k3⁻¹ * k1 * x * k2 * k4⁻¹ * k', DoubleCoset.mem_doubleCoset.mpr
      ⟨k * k3⁻¹ * k1, K.mul_mem (K.mul_mem hk (K.inv_mem hk3)) hk1,
        k2 * k4⁻¹ * k', K.mul_mem (K.mul_mem hk2 (K.inv_mem hk4)) hk', by group⟩, ?_⟩
    rw [QuotientGroup.eq, hy]
    have e : (k * k3⁻¹ * k1 * x * k2 * k4⁻¹ * k')⁻¹ *
        (k * (k3⁻¹ * k1 * x * k2 * k4⁻¹ * z⁻¹) * k') = k'⁻¹ * (z⁻¹ * k') := by group
    rw [e, hzinv k', ← mul_assoc, inv_mul_cancel, one_mul]
    exact (Subgroup.center G).inv_mem hpp'

section Measure

variable [IsTopologicalGroup G] {K : OpenSubgroup G} {N M Nbar : Subgroup G} {g : G}

omit [IsTopologicalGroup G] in
/-- For `g` normalizing `N`, membership in `g (K ∩ N) g⁻¹` is membership of
`g⁻¹ x g` in `K` for `x ∈ N`. -/
theorem mem_conjRadicalPiece_iff_of_mem (hgN : g ∈ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N) : x ∈ conjRadicalPiece K N g ↔ g⁻¹ * x * g ∈ K := by
  rw [mem_conjRadicalPiece]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa [mul_assoc] using hv.1
  · intro h
    refine ⟨g⁻¹ * x * g, ⟨h, (Subgroup.mem_normalizer_iff''.mp hgN x).mp hx⟩, by group⟩

/-- `g (K ∩ N) g⁻¹` has finite index in `K ∩ N` when `K` is compact and `N` closed. -/
theorem finite_quotient_conjRadicalPiece (hK : IsCompact (K : Set G))
    (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hg : IsWeakIwahoriContraction K N M Nbar g) :
    Finite (↥(K.toSubgroup ⊓ N) ⧸ (conjRadicalPiece K N g).subgroupOf (K.toSubgroup ⊓ N)) := by
  have hc : IsCompact (((K.toSubgroup ⊓ N : Subgroup G)) : Set G) := hK.inter_right hN
  have : CompactSpace ↥(K.toSubgroup ⊓ N) := isCompact_iff_compactSpace.mp hc
  apply Subgroup.quotient_finite_of_isOpen
  have hopen : IsOpen ((fun x : G => g⁻¹ * x * g) ⁻¹' (K : Set G)) :=
    K.isOpen.preimage (by fun_prop)
  convert hopen.preimage continuous_subtype_val using 1
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
  exact mem_conjRadicalPiece_iff_of_mem (hMN hg.mem_levi) x.2.2

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (haar : Measure (G ⧸ Subgroup.center G)) [haar.IsHaarMeasure]

/-- **Iwahori double-coset volume.** The Haar measure of the image of `K g K` in
the central quotient is the Iwahori index `[K ∩ N : g (K ∩ N) g⁻¹]` times the
measure of the image of `K`. -/
theorem measure_centralCell
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (hunique : ∀ l ∈ Nbar, ∀ m ∈ M, ∀ u ∈ N, ∀ l' ∈ Nbar, ∀ m' ∈ M, ∀ u' ∈ N,
      l * m * u = l' * m' * u' → l = l' ∧ m = m' ∧ u = u')
    (hZ : Subgroup.center G ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMNbar : M ≤ Subgroup.normalizer (Nbar : Set G))
    (hcomm : ∀ m ∈ M, m * g = g * m)
    (hK : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    (hg : IsWeakIwahoriContraction K N M Nbar g) :
    haar (centralCell K g) =
      (iwahoriIndex K N g : ℝ≥0∞) * haar (QuotientGroup.mk '' (K : Set G)) := by
  have hfin := finite_quotient_conjRadicalPiece hK hN hMN hg
  have hopen : IsOpen (QuotientGroup.mk '' (K : Set G) : Set (G ⧸ Subgroup.center G)) :=
    QuotientGroup.isOpenMap_coe _ K.isOpen
  rw [centralCell_eq_iUnion hfactor hcomm hg,
    measure_iUnion (cellTranslate_disjoint hfactor hunique hZ hMN hMNbar hcomm hg)
      (fun q => (hopen.smul _).measurableSet)]
  simp only [measure_smul]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, iwahoriIndex, Subgroup.relIndex,
    Subgroup.index]
  rfl

end Measure

end Langlands.Jacquet
