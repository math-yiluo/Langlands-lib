import Langlands.Algebra.OrderedPBWReduction

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping.PBW

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
variable {n : ℕ} (b : Module.Basis (Fin n) k L)

/-- A linear map respects all reductions strictly below a given word. -/
def RespectsBelow (w : List (Fin n)) (f : Module.End k (WordModule k n)) : Prop :=
  ∀ v p, WordLT v w → Reduction b v p → f (Finsupp.single v 1) = f p

theorem linear_eq_of_support (f g : Module.End k (WordModule k n))
    (p : WordModule k n)
    (h : ∀ w ∈ p.support, f (Finsupp.single w 1) = g (Finsupp.single w 1)) :
    f p = g p := by
  classical
  conv_lhs => rw [← p.sum_single]
  conv_rhs => rw [← p.sum_single]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have ha : Finsupp.single w (p w) = p w • Finsupp.single w 1 := by simp
  rw [ha, map_smul, map_smul, h w hw]

theorem respects_pair_of_length (w : List (Fin n)) (f : Module.End k (WordModule k n))
    (hf : RespectsBelow b w f) (i j : Fin n) (s : List (Fin n))
    (hlen : s.length + 2 < w.length) :
    f (prepend i (prepend j (Finsupp.single s 1))) =
      f (prepend j (prepend i (Finsupp.single s 1))) +
        f (insert b ⁅b i, b j⁆ (Finsupp.single s 1)) := by
  simp only [prepend_single]
  have hijw : WordLT (i :: j :: s) w := List.Shortlex.of_length_lt (by simpa using hlen)
  have hjiw : WordLT (j :: i :: s) w := List.Shortlex.of_length_lt (by simpa using hlen)
  rcases lt_trichotomy j i with hji | rfl | hij
  · simpa only [map_add] using hf _ _ hijw (Reduction.head i j s hji)
  · simp
  · have h := hf _ _ hjiw (Reduction.head j i s hij)
    have hskew : ⁅b j, b i⁆ = -⁅b i, b j⁆ := (lie_skew _ _).symm
    simp only [hskew, map_add, map_neg, LinearMap.neg_apply] at h
    rw [h]
    abel

theorem respects_insert_pair_of_length (w : List (Fin n))
    (f : Module.End k (WordModule k n)) (hf : RespectsBelow b w f)
    (x : L) (j : Fin n) (s : List (Fin n))
    (hlen : s.length + 2 < w.length) :
    f (insert b x (prepend j (Finsupp.single s 1))) =
      f (prepend j (insert b x (Finsupp.single s 1))) +
        f (insert b ⁅x, b j⁆ (Finsupp.single s 1)) := by
  classical
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_lie, smul_lie, insert_basis]
  simp_rw [respects_pair_of_length b w f hf _ j s hlen]
  simp only [smul_add, Finset.sum_add_distrib]

theorem head_disjoint (i j : Fin n) (s : List (Fin n)) (p : WordModule k n)
    (hji : j < i) (hp : Reduction b s p)
    (f : Module.End k (WordModule k n))
    (hf : RespectsBelow b (i :: j :: s) f) :
    f (Finsupp.single (j :: i :: s) 1 +
        insert b ⁅b i, b j⁆ (Finsupp.single s 1)) =
      f (prepend i (prepend j p)) := by
  classical
  have hswap := hf _ _ (shortlex_adjacent_swap [] i j s hji)
    (Reduction.cons j (Reduction.cons i hp))
  simp only [List.nil_append] at hswap
  have hins : f (insert b ⁅b i, b j⁆ (Finsupp.single s 1)) =
      f (insert b ⁅b i, b j⁆ p) := by
    simp only [insert_apply, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro t ht
    congr 1
    simpa only [prepend_single] using
      hf _ _ (List.Shortlex.of_length_lt (by simp)) (Reduction.cons t hp)
  have hlin : f (prepend i (prepend j p)) =
      f (prepend j (prepend i p) + insert b ⁅b i, b j⁆ p) := by
    let A : Module.End k (WordModule k n) := f.comp ((prepend i).comp (prepend j))
    let B : Module.End k (WordModule k n) :=
      f.comp (((prepend j).comp (prepend i)) + insert b ⁅b i, b j⁆)
    change A p = B p
    apply linear_eq_of_support A B p
    intro t ht
    have ht' := reduction_triangular b s p hp t ht
    have h := hf _ _ (List.Shortlex.cons (List.Shortlex.cons ht'))
      (Reduction.head i j t hji)
    simpa only [A, B, LinearMap.comp_apply, LinearMap.add_apply, prepend_single] using h
  rw [map_add, hswap, hins]
  simpa only [map_add] using hlin.symm

theorem head_overlap (i j h : Fin n) (s : List (Fin n))
    (hji : j < i) (hhj : h < j) (f : Module.End k (WordModule k n))
    (hf : RespectsBelow b (i :: j :: h :: s) f) :
    f (Finsupp.single (j :: i :: h :: s) 1 +
        insert b ⁅b i, b j⁆ (Finsupp.single (h :: s) 1)) =
      f (prepend i (Finsupp.single (h :: j :: s) 1 +
        insert b ⁅b j, b h⁆ (Finsupp.single s 1))) := by
  have hhi : h < i := hhj.trans hji
  have ha1 := hf _ _
    (List.Shortlex.of_lex (by simp) (List.Lex.rel hji))
    (Reduction.cons j (Reduction.head i h s hhi))
  have ha2 := hf _ _
    (List.Shortlex.of_lex (by simp) (List.Lex.rel hji))
    (Reduction.head j h (i :: s) hhj)
  have hb1 := hf _ _
    (List.Shortlex.of_lex (by simp) (List.Lex.cons (List.Lex.rel hhj)))
    (Reduction.head i h (j :: s) hhi)
  have hb2 := hf _ _
    (List.Shortlex.of_lex (by simp) (List.Lex.rel hhi))
    (Reduction.cons h (Reduction.head i j s hji))
  simp only [map_add, prepend_single] at ha1 ha2 hb1 hb2
  have hc1 := respects_insert_pair_of_length b (i :: j :: h :: s) f hf
    ⁅b j, b h⁆ i s (by simp)
  have hc2 := respects_insert_pair_of_length b (i :: j :: h :: s) f hf
    ⁅b i, b h⁆ j s (by simp)
  have hc3 := respects_insert_pair_of_length b (i :: j :: h :: s) f hf
    ⁅b i, b j⁆ h s (by simp)
  simp only [prepend_single] at hc1 hc2 hc3
  have hjac :
      ⁅⁅b j, b h⁆, b i⁆ - ⁅⁅b i, b h⁆, b j⁆ + ⁅⁅b i, b j⁆, b h⁆ = 0 := by
    rw [lie_lie (b i) (b j) (b h), ← lie_skew (b i) ⁅b j, b h⁆,
      ← lie_skew (b j) ⁅b i, b h⁆]
    abel
  have hzero := congrArg (fun x : L => f (insert b x (Finsupp.single s 1))) hjac
  simp only [map_add, map_sub, map_zero, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.zero_apply] at hzero
  calc
    _ = f (prepend i (Finsupp.single (h :: j :: s) 1 +
          insert b ⁅b j, b h⁆ (Finsupp.single s 1))) +
        (f (insert b ⁅⁅b j, b h⁆, b i⁆ (Finsupp.single s 1)) -
          f (insert b ⁅⁅b i, b h⁆, b j⁆ (Finsupp.single s 1)) +
          f (insert b ⁅⁅b i, b j⁆, b h⁆ (Finsupp.single s 1))) := by
      simp only [map_add, prepend_single]
      rw [ha1, ha2, hb1, hb2, hc1, hc2, hc3]
      abel
    _ = _ := by rw [hzero, add_zero]

theorem head_cons (i j : Fin n) (s : List (Fin n)) (p : WordModule k n)
    (hji : j < i) (hp : Reduction b (j :: s) p)
    (f : Module.End k (WordModule k n))
    (hf : RespectsBelow b (i :: j :: s) f) :
    f (Finsupp.single (j :: i :: s) 1 +
        insert b ⁅b i, b j⁆ (Finsupp.single s 1)) =
      f (prepend i p) := by
  cases hp with
  | head j h s hhj => exact head_overlap b i j h s hji hhj f hf
  | cons j hp => exact head_disjoint b i j s _ hji hp f hf

theorem reduction_coherent :
    TriangularNormalization.Coherent WordLT (Reduction b) := by
  intro w p q hp
  induction hp generalizing q with
  | head i j s hji =>
    intro hq f hf
    cases hq with
    | head => rfl
    | cons i hq => exact head_cons b i j s _ hji hq f hf
  | cons i hp ih =>
    intro hq f hf
    cases hq with
    | head i j s hji => exact (head_cons b i j s _ hji hp f hf).symm
    | cons i hq =>
      apply ih _ hq (f.comp (prepend i))
      intro v p hv hp
      have H := hf _ _ (List.Shortlex.cons hv) (Reduction.cons i hp)
      simpa only [LinearMap.comp_apply, prepend_single] using H

end Langlands.Algebra.UniversalEnveloping.PBW
