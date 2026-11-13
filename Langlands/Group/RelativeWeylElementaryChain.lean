import Langlands.Group.RelativeWeylSolomonProof
import Langlands.Group.RelativeWeylLongestProof

/-!
# Elementary chains in a finite Coxeter group (Bernstein–Zelevinsky 6.5)

Inside a finite Coxeter system, with all parabolic facts proved in the ambient system,
this module shows that every element carrying a standard parabolic subgroup `W_I`
(with `I` proper) onto another one `W_J` is a product of elementary elements along a
chain of index sets. The transport relation is an arbitrary predicate `R` that implies
conjugation of the standard subgroups, contains the minimal positive simple bijections,
and contains `W_I` from `I` to `I`.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical

noncomputable section

private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-! ### Minimal coset representatives and descents -/

/-- At a minimum of `x W_I`, every simple reflection of `I` increases length. -/
theorem length_lt_mul_simple_of_right_minimal {I : Finset B} {x : W}
    (hx : ∀ y ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * y))
    {i : B} (hi : i ∈ I) : cs.length x < cs.length (x * cs.simple i) := by
  have h := hx _ (simple_mem_standardSubgroup cs hi)
  have hn := cs.length_mul_simple_ne x i
  omega

/-- A nontrivial element of `W_S` has a right descent indexed by `S`. -/
theorem exists_right_descent_of_mem {S : Finset B} {x : W}
    (hx : x ∈ standardSubgroup cs S) (h1 : x ≠ 1) :
    ∃ i ∈ S, cs.length (x * cs.simple i) < cs.length x := by
  by_contra hcon
  have hmin : ∀ j ∈ S, cs.length x < cs.length (x * cs.simple j) := by
    intro j hj
    have hle : ¬ cs.length (x * cs.simple j) < cs.length x := fun h => hcon ⟨j, hj, h⟩
    have hn := cs.length_mul_simple_ne x j
    omega
  have h := right_minimal_of_simple cs hmin x⁻¹ ((standardSubgroup cs S).inv_mem hx)
  rw [mul_inv_cancel, cs.length_one] at h
  exact h1 (cs.length_eq_zero_iff.mp (by omega))

/-- A nontrivial element of `W_S` has a left descent indexed by `S`. -/
theorem exists_left_descent_of_mem {S : Finset B} {x : W}
    (hx : x ∈ standardSubgroup cs S) (h1 : x ≠ 1) :
    ∃ i ∈ S, cs.length (cs.simple i * x) < cs.length x := by
  by_contra hcon
  have hmin : ∀ j ∈ S, cs.length x < cs.length (cs.simple j * x) := by
    intro j hj
    have hle : ¬ cs.length (cs.simple j * x) < cs.length x := fun h => hcon ⟨j, hj, h⟩
    have hn := cs.length_simple_mul_ne x j
    omega
  have h := left_minimal_of_simple cs hmin x⁻¹ ((standardSubgroup cs S).inv_mem hx)
  rw [inv_mul_cancel, cs.length_one] at h
  exact h1 (cs.length_eq_zero_iff.mp (by omega))

/-- Every element is `x * y` with `y ∈ W_I` and `x` of least length in `x W_I`. -/
theorem exists_right_minimal_decomposition (I : Finset B) (w : W) :
    ∃ x : W, ∃ y ∈ standardSubgroup cs I, w = x * y ∧
      ∀ z ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * z) := by
  obtain ⟨x, ⟨a, ha, b, hb, he⟩, hmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs ∅ I w
  have ha1 : a = 1 := by simpa using ha
  subst ha1
  refine ⟨x, b⁻¹, (standardSubgroup cs I).inv_mem hb, by simp [he], ?_⟩
  intro z hz
  simpa using hmin 1 (standardSubgroup cs ∅).one_mem z hz

/-- Right multiplication by a simple reflection outside `I` adds one to the length of
every element of `W_I`. -/
theorem length_mul_simple_of_not_mem [Fintype B] {I : Finset B} {b : B} (hb : b ∉ I)
    {x : W} (hx : x ∈ standardSubgroup cs I) :
    cs.length (x * cs.simple b) = cs.length x + 1 := by
  have hmin : ∀ i ∈ I, cs.length (cs.simple b) < cs.length (cs.simple i * cs.simple b) := by
    intro i hi
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    have hne : cs.simple i * cs.simple b ≠ 1 := by
      intro h
      apply hib
      apply simple_reflection_injective cs
      calc
        cs.simple i = (cs.simple b)⁻¹ := eq_inv_of_mul_eq_one_left h
        _ = cs.simple b := cs.inv_simple b
    have h0 : cs.length (cs.simple i * cs.simple b) ≠ 0 :=
      fun h => hne (cs.length_eq_zero_iff.mp h)
    rw [cs.length_simple]
    rcases cs.length_simple_mul (cs.simple b) i with h | h
    · rw [h, cs.length_simple]
      omega
    · rw [cs.length_simple] at h
      omega
  have h := length_mul_of_left_minimal cs (left_minimal_of_simple cs hmin) hx
  rw [h, cs.length_simple]

/-! ### Conjugation of standard subgroups -/

/-- Conjugation by `x` carries `W_I` onto `W_J`, in membership form. -/
theorem conj_left_minimal {I J : Finset B} {x : W}
    (hc : ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I)
    (hx : ∀ y ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * y)) :
    IsMinimal cs J I x := by
  intro a ha b hb
  have h := hx (x⁻¹ * a * x * b)
    ((standardSubgroup cs I).mul_mem ((hc a).mp ha) hb)
  simpa [mul_assoc] using h

/-- A minimal representative conjugating `W_I` onto `W_J` sends the simple reflections
of `I` to simple reflections of `J`. -/
theorem conj_simple_into [Fintype B] {I J : Finset B} {x : W}
    (hc : ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I)
    (hx : ∀ y ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * y))
    {i : B} (hi : i ∈ I) : ∃ j ∈ J, x * cs.simple i * x⁻¹ = cs.simple j :=
  exists_conj_simple_eq_of_isMinimal cs (conj_left_minimal cs hc hx) hi
    ((hc _).mpr (by simpa [mul_assoc] using simple_mem_standardSubgroup cs hi))

/-- A minimal representative conjugating `W_I` onto `W_J` reaches every simple
reflection of `J` from one of `I`. -/
theorem conj_simple_onto [Fintype B] {I J : Finset B} {x : W}
    (hc : ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I)
    (hx : ∀ y ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * y))
    {j : B} (hj : j ∈ J) : ∃ i ∈ I, x * cs.simple i * x⁻¹ = cs.simple j := by
  obtain ⟨i, hi, he⟩ := exists_conj_simple_eq_of_isMinimal cs
    (isMinimal_inv cs (conj_left_minimal cs hc hx)) hj
    (by simpa using (hc _).mp (simple_mem_standardSubgroup cs hj))
  refine ⟨i, hi, ?_⟩
  rw [← he]
  group

/-! ### The longest element of a standard parabolic subgroup -/

/-- A finite Coxeter group has a longest element in every standard parabolic subgroup. -/
theorem exists_longest_mem [Finite W] (S : Finset B) :
    ∃ w₀ ∈ standardSubgroup cs S,
      ∀ x ∈ standardSubgroup cs S, cs.length x ≤ cs.length w₀ :=
  Set.exists_max_image _ cs.length (Set.toFinite _) ⟨1, (standardSubgroup cs S).one_mem⟩

section Longest

variable {S : Finset B} {w₀ : W} (hw₀ : w₀ ∈ standardSubgroup cs S)
  (hmax : ∀ x ∈ standardSubgroup cs S, cs.length x ≤ cs.length w₀)
include hw₀ hmax

/-- Length complement at the longest element of `W_S`, for left factors in `W_S`. -/
theorem length_mul_longest_add {x : W} (hx : x ∈ standardSubgroup cs S) :
    cs.length (x * w₀) + cs.length x = cs.length w₀ := by
  have hinv : ∀ y ∈ standardSubgroup cs S, ∀ i ∈ S,
      reflectionParity cs w₀ (y⁻¹ * cs.simple i * y) = 1 := by
    intro y hy i hi
    have ht : cs.IsReflection (y⁻¹ * cs.simple i * y) := by
      simpa using (cs.isReflection_simple i).conj y⁻¹
    have hmem : y⁻¹ * cs.simple i * y * w₀ ∈ standardSubgroup cs S :=
      (standardSubgroup cs S).mul_mem ((standardSubgroup cs S).mul_mem
        ((standardSubgroup cs S).mul_mem ((standardSubgroup cs S).inv_mem hy)
          (simple_mem_standardSubgroup cs hi)) hy) hw₀
    have hle := hmax _ hmem
    have hne := ht.length_mul_right_ne w₀
    exact (length_reflection_mul_lt_iff cs ht).mp (by omega)
  induction hn : cs.length x generalizing x with
  | zero =>
    rw [cs.length_eq_zero_iff.mp hn]
    simp
  | succ n ih =>
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hn
    obtain ⟨i, hiS, hi⟩ := exists_left_descent_of_mem cs hx hx1
    have hyS : cs.simple i * x ∈ standardSubgroup cs S :=
      (standardSubgroup cs S).mul_mem (simple_mem_standardSubgroup cs hiS) hx
    have hxy : x = cs.simple i * (cs.simple i * x) := by simp
    have hy : cs.length (cs.simple i * x) = n := by
      rcases cs.length_simple_mul x i with h | h <;> omega
    have ihy := ih hyS hy
    have hy0 : reflectionParity cs (cs.simple i * x) (cs.simple i) = 0 := by
      rcases zmod_two_eq_zero_or_one (reflectionParity cs (cs.simple i * x) (cs.simple i))
        with h | h
      · exact h
      · have hlt := length_mul_lt_of_reflectionParity cs h
        rw [← hxy] at hlt
        omega
    have hp : reflectionParity cs (cs.simple i * x * w₀) (cs.simple i) = 1 := by
      rw [reflectionParity_mul, hy0, hinv _ hyS i hiS, zero_add]
    have hlt := length_mul_lt_of_reflectionParity cs hp
    rw [← mul_assoc, ← hxy] at hlt
    have hstep := cs.length_simple_mul (cs.simple i * x * w₀) i
    rw [← mul_assoc, ← hxy] at hstep
    omega

/-- The longest element of `W_S` is an involution. -/
theorem longest_mul_self : w₀ * w₀ = 1 := by
  have h := length_mul_longest_add cs hw₀ hmax hw₀
  exact cs.length_eq_zero_iff.mp (by omega)

/-- The longest element of `W_S` is its own inverse. -/
theorem longest_inv : w₀⁻¹ = w₀ :=
  inv_eq_of_mul_eq_one_right (longest_mul_self cs hw₀ hmax)

/-- Length complement at the longest element of `W_S`, for right factors in `W_S`. -/
theorem length_longest_mul_add {x : W} (hx : x ∈ standardSubgroup cs S) :
    cs.length (w₀ * x) + cs.length x = cs.length w₀ := by
  have h := length_mul_longest_add cs hw₀ hmax ((standardSubgroup cs S).inv_mem hx)
  rw [cs.length_inv] at h
  rwa [← cs.length_inv (x⁻¹ * w₀), mul_inv_rev, inv_inv, longest_inv cs hw₀ hmax] at h

/-- Every simple reflection of `S` is a right descent of the longest element of `W_S`. -/
theorem length_longest_mul_simple {i : B} (hi : i ∈ S) :
    cs.length (w₀ * cs.simple i) + 1 = cs.length w₀ := by
  have h := length_longest_mul_add cs hw₀ hmax (simple_mem_standardSubgroup cs hi)
  rwa [cs.length_simple] at h

/-- An element of `W_S` with every simple reflection of `S` as a right descent is the
longest element. -/
theorem eq_longest_of_forall_descent {c : W} (hc : c ∈ standardSubgroup cs S)
    (hdesc : ∀ i ∈ S, cs.length (c * cs.simple i) < cs.length c) : c = w₀ := by
  have h := length_mul_longest_add cs hw₀ hmax ((standardSubgroup cs S).inv_mem hc)
  rw [cs.length_inv] at h
  by_cases hy : c⁻¹ * w₀ = 1
  · exact inv_mul_eq_one.mp hy
  · exfalso
    obtain ⟨i, hiS, hi⟩ := exists_left_descent_of_mem cs
      ((standardSubgroup cs S).mul_mem ((standardSubgroup cs S).inv_mem hc) hw₀) hy
    have hci := hdesc i hiS
    have hsplit : w₀ = (c * cs.simple i) * (cs.simple i * (c⁻¹ * w₀)) := by
      simp [mul_assoc]
    have hle := cs.length_mul_le (c * cs.simple i) (cs.simple i * (c⁻¹ * w₀))
    rw [← hsplit] at hle
    rcases cs.length_mul_simple c i with h1 | h1 <;>
      rcases cs.length_simple_mul (c⁻¹ * w₀) i with h2 | h2 <;> omega

/-- Conjugation by the longest element of `W_S` permutes the simple reflections of `S`. -/
theorem longest_conj_simple [Fintype B] {i : B} (hi : i ∈ S) :
    ∃ j ∈ S, w₀ * cs.simple i * w₀⁻¹ = cs.simple j := by
  have h1 := length_mul_longest_add cs hw₀ hmax (simple_mem_standardSubgroup cs hi)
  rw [cs.length_simple] at h1
  have hmem : cs.simple i * w₀ ∈ standardSubgroup cs S :=
    (standardSubgroup cs S).mul_mem (simple_mem_standardSubgroup cs hi) hw₀
  have h2 := length_longest_mul_add cs hw₀ hmax hmem
  have hmem' : w₀ * cs.simple i * w₀⁻¹ ∈ standardSubgroup cs S :=
    (standardSubgroup cs S).mul_mem ((standardSubgroup cs S).mul_mem hw₀
      (simple_mem_standardSubgroup cs hi)) ((standardSubgroup cs S).inv_mem hw₀)
  apply exists_simple_of_mem_standardSubgroup cs hmem'
  rw [longest_inv cs hw₀ hmax, mul_assoc]
  omega

end Longest

/-! ### The two cosets of a maximal standard subgroup -/

/-- Let `I ⊆ S` with `S ⊆ insert b I`. If `v ∈ W_S` conjugates `W_I` onto some standard
subgroup, then `v` lies in `W_I` or in `w₀ W_I`, for `w₀` longest in `W_S`. -/
theorem mem_or_longest_inv_mul_mem [Fintype B] {S I K : Finset B} {b : B}
    (hIS : I ⊆ S) (hS : S ⊆ insert b I) {w₀ wI : W}
    (hw₀ : w₀ ∈ standardSubgroup cs S)
    (hmax : ∀ x ∈ standardSubgroup cs S, cs.length x ≤ cs.length w₀)
    (hwI : wI ∈ standardSubgroup cs I)
    (hmaxI : ∀ x ∈ standardSubgroup cs I, cs.length x ≤ cs.length wI)
    {v : W} (hv : v ∈ standardSubgroup cs S)
    (hc : ∀ g, g ∈ standardSubgroup cs K ↔ v⁻¹ * g * v ∈ standardSubgroup cs I) :
    v ∈ standardSubgroup cs I ∨ w₀⁻¹ * v ∈ standardSubgroup cs I := by
  obtain ⟨v', m, hm, rfl, hv'min⟩ := exists_right_minimal_decomposition cs I v
  have hmS : m ∈ standardSubgroup cs S := standardSubgroup_mono cs hIS hm
  have hv'S : v' ∈ standardSubgroup cs S := by
    have h := (standardSubgroup cs S).mul_mem hv ((standardSubgroup cs S).inv_mem hmS)
    simpa using h
  have hc' : ∀ g, g ∈ standardSubgroup cs K ↔ v'⁻¹ * g * v' ∈ standardSubgroup cs I := by
    intro g
    rw [hc]
    constructor
    · intro h
      have h' := (standardSubgroup cs I).mul_mem ((standardSubgroup cs I).mul_mem hm h)
        ((standardSubgroup cs I).inv_mem hm)
      simpa [mul_assoc] using h'
    · intro h
      have h' := (standardSubgroup cs I).mul_mem
        ((standardSubgroup cs I).mul_mem ((standardSubgroup cs I).inv_mem hm) h) hm
      simpa [mul_assoc] using h'
  by_cases h1 : v' = 1
  · left
    subst h1
    simpa using hm
  · right
    have hlen_y := length_mul_of_right_minimal cs hv'min hwI
    have hy : v' * wI = w₀ := by
      apply eq_longest_of_forall_descent cs hw₀ hmax
        ((standardSubgroup cs S).mul_mem hv'S (standardSubgroup_mono cs hIS hwI))
      intro j hj
      rcases Finset.mem_insert.mp (hS hj) with hjb | hjI
      · -- the extra simple reflection
        obtain ⟨i, hiS, hi⟩ := exists_right_descent_of_mem cs hv'S h1
        have hiI : i ∉ I := fun hiI => by
          have := length_lt_mul_simple_of_right_minimal cs hv'min hiI
          omega
        have hij : i = j := by
          rcases Finset.mem_insert.mp (hS hiS) with h | h
          · rw [h, hjb]
          · exact absurd h hiI
        subst hij
        have hhK : v' * wI * v'⁻¹ ∈ standardSubgroup cs K :=
          (hc' _).mpr (by simpa [mul_assoc] using hwI)
        have hLmin : ∀ x ∈ standardSubgroup cs K, cs.length v' ≤ cs.length (x * v') := by
          intro x hx
          simpa using conj_left_minimal cs hc' hv'min x hx 1 (standardSubgroup cs I).one_mem
        have hadd := length_mul_of_left_minimal cs hLmin hhK
        rw [inv_mul_cancel_right] at hadd
        have hsub := cs.length_mul_le (v' * wI * v'⁻¹) (v' * cs.simple i)
        rw [show v' * wI * v'⁻¹ * (v' * cs.simple i) = v' * wI * cs.simple i by group] at hsub
        omega
      · have h2 := length_mul_of_right_minimal cs hv'min
          ((standardSubgroup cs I).mul_mem hwI (simple_mem_standardSubgroup cs hjI))
        have h3 := length_longest_mul_simple cs hwI hmaxI hjI
        rw [mul_assoc]
        omega
    have he : w₀⁻¹ * (v' * m) = wI⁻¹ * m := by
      rw [← hy]
      group
    rw [he]
    exact (standardSubgroup cs I).mul_mem ((standardSubgroup cs I).inv_mem hwI) hm

/-- The product `ŵ = w₀ wI` of the longest elements of `W_S` and `W_I` is minimal in its
coset `ŵ W_I`. -/
theorem length_lt_longest_mul_mul_simple {S I : Finset B} (hIS : I ⊆ S) {w₀ wI : W}
    (hw₀ : w₀ ∈ standardSubgroup cs S)
    (hmax : ∀ x ∈ standardSubgroup cs S, cs.length x ≤ cs.length w₀)
    (hwI : wI ∈ standardSubgroup cs I)
    (hmaxI : ∀ x ∈ standardSubgroup cs I, cs.length x ≤ cs.length wI)
    {i : B} (hi : i ∈ I) :
    cs.length (w₀ * wI) < cs.length (w₀ * wI * cs.simple i) := by
  have hwIS := standardSubgroup_mono cs hIS hwI
  have h1 := length_longest_mul_add cs hw₀ hmax hwIS
  have h2 := length_longest_mul_add cs hw₀ hmax ((standardSubgroup cs S).mul_mem hwIS
    (simple_mem_standardSubgroup cs (hIS hi)))
  have h3 := length_longest_mul_simple cs hwI hmaxI hi
  rw [mul_assoc]
  omega

/-- The product `ŵ = w₀ wI` sends the simple reflections of `I` to simple reflections
of `S`. -/
theorem longest_mul_conj_simple [Fintype B] {S I : Finset B} (hIS : I ⊆ S) {w₀ wI : W}
    (hw₀ : w₀ ∈ standardSubgroup cs S)
    (hmax : ∀ x ∈ standardSubgroup cs S, cs.length x ≤ cs.length w₀)
    (hwI : wI ∈ standardSubgroup cs I)
    (hmaxI : ∀ x ∈ standardSubgroup cs I, cs.length x ≤ cs.length wI)
    {i : B} (hi : i ∈ I) :
    ∃ j ∈ S, w₀ * wI * cs.simple i * (w₀ * wI)⁻¹ = cs.simple j := by
  obtain ⟨j', hj', he'⟩ := longest_conj_simple cs hwI hmaxI hi
  obtain ⟨j, hj, he⟩ := longest_conj_simple cs hw₀ hmax (hIS hj')
  refine ⟨j, hj, ?_⟩
  rw [← he, ← he']
  group

/-- A family of simple conjugates `x s_i x⁻¹ = s_j` indexed by `I` has an image `K ⊆ S`
of the same cardinality, reached exactly. -/
theorem exists_simple_image [Fintype B] {I S : Finset B} {x : W}
    (hmaps : ∀ i ∈ I, ∃ j ∈ S, x * cs.simple i * x⁻¹ = cs.simple j) :
    ∃ K : Finset B, K ⊆ S ∧ K.card = I.card ∧
      (∀ i ∈ I, ∃ j ∈ K, x * cs.simple i * x⁻¹ = cs.simple j) ∧
      (∀ j ∈ K, ∃ i ∈ I, x * cs.simple i * x⁻¹ = cs.simple j) := by
  choose φ hφS hφ using hmaps
  let f : I → B := fun i => φ i.1 i.2
  have hf : Function.Injective f := by
    intro i i' hii'
    apply Subtype.ext
    apply simple_reflection_injective cs
    have h1 := hφ i.1 i.2
    have h2 := hφ i'.1 i'.2
    have h3 : x * cs.simple i.1 * x⁻¹ = x * cs.simple i'.1 * x⁻¹ := by
      rw [h1, h2]
      exact congrArg cs.simple hii'
    simpa using h3
  refine ⟨I.attach.image f, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    exact hφS i.1 i.2
  · rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  · intro i hi
    exact ⟨f ⟨i, hi⟩, Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩, hφ i hi⟩
  · intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i.1, i.2, hφ i.1 i.2⟩

/-- A subset with one element fewer misses exactly one element. -/
theorem exists_not_mem_of_card_add_one {K S : Finset B} (hKS : K ⊆ S)
    (hcard : K.card + 1 = S.card) : ∃ c ∈ S, c ∉ K ∧ S ⊆ insert c K := by
  have h1 : (S \ K).card = 1 := by
    rw [Finset.card_sdiff_of_subset hKS]
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
  have hcmem : c ∈ S \ K := hc ▸ Finset.mem_singleton_self c
  rw [Finset.mem_sdiff] at hcmem
  refine ⟨c, hcmem.1, hcmem.2, fun x hx => ?_⟩
  by_cases hxK : x ∈ K
  · exact Finset.mem_insert_of_mem hxK
  · have h : x ∈ S \ K := Finset.mem_sdiff.mpr ⟨hx, hxK⟩
    rw [hc, Finset.mem_singleton] at h
    rw [h]
    exact Finset.mem_insert_self _ _

/-- A set of group elements meeting only the cosets `H` and `g H`, both of them, has
exactly two images in `G ⧸ H`. -/
theorem nat_card_image_mk_eq_two {G : Type*} [Group G] (H : Subgroup G) (X : Set G)
    {g : G} (h1 : (1 : G) ∈ X) (hg : g ∈ X) (hgH : g ∉ H)
    (hX : ∀ v ∈ X, v ∈ H ∨ g⁻¹ * v ∈ H) :
    Nat.card ((QuotientGroup.mk : G → G ⧸ H) '' X) = 2 := by
  have heq : (QuotientGroup.mk : G → G ⧸ H) '' X =
      {(QuotientGroup.mk 1 : G ⧸ H), QuotientGroup.mk g} := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hX v hv with h | h
      · left
        exact QuotientGroup.eq.mpr (by simpa using H.inv_mem h)
      · right
        exact QuotientGroup.eq.mpr (by simpa using H.inv_mem h)
    · rintro (rfl | rfl)
      · exact ⟨1, h1, rfl⟩
      · exact ⟨g, hg, rfl⟩
  rw [heq, Nat.card_coe_set_eq, Set.ncard_pair]
  intro h
  exact hgH (by simpa using QuotientGroup.eq.mp h)

/-! ### Elementary chains -/

/-- `g` is elementary from `I` to `J`: it transports `I` to `J`, and some `S ⊇ I ∪ J`
has `g ∈ W_S` and exactly two cosets of `W_J` in `W_S` transporting `J` into `S`. -/
def IsElementaryTransport (R : Finset B → Finset B → W → Prop) (WS : Finset B → Subgroup W)
    (I J : Finset B) (g : W) : Prop :=
  R I J g ∧ ∃ S : Finset B, I ⊆ S ∧ J ⊆ S ∧ g ∈ WS S ∧
    Nat.card ((QuotientGroup.mk : W → W ⧸ WS J) ''
      {v | v ∈ WS S ∧ ∃ K : Finset B, K ⊆ S ∧ R J K v}) = 2

/-- `w` is a product `w_m ⋯ w_1` of elementary elements along a chain of index sets
from `I` to `J`. -/
def HasElementaryChain (R : Finset B → Finset B → W → Prop) (WS : Finset B → Subgroup W)
    (I J : Finset B) (w : W) : Prop :=
  ∃ (m : ℕ) (Ls : Fin (m + 1) → Finset B) (ws : Fin m → W),
    Ls 0 = I ∧ Ls (Fin.last m) = J ∧
      (∀ j : Fin m, IsElementaryTransport R WS (Ls j.castSucc) (Ls j.succ) (ws j)) ∧
      w = ((List.ofFn ws).reverse).prod

/-- Prepending an elementary step to a chain. -/
theorem hasElementaryChain_cons (R : Finset B → Finset B → W → Prop)
    {WS : Finset B → Subgroup W} {I J K : Finset B} {g x : W}
    (hg : IsElementaryTransport R WS I J g) (hx : HasElementaryChain R WS J K x) :
    HasElementaryChain R WS I K (x * g) := by
  obtain ⟨m, Ls, ws, h0, hlast, hel, rfl⟩ := hx
  refine ⟨m + 1, Fin.cons I Ls, Fin.cons g ws, rfl, ?_, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hlast]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [h0] using hg
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      exact hel j
  · rw [List.ofFn_succ]
    simp

/-- The trivial chain. -/
theorem hasElementaryChain_refl (R : Finset B → Finset B → W → Prop)
    {WS : Finset B → Subgroup W} (I : Finset B) :
    HasElementaryChain R WS I I 1 :=
  ⟨0, fun _ => I, Fin.elim0, rfl, rfl, fun j => j.elim0, by simp⟩

section Transport

variable [Fintype B] [Finite W] (R : Finset B → Finset B → W → Prop)
  (hR1 : ∀ I J x, R I J x →
    ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I)
  (hR2 : ∀ I J x, (∀ i ∈ I, cs.length x < cs.length (x * cs.simple i)) →
    (∀ i ∈ I, ∃ j ∈ J, x * cs.simple i * x⁻¹ = cs.simple j) →
    (∀ j ∈ J, ∃ i ∈ I, x * cs.simple i * x⁻¹ = cs.simple j) → R I J x)
  (hR3 : ∀ I x, x ∈ standardSubgroup cs I → R I I x)

omit [Finite W] in
include hR2 in
/-- A minimal representative conjugating `W_I` onto `W_J` satisfies the transport
predicate. -/
theorem transport_of_right_minimal
    {I J : Finset B} {x : W}
    (hc : ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I)
    (hx : ∀ y ∈ standardSubgroup cs I, cs.length x ≤ cs.length (x * y)) : R I J x :=
  hR2 I J x (fun _ hi => length_lt_mul_simple_of_right_minimal cs hx hi)
    (fun _ hi => conj_simple_into cs hc hx hi) (fun _ hj => conj_simple_onto cs hc hx hj)

include hR1 hR2 hR3 in
/-- For `I ⊆ S` with `S = insert b I` and `b ∉ I`, the elements of `W_S` transporting
`I` to a subset of `S` fill exactly two cosets of `W_I`. -/
theorem nat_card_transport_cosets_eq_two {S I : Finset B} {b : B} (hIS : I ⊆ S)
    (hbS : b ∈ S) (hbI : b ∉ I) (hS : S ⊆ insert b I) :
    Nat.card ((QuotientGroup.mk : W → W ⧸ standardSubgroup cs I) ''
      {v | v ∈ standardSubgroup cs S ∧ ∃ K : Finset B, K ⊆ S ∧ R I K v}) = 2 := by
  obtain ⟨w₀, hw₀, hmax⟩ := exists_longest_mem cs S
  obtain ⟨wI, hwI, hmaxI⟩ := exists_longest_mem cs I
  have hwIS := standardSubgroup_mono cs hIS hwI
  obtain ⟨K, hKS, -, hinto, honto⟩ := exists_simple_image cs
    (fun i hi => longest_mul_conj_simple cs hIS hw₀ hmax hwI hmaxI hi)
  apply nat_card_image_mk_eq_two _ _ (g := w₀ * wI)
  · exact ⟨(standardSubgroup cs S).one_mem, I, hIS, hR3 I 1 (standardSubgroup cs I).one_mem⟩
  · refine ⟨(standardSubgroup cs S).mul_mem hw₀ hwIS, K, hKS, hR2 I K _ ?_ hinto honto⟩
    intro i hi
    exact length_lt_longest_mul_mul_simple cs hIS hw₀ hmax hwI hmaxI hi
  · intro hmem
    have hw₀I : w₀ ∈ standardSubgroup cs I := by
      have h := (standardSubgroup cs I).mul_mem hmem ((standardSubgroup cs I).inv_mem hwI)
      simpa using h
    have h1 := length_mul_simple_of_not_mem cs hbI hw₀I
    have h2 := length_longest_mul_simple cs hw₀ hmax hbS
    omega
  · rintro v ⟨hv, K', -, hR⟩
    rcases mem_or_longest_inv_mul_mem cs hIS hS hw₀ hmax hwI hmaxI hv (hR1 _ _ _ hR) with
      h | h
    · exact Or.inl h
    · right
      have h' := (standardSubgroup cs I).mul_mem ((standardSubgroup cs I).inv_mem hwI) h
      simpa [mul_assoc] using h'

include hR1 hR2 hR3 in
/-- The minimal case (Bernstein–Zelevinsky 6.5(4)): induction on the length of a
minimal representative. -/
theorem hasElementaryChain_of_right_minimal (n : ℕ) :
    ∀ (x : W) (IL IM : Finset B), cs.length x = n → (∃ a, a ∉ IL) →
      (∀ y ∈ standardSubgroup cs IL, cs.length x ≤ cs.length (x * y)) → R IL IM x →
      HasElementaryChain R (standardSubgroup cs) IL IM x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x IL IM hn _ hxmin hR
  have hc := hR1 _ _ _ hR
  by_cases hx1 : x = 1
  · subst hx1
    have hLM : IL = IM := by
      apply standardSubgroup_injective cs
      ext g
      simpa using (hc g).symm
    subst hLM
    exact hasElementaryChain_refl R IL
  obtain ⟨α, hα⟩ := cs.exists_rightDescent_of_ne_one hx1
  have hα' : cs.length (x * cs.simple α) < cs.length x := hα
  have hαL : α ∉ IL := fun h => by
    have := length_lt_mul_simple_of_right_minimal cs hxmin h
    omega
  set S := insert α IL with hS_def
  have hLS : IL ⊆ S := Finset.subset_insert _ _
  have hαS : α ∈ S := Finset.mem_insert_self _ _
  obtain ⟨w₀, hw₀, hmax⟩ := exists_longest_mem cs S
  obtain ⟨wI, hwI, hmaxI⟩ := exists_longest_mem cs IL
  have hwIS := standardSubgroup_mono cs hLS hwI
  obtain ⟨K, hKS, hKcard, hinto, honto⟩ := exists_simple_image cs
    (fun i hi => longest_mul_conj_simple cs hLS hw₀ hmax hwI hmaxI hi)
  have hpos : ∀ i ∈ IL, cs.length (w₀ * wI) < cs.length (w₀ * wI * cs.simple i) :=
    fun i hi => length_lt_longest_mul_mul_simple cs hLS hw₀ hmax hwI hmaxI hi
  have hRhat : R IL K (w₀ * wI) := hR2 IL K _ hpos hinto honto
  have hchat := hR1 _ _ _ hRhat
  obtain ⟨c, hcS, hcK, hSK⟩ := exists_not_mem_of_card_add_one hKS
    (by rw [hKcard, hS_def, Finset.card_insert_of_notMem hαL])
  -- `y = x wI` has every simple reflection of `S` as a right descent.
  have hlen_y := length_mul_of_right_minimal cs hxmin hwI
  have hdesc : ∀ j ∈ S, cs.length (x * wI * cs.simple j) < cs.length (x * wI) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjI
    · have hhM : x * wI * x⁻¹ ∈ standardSubgroup cs IM :=
        (hc _).mpr (by simpa [mul_assoc] using hwI)
      have hLmin : ∀ z ∈ standardSubgroup cs IM, cs.length x ≤ cs.length (z * x) := by
        intro z hz
        simpa using conj_left_minimal cs hc hxmin z hz 1 (standardSubgroup cs IL).one_mem
      have hadd := length_mul_of_left_minimal cs hLmin hhM
      rw [inv_mul_cancel_right] at hadd
      have hsub := cs.length_mul_le (x * wI * x⁻¹) (x * cs.simple j)
      rw [show x * wI * x⁻¹ * (x * cs.simple j) = x * wI * cs.simple j by group] at hsub
      omega
    · have h2 := length_mul_of_right_minimal cs hxmin
        ((standardSubgroup cs IL).mul_mem hwI (simple_mem_standardSubgroup cs hjI))
      have h3 := length_longest_mul_simple cs hwI hmaxI hjI
      rw [mul_assoc]
      omega
  -- Hence `x wI = x' w₀` with `x'` minimal in `x' W_S`.
  obtain ⟨x', u, hu, hy, hx'min⟩ := exists_right_minimal_decomposition cs S (x * wI)
  have hu0 : u = w₀ := by
    apply eq_longest_of_forall_descent cs hw₀ hmax hu
    intro j hj
    have h1 := length_mul_of_right_minimal cs hx'min hu
    have h2 := length_mul_of_right_minimal cs hx'min
      ((standardSubgroup cs S).mul_mem hu (simple_mem_standardSubgroup cs hj))
    have h3 := hdesc j hj
    rw [hy, mul_assoc] at h3
    rw [hy] at hlen_y
    omega
  subst hu0
  have hx' : x' = x * (u * wI)⁻¹ := by
    rw [mul_inv_rev, longest_inv cs hwI hmaxI, longest_inv cs hw₀ hmax, ← mul_assoc, hy]
    rw [mul_assoc, longest_mul_self cs hw₀ hmax, mul_one]
  have hx'len : cs.length x' < cs.length x := by
    have h1 := length_mul_of_right_minimal cs hx'min hu
    have h2 := length_mul_simple_of_not_mem cs hαL hwI
    have h3 := hmax _ ((standardSubgroup cs S).mul_mem hwIS (simple_mem_standardSubgroup cs hαS))
    rw [← hy] at h1
    omega
  have hx'K : ∀ z ∈ standardSubgroup cs K, cs.length x' ≤ cs.length (x' * z) :=
    fun z hz => hx'min z (standardSubgroup_mono cs hKS hz)
  have hc' : ∀ g, g ∈ standardSubgroup cs IM ↔ x'⁻¹ * g * x' ∈ standardSubgroup cs K := by
    intro g
    rw [hc, hchat, hx']
    simp only [mul_inv_rev, inv_inv]
    constructor
    · intro h
      simpa [mul_assoc] using h
    · intro h
      simpa [mul_assoc] using h
  have hRx' : R K IM x' := transport_of_right_minimal cs R hR2 hc' hx'K
  have hchain := ih _ (hn ▸ hx'len) x' K IM rfl ⟨c, hcK⟩ hx'K hRx'
  have hel : IsElementaryTransport R (standardSubgroup cs) IL K (u * wI) :=
    ⟨hRhat, S, hLS, hKS, (standardSubgroup cs S).mul_mem hu hwIS,
      nat_card_transport_cosets_eq_two cs R hR1 hR2 hR3 hKS hcS hcK hSK⟩
  have h := hasElementaryChain_cons R hel hchain
  rwa [hx', inv_mul_cancel_right] at h

include hR1 hR2 hR3 in
/-- **Elementary chains (Bernstein–Zelevinsky 1977, Lemma 2.17).** For `I` proper, every
element transporting `I` to `J` is a product of elementary elements along a chain of
index sets from `I` to `J`. -/
theorem hasElementaryChain (WS : Finset B → Subgroup W)
    (hWS : ∀ I, standardSubgroup cs I = WS I) {IL IM : Finset B} (ha : ∃ a, a ∉ IL)
    {w : W} (hw : R IL IM w) : HasElementaryChain R WS IL IM w := by
  obtain rfl : standardSubgroup cs = WS := funext hWS
  obtain ⟨a, haL⟩ := ha
  obtain ⟨x, u, hu, rfl, hxmin⟩ := exists_right_minimal_decomposition cs IL w
  have hc := hR1 _ _ _ hw
  have hcx : ∀ g, g ∈ standardSubgroup cs IM ↔ x⁻¹ * g * x ∈ standardSubgroup cs IL := by
    intro g
    rw [hc]
    constructor
    · intro h
      have h' := (standardSubgroup cs IL).mul_mem ((standardSubgroup cs IL).mul_mem hu h)
        ((standardSubgroup cs IL).inv_mem hu)
      simpa [mul_assoc] using h'
    · intro h
      have h' := (standardSubgroup cs IL).mul_mem
        ((standardSubgroup cs IL).mul_mem ((standardSubgroup cs IL).inv_mem hu) h) hu
      simpa [mul_assoc] using h'
  have hRx : R IL IM x := transport_of_right_minimal cs R hR2 hcx hxmin
  have hchain := hasElementaryChain_of_right_minimal cs R hR1 hR2 hR3 _ x IL IM rfl
    ⟨a, haL⟩ hxmin hRx
  have hLS : IL ⊆ insert a IL := Finset.subset_insert _ _
  have hel : IsElementaryTransport R (standardSubgroup cs) IL IL u :=
    ⟨hR3 IL u hu, insert a IL, hLS, hLS, standardSubgroup_mono cs hLS hu,
      nat_card_transport_cosets_eq_two cs R hR1 hR2 hR3 hLS (Finset.mem_insert_self _ _) haL
        subset_rfl⟩
  exact hasElementaryChain_cons R hel hchain

end Transport

end

end Langlands.Group.RelativeWeylIndexing
