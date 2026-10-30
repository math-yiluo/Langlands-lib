import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.Cohomology.HerbrandQuotient

/-! # Herbrand quotients of the archimedean local unit groups

For an infinite place `w` of `E` with stabilizer `D_w ⊆ Aut(E/F)`, the local coefficient module
`E_wˣ` of `D_w` has `H¹(D_w, E_wˣ) = 0` and `|H²(D_w, E_wˣ)| = |D_w|`.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField ComplexConjugate
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Cohomology.Herbrand

section Generic

variable {k G : Type u} [CommRing k] [Group G]

/-- The subquotient `Subquotient φ ψ = ker φ ⧸ (range ψ ∩ ker φ)` is trivial when `ker φ` lies in
the range of `ψ`. -/
theorem subsingleton_subquotient_of_forall {X : Type*} [AddCommGroup X] [Module k X]
    {φ ψ : X →ₗ[k] X} (h : ∀ x, φ x = 0 → x ∈ LinearMap.range ψ) :
    Subsingleton (Subquotient φ ψ) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨x, hx, rfl⟩ := Subquotient.mk_surjective z
  exact (Subquotient.mk_eq_zero_iff x hx).2 (h x hx)

/-- For a trivial group, the cohomology groups `H¹` and `H²` vanish. -/
theorem subsingleton_groupCohomology_of_subsingleton [Subsingleton G] (A : Rep k G) :
    Subsingleton (groupCohomology A 1) ∧ Subsingleton (groupCohomology A 2) := by
  let := Fintype.ofFinite G
  have hg : ∀ x : G, x ∈ Subgroup.zpowers 1 := fun x =>
    Subsingleton.elim 1 x ▸ Subgroup.one_mem _
  have hN : ∀ x, A.ρ.norm x = x := by
    intro x
    rw [Representation.norm, LinearMap.sum_apply, Fintype.sum_subsingleton _ 1, map_one]
    rfl
  obtain ⟨e₁⟩ := nonempty_linearEquiv_one hg A
  obtain ⟨e₂⟩ := nonempty_linearEquiv_two hg A
  have s₁ : Subsingleton (Subquotient A.ρ.norm (A.ρ 1 - 1)) :=
    subsingleton_subquotient_of_forall fun x hx => ⟨0, by rw [hN] at hx; rw [hx, map_zero]⟩
  have s₂ : Subsingleton (Subquotient (A.ρ 1 - 1) A.ρ.norm) :=
    subsingleton_subquotient_of_forall fun x _ => ⟨x, hN x⟩
  exact ⟨e₁.toEquiv.subsingleton, e₂.toEquiv.subsingleton⟩

end Generic

section Value

variable {E : Type u} [Field E]

/-- The complex value of an element of the additive module `E_wˣ` under the canonical embedding
`E_w → ℂ`. -/
def infiniteLocalValue (w : InfinitePlace E) (a : Additive (w.Completion)ˣ) : ℂ :=
  InfinitePlace.Completion.extensionEmbedding w (a.toMul : w.Completion)

theorem infiniteLocalValue_add (w : InfinitePlace E) (a b : Additive (w.Completion)ˣ) :
    infiniteLocalValue w (a + b) = infiniteLocalValue w a * infiniteLocalValue w b := by
  simp [infiniteLocalValue]

theorem infiniteLocalValue_zero (w : InfinitePlace E) :
    infiniteLocalValue w 0 = 1 := by
  simp [infiniteLocalValue]

theorem infiniteLocalValue_ne_zero (w : InfinitePlace E) (a : Additive (w.Completion)ˣ) :
    infiniteLocalValue w a ≠ 0 :=
  (map_ne_zero _).2 (Units.ne_zero _)

theorem infiniteLocalValue_injective (w : InfinitePlace E) :
    Function.Injective (infiniteLocalValue w) := by
  intro a b h
  exact Additive.toMul.injective (Units.ext ((InfinitePlace.Completion.extensionEmbedding w).injective h))

theorem infiniteLocalValue_sub (w : InfinitePlace E) (a b : Additive (w.Completion)ˣ) :
    infiniteLocalValue w (a - b) = infiniteLocalValue w a / infiniteLocalValue w b := by
  rw [eq_div_iff (infiniteLocalValue_ne_zero w b), ← infiniteLocalValue_add, sub_add_cancel]

/-- At a complex place every nonzero complex number is the value of an element of `E_wˣ`. -/
theorem exists_infiniteLocalValue_eq {w : InfinitePlace E} (hw : w.IsComplex) {z : ℂ}
    (hz : z ≠ 0) : ∃ a, infiniteLocalValue w a = z := by
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw z
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hz (by rw [← hy, map_zero])
  exact ⟨Additive.ofMul (Units.mk0 y hy0), hy⟩

end Value

section Local

variable {F E : Type u} [Field F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
/-- An element of the stabilizer of `w` is trivial or a complex conjugation of `w`. -/
theorem eq_one_or_isConj_of_mem_stabilizer {w : InfinitePlace E} {d : E ≃ₐ[F] E}
    (hd : d ∈ MulAction.stabilizer (E ≃ₐ[F] E) w) :
    d = 1 ∨ ComplexEmbedding.IsConj w.embedding d := by
  rw [← w.mk_embedding, InfinitePlace.mem_stabilizer_mk_iff] at hd
  exact hd

/-- A complex conjugation of `w` acts on `E_wˣ` as complex conjugation of complex values. -/
theorem infiniteLocalValue_ρ_of_isConj {w : InfinitePlace E} {c : E ≃ₐ[F] E}
    (hc : ComplexEmbedding.IsConj w.embedding c) (a : Additive (w.Completion)ˣ) :
    infiniteLocalValue w
        ((infiniteLocalRepresentation F w).ρ ⟨c, mem_stabilizer_of_isConj hc⟩ a) =
      conj (infiniteLocalValue w a) := by
  have h := extensionEmbedding_ideleInfiniteCoordinate_of_isConj hc
    (IdeleGroup.ofCompletion (𝓞 E) E w a.toMul)
  rw [ideleInfiniteCoordinate_ofCompletion_self] at h
  exact h

/-- If `w` has a nontrivial complex conjugation `c`, then `H¹(D_w, E_wˣ) = 0` and
`|H²(D_w, E_wˣ)| = |D_w| = 2`. -/
theorem infiniteLocal_cohomology_of_isConj {w : InfinitePlace E} {c : E ≃ₐ[F] E}
    (hc : ComplexEmbedding.IsConj w.embedding c) (hc1 : c ≠ 1) :
    Subsingleton (groupCohomology (infiniteLocalRepresentation F w) 1) ∧
      Nat.card (groupCohomology (infiniteLocalRepresentation F w) 2) =
        Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) := by
  set D := MulAction.stabilizer (E ≃ₐ[F] E) w
  set A := infiniteLocalRepresentation F w
  let c' : D := ⟨c, mem_stabilizer_of_isConj hc⟩
  have hc1' : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hmem : ∀ d : D, d = 1 ∨ d = c' := by
    intro d
    rcases eq_one_or_isConj_of_mem_stabilizer d.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.ext hc))
  have hcardD : Nat.card D = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, c', hc1'.symm, Set.eq_univ_of_forall fun d => ?_⟩
    rcases hmem d with h | h
    · exact Or.inl h
    · exact Or.inr h
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; norm_num)
  let := Fintype.ofFinite D
  have hg : ∀ d : D, d ∈ Subgroup.zpowers c' := by
    intro d
    rcases hmem d with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
  have hw : w.IsComplex := by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    exact (ComplexEmbedding.isConj_ne_one_iff hc).1 hc1
  let v : A → ℂ := infiniteLocalValue w
  have vadd : ∀ a b : A, v (a + b) = v a * v b := infiniteLocalValue_add w
  have vsub : ∀ a b : A, v (a - b) = v a / v b := infiniteLocalValue_sub w
  have vzero : v 0 = 1 := infiniteLocalValue_zero w
  have vne : ∀ a : A, v a ≠ 0 := infiniteLocalValue_ne_zero w
  have vinj : ∀ a b : A, v a = v b → a = b := fun a b h => infiniteLocalValue_injective w h
  have vex : ∀ z : ℂ, z ≠ 0 → ∃ a : A, v a = z := fun z hz => exists_infiniteLocalValue_eq hw hz
  have hρ : ∀ a : A, v (A.ρ c' a) = conj (v a) := infiniteLocalValue_ρ_of_isConj hc
  have hN : ∀ a, A.ρ.norm a = a + A.ρ c' a := by
    intro a
    rw [Representation.norm, LinearMap.sum_apply,
      Fintype.sum_eq_add 1 c' hc1'.symm fun x hx => ((hmem x).elim hx.1 hx.2).elim, map_one]
    rfl
  have hvN : ∀ a, v (A.ρ.norm a) = v a * conj (v a) := by
    intro a
    rw [hN, vadd, hρ]
  have hvsub : ∀ a, v ((A.ρ c' - 1) a) = conj (v a) / v a := by
    intro a
    rw [LinearMap.sub_apply, vsub, hρ]
    rfl
  -- `H¹ = 0`: every norm-one complex number is `conj t / t`.
  have s₁ : Subsingleton (Subquotient A.ρ.norm (A.ρ c' - 1)) := by
    refine subsingleton_subquotient_of_forall fun a ha => ?_
    have hz : v a * conj (v a) = 1 := by
      rw [← hvN, ha]
      exact vzero
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (conj (v a)) two_pos
    have hnz : ‖v a‖ = 1 := by
      have h2 : ((‖v a‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast
        rw [← Complex.mul_conj', hz]
      have h3 : ‖v a‖ ^ 2 = 1 := Complex.ofReal_injective h2
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    have hnt : ‖t‖ = 1 := by
      have h3 : ‖t‖ ^ 2 = 1 := by
        rw [← norm_pow, ht, Complex.norm_conj, hnz]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at hnt
    have htt : conj t * t = 1 := by
      rw [Complex.conj_mul', hnt]
      simp
    obtain ⟨b, hb⟩ := vex t ht0
    refine ⟨b, vinj _ _ ?_⟩
    change v ((A.ρ c' - 1) b) = v a
    rw [hvsub, hb, eq_inv_of_mul_eq_one_left htt, div_eq_mul_inv, ← mul_inv, ← sq, ht,
      eq_inv_of_mul_eq_one_right hz, inv_inv]
  -- Positive real values are norms.
  have hpos : ∀ (r : ℝ), 0 < r → ∀ x : A, v x = r → x ∈ LinearMap.range A.ρ.norm := by
    intro r hr x hx
    obtain ⟨b, hb⟩ := vex (Real.sqrt r : ℂ)
      (by exact_mod_cast (Real.sqrt_pos.2 hr).ne')
    refine ⟨b, vinj _ _ ?_⟩
    change v (A.ρ.norm b) = v x
    rw [hvN, hb, Complex.mul_conj', Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← Complex.ofReal_pow, Real.sq_sqrt hr.le, hx]
  -- `H²` has the two classes of `1` and `-1`.
  obtain ⟨m, hm⟩ := vex (-1) (by norm_num)
  have hm1 : (A.ρ c' - 1) m = 0 := by
    apply vinj
    rw [hvsub, hm, vzero]
    simp
  have hcard₂ : Nat.card (Subquotient (A.ρ c' - 1) A.ρ.norm) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨0, Subquotient.mk m hm1, ?_, Set.eq_univ_of_forall fun q => ?_⟩
    · intro h
      obtain ⟨b, hb⟩ := (Subquotient.mk_eq_zero_iff m hm1).1 h.symm
      have h2 : ((‖v b‖ ^ 2 : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
        push_cast
        rw [← Complex.mul_conj', ← hvN, hb, hm]
      have h3 : ‖v b‖ ^ 2 = -1 := Complex.ofReal_injective h2
      nlinarith [sq_nonneg ‖v b‖]
    · obtain ⟨a, ha, rfl⟩ := Subquotient.mk_surjective q
      have hreal : conj (v a) = v a := by
        have h := congrArg v ha
        change v ((A.ρ c' - 1) a) = v 0 at h
        rw [hvsub, vzero, div_eq_one_iff_eq (vne a)] at h
        exact h
      have hre : ((v a).re : ℂ) = v a := Complex.conj_eq_iff_re.1 hreal
      have hre0 : (v a).re ≠ 0 := by
        intro h0
        apply vne a
        rw [← hre, h0, Complex.ofReal_zero]
      rcases lt_or_gt_of_ne hre0 with hneg | hpos'
      · right
        refine (Subquotient.mk_eq_mk_iff a m ha hm1).2 (hpos (-(v a).re) (by linarith) _ ?_)
        rw [vsub, hm, div_neg, div_one, Complex.ofReal_neg, hre]
      · left
        exact (Subquotient.mk_eq_zero_iff a ha).2 (hpos _ hpos' a hre.symm)
  obtain ⟨e₁⟩ := nonempty_linearEquiv_one hg A
  obtain ⟨e₂⟩ := nonempty_linearEquiv_two hg A
  exact ⟨e₁.toEquiv.subsingleton, by rw [Nat.card_congr e₂.toEquiv, hcard₂, hcardD]⟩

variable (F) in
/-- For every infinite place `w` of `E`: `H¹(D_w, E_wˣ) = 0` and `|H²(D_w, E_wˣ)| = |D_w|`. -/
theorem infiniteLocal_cohomology (w : InfinitePlace E) :
    Subsingleton (groupCohomology (infiniteLocalRepresentation F w) 1) ∧
      Nat.card (groupCohomology (infiniteLocalRepresentation F w) 2) =
        Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) := by
  by_cases h : ∃ d : MulAction.stabilizer (E ≃ₐ[F] E) w, d ≠ 1
  · obtain ⟨⟨c, hcD⟩, hc1⟩ := h
    have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
    exact infiniteLocal_cohomology_of_isConj
      ((eq_one_or_isConj_of_mem_stabilizer hcD).resolve_left hc1') hc1'
  · push Not at h
    have : Subsingleton (MulAction.stabilizer (E ≃ₐ[F] E) w) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    obtain ⟨h₁, h₂⟩ := subsingleton_groupCohomology_of_subsingleton
      (infiniteLocalRepresentation F w)
    exact ⟨h₁, by rw [Nat.card_of_subsingleton (0 : groupCohomology _ 2),
      Nat.card_of_subsingleton (1 : MulAction.stabilizer (E ≃ₐ[F] E) w)]⟩

variable (F) in
/-- `H¹(D_w, E_wˣ) = 0` for every infinite place `w`. -/
theorem subsingleton_groupCohomology_one_infiniteLocalRepresentation (w : InfinitePlace E) :
    Subsingleton (groupCohomology (infiniteLocalRepresentation F w) 1) :=
  (infiniteLocal_cohomology F w).1

variable (F) in
/-- `|H²(D_w, E_wˣ)| = |D_w|` for every infinite place `w`. -/
theorem natCard_groupCohomology_two_infiniteLocalRepresentation (w : InfinitePlace E) :
    Nat.card (groupCohomology (infiniteLocalRepresentation F w) 2) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) :=
  (infiniteLocal_cohomology F w).2

variable (F) in
/-- The Herbrand quotient of `E_wˣ` as a module for the stabilizer `D_w` is `|D_w|`. -/
theorem hasHerbrandQuotient_infiniteLocalRepresentation (w : InfinitePlace E) :
    HasHerbrandQuotient (infiniteLocalRepresentation F w)
      (Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w)) := by
  obtain ⟨h₁, h₂⟩ := infiniteLocal_cohomology F w
  have hD : Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w) ≠ 0 := by
    rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two F w with h | h <;> rw [h] <;> norm_num
  rw [hasHerbrandQuotient_natCast_iff]
  refine ⟨Finite.of_subsingleton, Nat.finite_of_card_ne_zero (h₂ ▸ hD), ?_⟩
  rw [h₂, Nat.card_of_subsingleton (0 : groupCohomology _ 1), mul_one]

end Local

end Langlands.ClassField.Global
