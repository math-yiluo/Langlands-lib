import Langlands.Algebra.EnvelopingPBWSymbol
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Left Noetherianity of a finite-dimensional universal enveloping algebra -/

noncomputable section

open Langlands.Archimedean.Kostant MvPolynomial Finsupp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.UniversalEnveloping

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  {r : ℕ} (b : Module.Basis (Fin r) k L)

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "P" => MvPolynomial (Fin r) k
local notation "F" => degreeFiltration k L

private theorem symbol_word_mul (l m : List L) {d e : ℕ}
    (hl : l.length ≤ d) (hm : m.length ≤ e) :
    pbwSymbol b (d + e) (word k L l * word k L m) =
      pbwSymbol b d (word k L l) * pbwSymbol b e (word k L m) := by
  have he : word k L l * word k L m = word k L (l ++ m) := by
    simp [word, List.map_append, List.prod_append]
  by_cases h : (l ++ m).length < d + e
  · rw [he, pbwSymbol_eq_zero_of_lt b h (word_mem_degreeFiltration k L _)]
    by_cases h' : l.length < d
    · rw [pbwSymbol_eq_zero_of_lt b h' (word_mem_degreeFiltration k L _), zero_mul]
    · have h'' : m.length < e := by simp only [List.length_append] at h; omega
      rw [pbwSymbol_eq_zero_of_lt b h'' (word_mem_degreeFiltration k L _), mul_zero]
  · simp only [List.length_append] at h
    have hd : d = l.length := by omega
    have hd' : e = m.length := by omega
    rw [he, hd, hd', ← List.length_append, pbwSymbol_word, pbwSymbol_word, pbwSymbol_word]
    simp [List.map_append, List.prod_append]

/-- The symbol in the sum degree carries filtered multiplication to polynomial multiplication. -/
theorem pbwSymbol_mul {u v : U} {d e : ℕ} (hu : u ∈ F d) (hv : v ∈ F e) :
    pbwSymbol b (d + e) (u * v) = pbwSymbol b d u * pbwSymbol b e v := by
  have hu' := degreeFiltration_le_wordSpan k L d hu
  have hv' := degreeFiltration_le_wordSpan k L e hv
  clear hu hv
  induction hu' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    induction hv' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨m, hm, rfl⟩ := hv
      exact symbol_word_mul b l m hl hm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
    | smul c x _ hx => rw [mul_smul_comm, map_smul, hx, map_smul, mul_smul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | smul c x _ hx => rw [smul_mul_assoc, map_smul, hx, map_smul, smul_mul_assoc]

private theorem repr_zero_of_degree_lt {u : U} {d : ℕ} (hu : u ∈ F d)
    {a : Fin r →₀ ℕ} (ha : d < a.degree) : (pbwMonomialBasis b).repr u a = 0 := by
  have h := congrArg (fun p : P => p.coeff a) (pbwSymbol_eq_zero_of_lt b ha hu)
  rw [pbwSymbol_coeff, ite_eq_left rfl] at h
  exact h

private theorem mem_filtration_of_repr {u : U} {d : ℕ}
    (hu : ∀ a : Fin r →₀ ℕ, (pbwMonomialBasis b).repr u a ≠ 0 → a.degree ≤ d) :
    u ∈ F d := by
  rw [← (pbwMonomialBasis b).linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro a ha
  refine (F d).smul_mem _ (degreeFiltration_mono k L (hu a (Finsupp.mem_support_iff.mp ha)) ?_)
  rw [pbwMonomialBasis_apply]
  exact orderedMonomial_mem_degreeFiltration k L b
    (List.nodup_ofFn.mpr Function.injective_id) (fun i => List.mem_ofFn.mpr ⟨i, rfl⟩) a

private theorem mem_lower_of_zero_symbol {u : U} {d : ℕ} (hu : u ∈ F (d + 1))
    (hz : pbwSymbol b (d + 1) u = 0) : u ∈ F d := by
  apply mem_filtration_of_repr b
  intro a ha
  have hle : a.degree ≤ d + 1 :=
    not_lt.mp fun h => ha (repr_zero_of_degree_lt b hu h)
  by_contra! h
  have he : a.degree = d + 1 := by omega
  have hcoeff := congrArg (fun p : P => p.coeff a) hz
  rw [pbwSymbol_coeff, ite_eq_left he] at hcoeff
  exact ha hcoeff

private theorem eq_zero_of_zero_symbol {u : U} (hu : u ∈ F 0)
    (hz : pbwSymbol b 0 u = 0) : u = 0 := by
  apply (pbwMonomialBasis b).repr.injective
  ext a
  rw [map_zero, Finsupp.zero_apply]
  by_cases ha : a.degree = 0
  · have h := congrArg (fun p : P => p.coeff a) hz
    rw [pbwSymbol_coeff, ite_eq_left ha] at h
    exact h
  · exact repr_zero_of_degree_lt b hu (Nat.pos_of_ne_zero ha)

private def symbolDegree (J : Ideal U) (d : ℕ) : Submodule k P :=
  ((J.restrictScalars k) ⊓ F d).map (pbwSymbol b d)

private def symbolSum (J : Ideal U) : Submodule k P :=
  ⨆ d, symbolDegree b J d

private theorem mul_X_mem_symbolSum (J : Ideal U) (i : Fin r) {f : P}
    (hf : f ∈ symbolSum b J) : X i * f ∈ symbolSum b J := by
  have h : symbolSum b J ≤ (symbolSum b J).comap (LinearMap.mulLeft k (X i)) := by
    apply iSup_le
    intro d
    rintro _ ⟨u, hu, rfl⟩
    let x : U := UniversalEnvelopingAlgebra.ι k (b i)
    have hx : x ∈ F 1 := by simpa [x] using generator_mem_degreeOne k L (b i)
    have hX : pbwSymbol b 1 x = X i := by
      simpa [x, word, pbwLinearPolynomial_basis] using pbwSymbol_word b [b i]
    change X i * pbwSymbol b d u ∈ symbolSum b J
    apply Submodule.mem_iSup_of_mem (1 + d)
    refine ⟨x * u, ⟨J.mul_mem_left x hu.1, mul_mem_degreeFiltration k L hx hu.2⟩, ?_⟩
    rw [pbwSymbol_mul b hx hu.2, hX]
  exact h hf

private def symbolIdeal (J : Ideal U) : Ideal P where
  carrier := (symbolSum b J : Set P)
  zero_mem' := (symbolSum b J).zero_mem
  add_mem' := (symbolSum b J).add_mem
  smul_mem' := by
    intro p f hf
    change p * f ∈ symbolSum b J
    induction p using MvPolynomial.induction_on with
    | C c => rw [C_mul']; exact (symbolSum b J).smul_mem c hf
    | add p q hp hq => rw [add_mul]; exact (symbolSum b J).add_mem hp hq
    | mul_X p i hp =>
      rw [mul_comm p, mul_assoc]
      exact mul_X_mem_symbolSum b J i hp

private theorem homogeneousComponent_symbol (a d : ℕ) (u : U) :
    homogeneousComponent a (pbwSymbol b d u) = if a = d then pbwSymbol b d u else 0 := by
  apply homogeneousComponent_of_mem
  rw [mem_homogeneousSubmodule]
  intro m hm
  by_contra! h
  have h' : m.degree ≠ d := by
    rw [degree_eq_weight_one]
    exact h
  rw [pbwSymbol_coeff, ite_eq_right h'] at hm
  exact hm rfl

private theorem homogeneousComponent_mem_symbolDegree (J : Ideal U) (d : ℕ) {f : P}
    (hf : f ∈ symbolIdeal b J) : homogeneousComponent d f ∈ symbolDegree b J d := by
  have h : symbolSum b J ≤ (symbolDegree b J d).comap (homogeneousComponent d) := by
    apply iSup_le
    intro e
    rintro _ ⟨u, hu, rfl⟩
    change homogeneousComponent d (pbwSymbol b e u) ∈ symbolDegree b J d
    rw [homogeneousComponent_symbol]
    split_ifs with he
    · subst e
      exact ⟨u, hu, rfl⟩
    · exact (symbolDegree b J d).zero_mem
  exact h hf

private theorem symbolIdeal_mono : Monotone (symbolIdeal b) := by
  intro J N h f hf
  have he : symbolSum b J ≤ symbolSum b N := by
    apply iSup_mono
    intro d
    exact Submodule.map_mono (inf_le_inf_right _ h)
  exact he hf

private theorem ideal_le_of_symbolIdeal_le {J N : Ideal U} (hNJ : N ≤ J)
    (h : symbolIdeal b J ≤ symbolIdeal b N) : J ≤ N := by
  have hmatch (d : ℕ) (u : U) (hu : u ∈ J) (hF : u ∈ F d) :
      ∃ v : U, v ∈ N ∧ v ∈ F d ∧ pbwSymbol b d v = pbwSymbol b d u := by
    have hi : pbwSymbol b d u ∈ symbolIdeal b J :=
      Submodule.mem_iSup_of_mem d (show pbwSymbol b d u ∈ symbolDegree b J d from
        ⟨u, ⟨hu, hF⟩, rfl⟩)
    have hD := homogeneousComponent_mem_symbolDegree b N d (h hi)
    rw [homogeneousComponent_symbol, ite_eq_left rfl] at hD
    obtain ⟨v, hv, he⟩ := hD
    exact ⟨v, hv.1, hv.2, he⟩
  have hall (d : ℕ) (u : U) (hu : u ∈ J) (hF : u ∈ F d) : u ∈ N := by
    induction d generalizing u with
    | zero =>
      obtain ⟨v, hv, hV, he⟩ := hmatch 0 u hu hF
      have hz : pbwSymbol b 0 (u - v) = 0 := by rw [map_sub, he, sub_self]
      rwa [sub_eq_zero.mp (eq_zero_of_zero_symbol b ((F 0).sub_mem hF hV) hz)]
    | succ d ih =>
      obtain ⟨v, hv, hV, he⟩ := hmatch (d + 1) u hu hF
      have hz : pbwSymbol b (d + 1) (u - v) = 0 := by rw [map_sub, he, sub_self]
      have h' : u - v ∈ F d := mem_lower_of_zero_symbol b ((F (d + 1)).sub_mem hF hV) hz
      exact (sub_add_cancel u v) ▸ N.add_mem (ih (u - v) (J.sub_mem hu (hNJ hv)) h') hv
  intro u hu
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration k L u
  exact hall d u hu hd

private theorem strictMono_symbolIdeal : StrictMono (symbolIdeal b) := by
  intro N J h
  refine lt_of_le_of_ne (symbolIdeal_mono b h.le) ?_
  intro he
  exact (not_le_of_gt h) (ideal_le_of_symbolIdeal_le b h.le he.ge)

/-- The universal enveloping algebra of a finite-dimensional Lie algebra over a field
is left Noetherian. -/
def EnvelopingNoetherianStatement (k L : Type*) [Field k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] : Prop :=
  IsNoetherianRing (UniversalEnvelopingAlgebra k L)

theorem envelopingNoetherian (k L : Type*) [Field k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] : EnvelopingNoetherianStatement k L := by
  let b := Module.finBasis k L
  apply isNoetherian_iff.mpr
  refine Subrelation.wf (r := InvImage (· > ·) (symbolIdeal b)) ?_
    (InvImage.wf (symbolIdeal b) wellFounded_gt)
  intro _ _ h
  exact strictMono_symbolIdeal b h

end Langlands.Algebra.UniversalEnveloping
