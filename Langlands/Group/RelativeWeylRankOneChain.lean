import Langlands.Group.RelativeWeylElementaryChain

/-!
# Chains of rank-one steps in a finite Coxeter group

A right `I`-minimal element `x` of a finite Coxeter group that conjugates `W_I` onto `W_J` is
the product `x = g_{m-1} ⋯ g_0` of steps along a chain of index sets `I = L_0, …, L_m = J`. Each
step `g_t` lies in `W_{L_t ∪ {a_t}}` for an index `a_t ∉ L_t`, has `L_{t+1} ⊆ L_t ∪ {a_t}`, raises
the length on the simple reflections of `L_t`, and conjugates them bijectively onto those of
`L_{t+1}`. This is the recursion of Bernstein–Zelevinsky 6.5(2), (4), with the step
`ŵ = w₀^{L ∪ {a}} w₀^{L}`, recorded with its rank-one data.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W) [DecidableEq B]

noncomputable section

omit [DecidableEq B] in
/-- A bijection of simple reflections by conjugation carries `W_I` onto `W_J`, in membership
form. -/
theorem mem_standardSubgroup_iff_of_simple_bijection {I J : Finset B} {g : W}
    (hinto : ∀ i ∈ I, ∃ j ∈ J, g * cs.simple i * g⁻¹ = cs.simple j)
    (honto : ∀ j ∈ J, ∃ i ∈ I, g * cs.simple i * g⁻¹ = cs.simple j) (h : W) :
    h ∈ standardSubgroup cs J ↔ g⁻¹ * h * g ∈ standardSubgroup cs I := by
  have hmap : (standardSubgroup cs I).map (MulAut.conj g).toMonoidHom =
      standardSubgroup cs J := by
    rw [standardSubgroup, standardSubgroup, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      obtain ⟨j, hj, he⟩ := hinto i hi
      exact ⟨j, hj, by rw [← he]; rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, he⟩ := honto j hj
      exact ⟨cs.simple i, ⟨i, hi, rfl⟩, by rw [← he]; rfl⟩
  rw [← hmap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (g * y * g⁻¹) * g ∈ standardSubgroup cs I
    simpa [mul_assoc] using hy
  · intro hh
    refine ⟨g⁻¹ * h * g, hh, ?_⟩
    change g * (g⁻¹ * h * g) * g⁻¹ = h
    group

/-- `g` is a rank-one step from `I` to `J` along `a`: `a ∉ I`, `J ⊆ I ∪ {a}`, `g ∈ W_{I ∪ {a}}`,
`g` raises the length on the simple reflections of `I`, and conjugation by `g` maps the simple
reflections of `I` bijectively onto those of `J`. -/
def IsRankOneStep (I J : Finset B) (a : B) (g : W) : Prop :=
  a ∉ I ∧ J ⊆ insert a I ∧ g ∈ standardSubgroup cs (insert a I) ∧
    (∀ i ∈ I, cs.length g < cs.length (g * cs.simple i)) ∧
    (∀ i ∈ I, ∃ j ∈ J, g * cs.simple i * g⁻¹ = cs.simple j) ∧
    (∀ j ∈ J, ∃ i ∈ I, g * cs.simple i * g⁻¹ = cs.simple j)

/-- `x` is the product `g_{m-1} ⋯ g_0` of rank-one steps along a chain of index sets from `I`
to `J`; `xs t = g_{t-1} ⋯ g_0` are the partial products. -/
def HasRankOneChain (I J : Finset B) (x : W) : Prop :=
  ∃ (m : ℕ) (Ls : Fin (m + 1) → Finset B) (as : Fin m → B) (gs : Fin m → W)
    (xs : Fin (m + 1) → W),
    Ls 0 = I ∧ Ls (Fin.last m) = J ∧ xs 0 = 1 ∧ xs (Fin.last m) = x ∧
      ∀ t : Fin m, IsRankOneStep cs (Ls t.castSucc) (Ls t.succ) (as t) (gs t) ∧
        xs t.succ = gs t * xs t.castSucc

/-- The empty chain. -/
theorem hasRankOneChain_refl (I : Finset B) : HasRankOneChain cs I I 1 :=
  ⟨0, fun _ => I, Fin.elim0, Fin.elim0, fun _ => 1, rfl, rfl, rfl, rfl, fun t => t.elim0⟩

/-- Prepending a rank-one step to a chain. -/
theorem hasRankOneChain_cons {I J K : Finset B} {a : B} {g x : W}
    (hg : IsRankOneStep cs I J a g) (hx : HasRankOneChain cs J K x) :
    HasRankOneChain cs I K (x * g) := by
  obtain ⟨m, Ls, as, gs, xs, h0, hlast, hx0, hxlast, hstep⟩ := hx
  refine ⟨m + 1, Fin.cons I Ls, Fin.cons a as, Fin.cons g gs,
    Fin.cons 1 (fun t => xs t * g), rfl, ?_, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ, hlast]
  · rw [← Fin.succ_last, Fin.cons_succ, hxlast]
  · intro t
    refine Fin.cases ?_ (fun s => ?_) t
    · refine ⟨?_, ?_⟩
      · simpa [h0] using hg
      · simp [hx0]
    · rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ]
      refine ⟨(hstep s).1, ?_⟩
      rw [(hstep s).2, mul_assoc]

variable [Fintype B] [Finite W]

/-- **Rank-one chains** (Bernstein–Zelevinsky 6.5(2), (4)). A right `IL`-minimal element `x`
conjugating `W_IL` onto `W_IM` is a product of rank-one steps along a chain from `IL` to
`IM`. The proof is by strong induction on the length of `x`. -/
theorem hasRankOneChain_of_right_minimal (n : ℕ) :
    ∀ (x : W) (IL IM : Finset B), cs.length x = n →
      (∀ y ∈ standardSubgroup cs IL, cs.length x ≤ cs.length (x * y)) →
      (∀ g, g ∈ standardSubgroup cs IM ↔ x⁻¹ * g * x ∈ standardSubgroup cs IL) →
      HasRankOneChain cs IL IM x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x IL IM hn hxmin hc
  by_cases hx1 : x = 1
  · subst hx1
    have hLM : IL = IM := by
      apply standardSubgroup_injective cs
      ext g
      simpa using (hc g).symm
    subst hLM
    exact hasRankOneChain_refl cs IL
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
  obtain ⟨K, hKS, -, hinto, honto⟩ := exists_simple_image cs
    (fun i hi => longest_mul_conj_simple cs hLS hw₀ hmax hwI hmaxI hi)
  have hpos : ∀ i ∈ IL, cs.length (w₀ * wI) < cs.length (w₀ * wI * cs.simple i) :=
    fun i hi => length_lt_longest_mul_mul_simple cs hLS hw₀ hmax hwI hmaxI hi
  have hchat := mem_standardSubgroup_iff_of_simple_bijection cs hinto honto
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
  have hchain := ih _ (hn ▸ hx'len) x' K IM rfl hx'K hc'
  have hstep : IsRankOneStep cs IL K α (u * wI) :=
    ⟨hαL, hKS, (standardSubgroup cs S).mul_mem hu hwIS, hpos, hinto, honto⟩
  have h := hasRankOneChain_cons cs hstep hchain
  rwa [hx', inv_mul_cancel_right] at h

end

end Langlands.Group.RelativeWeylIndexing
