import Langlands.GroupScheme.Composition.CayleyIdentities

/-! # Gradings of a Cayley datum by abelian groups, and a rank bound -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

local notation "μ" => c.multiplication

/-- A grading of a Cayley datum by an additive group `M`, presented by its projection
matrices: orthogonal idempotents with finite support summing to the identity, the unit of
degree zero, and products of homogeneous vectors homogeneous of the sum of the degrees. -/
structure Grading (M : Type v) [AddCommGroup M] [DecidableEq M] where
  /-- The projection onto the homogeneous component of degree `m`. -/
  proj : M → Matrix (Fin 8) (Fin 8) K
  /-- The finite set of degrees with a nonzero component. -/
  support : Finset M
  mem_support : ∀ m, m ∈ support ↔ proj m ≠ 0
  sum_proj : ∑ m ∈ support, proj m = 1
  proj_mul_proj : ∀ m n, proj m * proj n = if m = n then proj m else 0
  proj_unit : proj 0 *ᵥ c.unit = c.unit
  proj_mul : ∀ a b x y, proj a *ᵥ x = x → proj b *ᵥ y = y →
    proj (a + b) *ᵥ c.multiplication x y = c.multiplication x y

/-- The unit of a Cayley datum is nonzero. -/
theorem unit_ne_zero : c.unit ≠ 0 := fun h => by
  have h1 := c.norm_unit
  rw [h, QuadraticMap.map_zero] at h1
  exact zero_ne_one h1

namespace Grading

variable {c} {M : Type v} [AddCommGroup M] [DecidableEq M] (g : c.Grading M)

theorem proj_mulVec_of_eq {m n : M} {x : CayleyVector K} (hx : g.proj n *ᵥ x = x) :
    g.proj m *ᵥ x = if m = n then x else 0 := by
  conv_lhs => rw [← hx, Matrix.mulVec_mulVec, g.proj_mul_proj]
  split_ifs with h
  · subst h
    exact hx
  · exact Matrix.zero_mulVec x

theorem proj_proj (m : M) (x : CayleyVector K) :
    g.proj m *ᵥ (g.proj m *ᵥ x) = g.proj m *ᵥ x := by
  rw [Matrix.mulVec_mulVec, g.proj_mul_proj, ite_eq_left rfl]

theorem proj_eq_zero {m : M} (hm : m ∉ g.support) : g.proj m = 0 := by
  by_contra h
  exact hm ((g.mem_support m).mpr h)

theorem eq_zero_of_not_mem {n : M} {x : CayleyVector K} (hx : g.proj n *ᵥ x = x)
    (hn : n ∉ g.support) : x = 0 := by
  rw [← hx, g.proj_eq_zero hn, Matrix.zero_mulVec]

theorem sum_proj_mulVec (x : CayleyVector K) : ∑ m ∈ g.support, g.proj m *ᵥ x = x := by
  rw [← Matrix.sum_mulVec, g.sum_proj, Matrix.one_mulVec]

theorem mul_eq_zero_of_not_mem {a b : M} {x y : CayleyVector K} (hx : g.proj a *ᵥ x = x)
    (hy : g.proj b *ᵥ y = y) (hab : a + b ∉ g.support) : μ x y = 0 :=
  g.eq_zero_of_not_mem (g.proj_mul a b x y hx hy) hab

theorem proj_unit_of_ne {m : M} (hm : m ≠ 0) : g.proj m *ᵥ c.unit = 0 := by
  rw [g.proj_mulVec_of_eq g.proj_unit, if_neg hm]

/-- A homogeneous vector of nonzero degree has trace zero. -/
theorem trace_eq_zero {a : M} (ha : a ≠ 0) {x : CayleyVector K} (hx : g.proj a *ᵥ x = x) :
    c.trace x = 0 := by
  have hsq := c.mul_self x
  have h2 := g.proj_mul a a x x hx hx
  have h3 : g.proj a *ᵥ μ x x = 0 := by
    rw [g.proj_mulVec_of_eq h2, if_neg]
    intro h
    exact ha (add_left_cancel (h.symm.trans (add_zero a).symm))
  rw [hsq, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hx,
    g.proj_unit_of_ne ha, smul_zero, sub_zero] at h3
  rcases smul_eq_zero.mp h3 with h | h
  · exact h
  · rw [h]
    simp [trace]

/-- Homogeneous vectors whose degrees do not sum to zero are orthogonal. -/
theorem form_eq_zero {a b : M} (hab : a + b ≠ 0) {x y : CayleyVector K}
    (hx : g.proj a *ᵥ x = x) (hy : g.proj b *ᵥ y = y) : c.form x y = 0 := by
  have h := c.trace_mul x y
  rw [g.trace_eq_zero hab (g.proj_mul a b x y hx hy)] at h
  have hprod : c.trace x * c.trace y = 0 := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        rintro rfl
        exact hab (by rw [ha, add_zero])
      rw [g.trace_eq_zero hb hy, mul_zero]
    · rw [g.trace_eq_zero ha hx, zero_mul]
  linear_combination hprod + h

/-- A nonzero homogeneous vector of degree `a` pairs to one with a vector of degree `-a`. -/
theorem exists_form_eq_one {a : M} {x : CayleyVector K} (hx : g.proj a *ᵥ x = x)
    (hx0 : x ≠ 0) : ∃ y, g.proj (-a) *ᵥ y = y ∧ c.form x y = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, c.form x w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (c.polar_nondegenerate x h)
  have hsum : c.form x w = c.form x (g.proj (-a) *ᵥ w) := by
    conv_lhs => rw [← g.sum_proj_mulVec w]
    rw [map_sum, Finset.sum_eq_single (-a)]
    · intro m _ hm
      refine g.form_eq_zero ?_ hx (g.proj_proj m w)
      intro h
      exact hm (neg_eq_of_add_eq_zero_right h).symm
    · intro ha
      rw [g.proj_eq_zero ha, Matrix.zero_mulVec, map_zero]
  refine ⟨(c.form x (g.proj (-a) *ᵥ w))⁻¹ • (g.proj (-a) *ᵥ w), ?_, ?_⟩
  · rw [Matrix.mulVec_smul, g.proj_proj]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (hsum ▸ hw)]

/-- Every degree in the support has a nonzero homogeneous vector. -/
theorem exists_ne_zero {m : M} (hm : m ∈ g.support) :
    ∃ x, g.proj m *ᵥ x = x ∧ x ≠ 0 := by
  have hne := (g.mem_support m).mp hm
  obtain ⟨i, j, hij⟩ : ∃ i j, g.proj m i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨g.proj m *ᵥ Pi.single j 1, g.proj_proj m _, fun h => hij ?_⟩
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun h i

/-- The support is symmetric. -/
theorem neg_mem_support {m : M} (hm : m ∈ g.support) : -m ∈ g.support := by
  obtain ⟨x, hx, hx0⟩ := g.exists_ne_zero hm
  obtain ⟨y, hy, hxy⟩ := g.exists_form_eq_one hx hx0
  by_contra h
  rw [g.eq_zero_of_not_mem hy h, map_zero] at hxy
  exact zero_ne_one hxy

theorem zero_mem_support : (0 : M) ∈ g.support := by
  by_contra h
  exact c.unit_ne_zero (g.eq_zero_of_not_mem g.proj_unit h)

/-- At most eight degrees occur. -/
theorem card_support_le : g.support.card ≤ 8 := by
  classical
  have hx : ∀ m : g.support, ∃ x, g.proj m *ᵥ x = x ∧ x ≠ 0 := fun m => g.exists_ne_zero m.2
  choose x hx hx0 using hx
  have hli : LinearIndependent K x := by
    rw [linearIndependent_iff']
    intro s r hr i hi
    have h := congrArg (g.proj i *ᵥ ·) hr
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_zero] at h
    rw [Finset.sum_eq_single i] at h
    · rw [hx i] at h
      exact (smul_eq_zero.mp h).resolve_right (hx0 i)
    · intro j _ hji
      rw [g.proj_mulVec_of_eq (hx j), if_neg (fun h => hji (Subtype.ext h).symm), smul_zero]
    · intro h
      exact absurd hi h
  have := hli.fintype_card_le_finrank
  simpa using this

/-- For two occurring degrees `a, b`, one of `b + a` and `b - a` occurs: this is the
linearized composition identity `x̄(yz) + ȳ(xz) = b(x, y) z`. -/
theorem add_mem_or_sub_mem {a b : M} (ha : a ∈ g.support) (hb : b ∈ g.support) :
    b + a ∈ g.support ∨ b - a ∈ g.support := by
  obtain ⟨x, hx, hx0⟩ := g.exists_ne_zero ha
  obtain ⟨y, hy, hxy⟩ := g.exists_form_eq_one hx hx0
  obtain ⟨z, hz, hz0⟩ := g.exists_ne_zero hb
  by_contra h
  push_neg at h
  have hxz : μ x z = 0 := g.mul_eq_zero_of_not_mem hx hz (by rw [add_comm]; exact h.1)
  have hyz : μ y z = 0 := g.mul_eq_zero_of_not_mem hy hz (by rw [neg_add_eq_sub]; exact h.2)
  have key := c.mul_mul_left₂ x y z
  rw [hxz, hyz, hxy, one_smul] at key
  simp only [smul_zero, map_zero, sub_self, add_zero] at key
  exact hz0 key.symm

end Grading

/-! ### Gradings by a lattice have rank at most two -/

section Rank

/-- Three vectors, each outside the span of the previous ones, are linearly independent. -/
theorem coeff_eq_zero_of_not_mem_span {V : Type w} [AddCommGroup V] [Module ℚ V] {x y z : V}
    (hx : x ≠ 0) (hy : y ∉ Submodule.span ℚ {x, x}) (hz : z ∉ Submodule.span ℚ {x, y})
    {r s t : ℚ} (h : r • x + s • y + t • z = 0) : r = 0 ∧ s = 0 ∧ t = 0 := by
  have ht : t = 0 := by
    by_contra ht
    apply hz
    have h1 : t • z = -(r • x + s • y) := eq_neg_of_add_eq_zero_right h
    have h2 : z = t⁻¹ • (t • z) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))))
  subst ht
  rw [zero_smul, add_zero] at h
  have hs : s = 0 := by
    by_contra hs
    apply hy
    have h1 : s • y = -(r • x) := eq_neg_of_add_eq_zero_right h
    have h2 : y = s⁻¹ • (s • y) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h2, h1]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  subst hs
  rw [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right hx, rfl, rfl⟩

variable {c} {I : Type w} [Fintype I] [DecidableEq I]

/-- **Rank bound.** A grading of a Cayley datum whose degrees generate the lattice `ℤ^I`
forces `|I| ≤ 2`. -/
theorem Grading.card_le_two (g : c.Grading (I → ℤ))
    (hgen : AddSubgroup.closure (g.support : Set (I → ℤ)) = ⊤) : Fintype.card I ≤ 2 := by
  classical
  let ρ : (I → ℤ) →+ (I → ℚ) := AddMonoidHom.compLeft (Int.castAddHom ℚ) I
  have hρ : ∀ (p q r : ℤ) (a b d : I → ℤ),
      ρ (p • a + q • b + r • d) = (p : ℚ) • ρ a + (q : ℚ) • ρ b + (r : ℚ) • ρ d := by
    intro p q r a b d
    funext i
    simp [ρ]
  obtain ⟨u, v, huv⟩ : ∃ u v : I → ℚ, ∀ m ∈ g.support, ρ m ∈ Submodule.span ℚ {u, v} := by
    by_contra hne
    push_neg at hne
    obtain ⟨a, ha, ha'⟩ := hne 0 0
    obtain ⟨b, hb, hb'⟩ := hne (ρ a) (ρ a)
    obtain ⟨d, hd, hd'⟩ := hne (ρ a) (ρ b)
    have ha0 : ρ a ≠ 0 := fun h => ha' (by rw [h]; exact Submodule.zero_mem _)
    let L : (Fin 3 → ℤ) → (I → ℤ) := fun p => p 0 • a + p 1 • b + p 2 • d
    have hL : Function.Injective L := by
      intro p q hpq
      have hdiff : (p 0 - q 0) • a + (p 1 - q 1) • b + (p 2 - q 2) • d = 0 := by
        have : (p 0 - q 0) • a + (p 1 - q 1) • b + (p 2 - q 2) • d = L p - L q := by
          simp only [L, sub_smul]
          abel
        rw [this, hpq, sub_self]
      have h := congrArg ρ hdiff
      rw [hρ, map_zero] at h
      obtain ⟨h0, h1, h2⟩ := coeff_eq_zero_of_not_mem_span ha0 hb' hd' h
      funext k
      fin_cases k
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h0)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h1)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h2)
    obtain ⟨σ, hσ, hbσ⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ σ • a + b ∈ g.support := by
      rcases g.add_mem_or_sub_mem ha hb with h | h
      · exact ⟨1, Or.inl rfl, by rwa [one_smul, add_comm]⟩
      · exact ⟨-1, Or.inr rfl, by rwa [neg_one_smul, neg_add_eq_sub]⟩
    let cs : Fin 9 → Fin 3 → ℤ := ![![0, 0, 0], ![1, 0, 0], ![-1, 0, 0], ![0, 1, 0],
      ![0, -1, 0], ![0, 0, 1], ![0, 0, -1], ![σ, 1, 0], ![-σ, -1, 0]]
    have hcs : Function.Injective cs := by
      rcases hσ with rfl | rfl <;> decide
    have hmem : ∀ k, L (cs k) ∈ g.support := by
      intro k
      fin_cases k
      · convert g.zero_mem_support using 1
        simp [L, cs]
      · convert ha using 1
        simp [L, cs]
      · convert g.neg_mem_support ha using 1
        simp [L, cs]
      · convert hb using 1
        simp [L, cs]
      · convert g.neg_mem_support hb using 1
        simp [L, cs]
      · convert hd using 1
        simp [L, cs]
      · convert g.neg_mem_support hd using 1
        simp [L, cs]
      · convert hbσ using 1
        simp [L, cs]
      · convert g.neg_mem_support hbσ using 1
        simp [L, cs]
        abel
    have hle : (Finset.univ : Finset (Fin 9)).card ≤ g.support.card :=
      Finset.card_le_card_of_injOn (fun k => L (cs k)) (by intro k _; exact hmem k)
        (by intro k₁ _ k₂ _ h; exact hcs (hL h))
    have := g.card_support_le
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hle : AddSubgroup.closure (g.support : Set (I → ℤ)) ≤
      (Submodule.span ℚ {u, v}).toAddSubgroup.comap ρ :=
    (AddSubgroup.closure_le _).mpr fun m hm => huv m hm
  rw [hgen] at hle
  have htop : Submodule.span ℚ {u, v} = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : ρ (Pi.single (M := fun _ : I => ℤ) i 1) ∈ Submodule.span ℚ {u, v} :=
      hle (AddSubgroup.mem_top (Pi.single (M := fun _ : I => ℤ) i 1))
    have heq : Pi.single i (w i) = w i • ρ (Pi.single (M := fun _ : I => ℤ) i 1) := by
      funext k
      by_cases hk : k = i
      · subst hk
        simp [ρ]
      · simp [ρ, Pi.single_apply, hk]
    rw [heq]
    exact Submodule.smul_mem _ _ hi
  have h1 := finrank_span_finset_le_card (R := ℚ) ({u, v} : Finset (I → ℚ))
  unfold Set.finrank at h1
  rw [Finset.coe_insert, Finset.coe_singleton, htop, finrank_top,
    Module.finrank_fintype_fun_eq_card] at h1
  exact h1.trans Finset.card_le_two

end Rank

end Langlands.GroupScheme.CayleyDatum
