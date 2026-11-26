import Langlands.BushnellKutzko.NormalizedLevelTwistProof

/-! # Determinants of intersections of filtered unit groups -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- The determinant congruence for a positive unit level in an arbitrary vector space. -/
theorem det_unitFiltration_congr (L : LatticeChain 𝒪[F] F V) (m : ℕ)
    {g : (Module.End F V)ˣ} (hg : g ∈ L.unitFiltration (m + 1)) :
    ∃ a : 𝒪[F], a ∈ 𝓂[F] ^ (m / L.period + 1) ∧
      LinearMap.det (g : Module.End F V) = 1 + (a : F) := by
  let := L.finiteDimensional
  let f := (Module.finBasis F V).equivFun
  let C := L.linearEquivMap f
  have hperiod : C.period = L.period := by
    symm
    apply C.period_unique
    intro i
    change ((L.lattice (i + L.period)).map _) =
      Ring.jacobson 𝒪[F] • ((L.lattice i).map (f.toLinearMap.restrictScalars 𝒪[F]))
    rw [L.lattice_add_period, Submodule.map_smul'']
  let x := (g : Module.End F V) - 1
  have hbound : (C.period : ℤ) * (m / L.period : ℕ) + 1 ≤ ((m + 1 : ℕ) : ℤ) := by
    have h : C.period * (m / L.period) + 1 ≤ m + 1 := by
      rw [hperiod, mul_comm L.period]
      exact Nat.succ_le_succ (Nat.div_mul_le_self m L.period)
    exact_mod_cast h
  have hx : x ∈ L.endFiltration ((C.period : ℤ) * (m / L.period : ℕ) + 1) :=
    L.endFiltration_antitone hbound hg.2.2
  have hy : f.conjRingEquiv x ∈ C.endFiltration ((C.period : ℤ) * (m / L.period : ℕ) + 1) := by
    intro i v hv
    rw [L.mem_linearEquivMap] at hv ⊢
    change f.symm (f (x (f.symm v))) ∈ L.lattice _
    simpa using hx i (f.symm v) hv
  obtain ⟨a, ha, hdet⟩ := C.exists_det_one_add_eq (m / L.period) hy
  refine ⟨a, ha, ?_⟩
  rw [← map_one f.conjRingEquiv, ← map_add] at hdet
  change LinearMap.det (f.toLinearMap ∘ₗ (1 + x) ∘ₗ f.symm.toLinearMap) = _ at hdet
  rwa [LinearMap.det_conj, show 1 + x = (g : Module.End F V) by simp [x]] at hdet

/-- Two lattice chains on the same space have a common nonempty finite splitting basis. -/
theorem exists_common_splitting_basis (L M : LatticeChain 𝒪[F] F V)
    {π : 𝒪[F]} (hπ : Irreducible π) :
    ∃ (r : ℕ) (b : Module.Basis (Fin r) F V), Nonempty (Fin r) ∧ L.Splits b ∧ M.Splits b := by
  obtain ⟨s, c, hc⟩ := M.exists_basis_splits hπ
  obtain ⟨r, b, hbL, hbM⟩ := L.exists_basis_splits_of_splits hπ M c hc
  have hb : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Subsingleton V := b.equivFun.injective.subsingleton
    exact (L.lattice_succ_lt 0).ne (Subsingleton.elim _ _)
  exact ⟨r, b, hb, hbL, hbM⟩

private theorem smul_projection_mem_endFiltration (L : LatticeChain 𝒪[F] F V)
    {r : ℕ} {b : Module.Basis (Fin r) F V} (hb : L.Splits b) (j : Fin r)
    {π : 𝒪[F]} (hπ : Irreducible π) (d : ℕ) {a : 𝒪[F]} (ha : a ∈ 𝓂[F] ^ d) :
    (a : F) • (b.coord j).smulRight (b j) ∈ L.endFiltration ((L.period : ℤ) * d) := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨t, ht⟩ := ha
  intro i v hv
  have hproj : b.repr v j • b j ∈ L.lattice i :=
    hb (fun k => b.repr v k) i (by rwa [b.sum_repr]) j
  rw [LinearMap.smul_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply, ht]
  change ((π : F) ^ d * (t : F)) • (b.repr v j • b j) ∈ L.lattice _
  rw [mul_smul, ← zpow_natCast, L.zpow_smul_mem_iff hπ, add_sub_cancel_right]
  exact (L.lattice i).smul_mem t hproj

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem det_one_add_smul_projection {r : ℕ} (b : Module.Basis (Fin r) F V)
    (j : Fin r) (a : F) :
    LinearMap.det (1 + a • (b.coord j).smulRight (b j)) = 1 + a := by
  classical
  let d : Fin r → F := fun i => if i = j then 1 + a else 1
  have hM : LinearMap.toMatrix b b (1 + a • (b.coord j).smulRight (b j)) =
      Matrix.diagonal d := by
    ext i k
    rw [LinearMap.toMatrix_apply]
    by_cases hkj : k = j
    · subst k
      by_cases hij : i = j
      · subst i
        simp [d]
      · simp [d, hij]
    · by_cases hik : i = k
      · subst i
        simp [d, hkj, Ne.symm hkj]
      · simp [d, hik, Ne.symm hkj]
  rw [← LinearMap.det_toMatrix b, hM, Matrix.det_diagonal]
  simp [d]

/-- Every principal unit at the common normalized level is the determinant of an element
in the intersection of the two filtered unit groups. -/
theorem exists_mem_inf_unitFiltration_det_eq (L M : LatticeChain 𝒪[F] F V)
    (m₁ m₂ : ℕ) (hm : m₁ / L.period = m₂ / M.period) {a : 𝒪[F]}
    (ha : a ∈ 𝓂[F] ^ (m₁ / L.period + 1)) :
    ∃ g ∈ L.unitFiltration (m₁ + 1) ⊓ M.unitFiltration (m₂ + 1),
      LinearMap.det (g : Module.End F V) = 1 + (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨r, b, ⟨j⟩, hbL, hbM⟩ := exists_common_splitting_basis L M hπ
  let x : Module.End F V := (a : F) • (b.coord j).smulRight (b j)
  have hshift (N : LatticeChain 𝒪[F] F V) (hN : N.Splits b) (m : ℕ)
      (haN : a ∈ 𝓂[F] ^ (m / N.period + 1)) : x ∈ N.endFiltration (m + 1 : ℕ) := by
    have hx := smul_projection_mem_endFiltration N hN j hπ (m / N.period + 1) haN
    have hlt : m < N.period * (m / N.period + 1) := by
      rw [Nat.mul_add, mul_one, mul_comm N.period]
      exact Nat.lt_div_mul_add N.period_pos
    exact N.endFiltration_antitone (by exact_mod_cast Nat.succ_le_of_lt hlt) hx
  obtain ⟨g, hg, hval⟩ := L.exists_mem_unitFiltration (by omega) (hshift L hbL m₁ ha)
  obtain ⟨g', hg', hval'⟩ := M.exists_mem_unitFiltration (by omega) (hshift M hbM m₂ (hm ▸ ha))
  have hgg' : g = g' := Units.ext (hval.trans hval'.symm)
  exact ⟨g, ⟨hg, hgg' ▸ hg'⟩, hval ▸ det_one_add_smul_projection b j (a : F)⟩

/-- The determinant image of the intersection of two filtered unit groups at the same
normalized level `m₁ / e₁ = m₂ / e₂` is the corresponding principal-unit group. -/
theorem det_image_inf_unitFiltration (L M : LatticeChain 𝒪[F] F V)
    (m₁ m₂ : ℕ) (hm : m₁ / L.period = m₂ / M.period) :
    (fun g : (Module.End F V)ˣ => LinearMap.det (g : Module.End F V)) ''
      ((L.unitFiltration (m₁ + 1) ⊓ M.unitFiltration (m₂ + 1) :
        Subgroup (Module.End F V)ˣ) : Set (Module.End F V)ˣ) =
      {u | ∃ a : 𝒪[F], a ∈ 𝓂[F] ^ (m₁ / L.period + 1) ∧ u = 1 + (a : F)} := by
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact L.det_unitFiltration_congr m₁ ((Subgroup.mem_inf.mp hg).1)
  · rintro ⟨a, ha, rfl⟩
    exact L.exists_mem_inf_unitFiltration_det_eq M m₁ m₂ hm ha

end Langlands.BushnellKutzko.LatticeChain
