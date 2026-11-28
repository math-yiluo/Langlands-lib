import Langlands.AlgebraicGeometry.DvrSmoothening.TorsionLength

/-! # The lattice comparison behind the defect drop under dilatation -/

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.DvrSmoothening

open Module Submodule

section Saturation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {F : Type*} [AddCommGroup F] [Module R F]

/-- If a combination of a finite family whose images in `k ⊗ F` are linearly independent lies in
`ϖ F`, then all its coefficients lie in the maximal ideal. -/
theorem coeff_mem_maximalIdeal {ι : Type*} [Fintype ι] {ϖ : R} (hϖ : Irreducible ϖ) (v : ι → F)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i))
    (c : ι → R) (y : F) (hc : ∑ i, c i • v i = ϖ • y) (i : ι) :
    c i ∈ IsLocalRing.maximalIdeal R := by
  let k := IsLocalRing.ResidueField R
  have h := congrArg (TensorProduct.mk R k F 1) hc
  simp only [map_sum, map_smul, TensorProduct.mk_apply] at h
  have hϖk : (ϖ • ((1 : k) ⊗ₜ[R] y)) = 0 := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff ϖ).mpr
        ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit), TensorProduct.zero_tmul]
  rw [hϖk] at h
  have h' : ∑ i, IsLocalRing.residue R (c i) • ((1 : k) ⊗ₜ[R] v i) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have := Fintype.linearIndependent_iff.mp hli _ h' i
  exact (IsLocalRing.residue_eq_zero_iff _).mp this

variable [Module.IsTorsionFree R F]

/-- Over a discrete valuation ring, the span of a finite family in a torsion-free module whose
images in `k ⊗ F` are linearly independent is saturated. -/
theorem mem_span_of_smul_mem_span {ι : Type*} [Fintype ι] {ϖ : R} (hϖ : Irreducible ϖ)
    (v : ι → F) (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i))
    (x : F) (hx : ϖ • x ∈ span R (Set.range v)) : x ∈ span R (Set.range v) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  have hm := coeff_mem_maximalIdeal hϖ v hli c x hc
  choose c' hc' using fun i => Ideal.mem_span_singleton'.mp (hϖ.maximalIdeal_eq ▸ hm i)
  have : ϖ • x = ϖ • ∑ i, c' i • v i := by
    rw [← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm, hc' i]
  rw [smul_right_injective F hϖ.ne_zero this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Over a discrete valuation ring, a finite family in a torsion-free module whose images in
`k ⊗ F` are linearly independent is linearly independent. -/
theorem linearIndependent_of_residue {ι : Type*} [Fintype ι] {ϖ : R} (hϖ : Irreducible ϖ)
    (v : ι → F) (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i)) :
    LinearIndependent R v := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ (k : ℕ) (c : ι → R), ∑ i, c i • v i = 0 →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal R ^ k := by
    intro k
    induction k with
    | zero => intro c _ i; simp
    | succ k ih =>
      intro c hc i
      have hm := coeff_mem_maximalIdeal hϖ v hli c 0 (by rw [hc, smul_zero])
      choose c' hc' using fun i => Ideal.mem_span_singleton'.mp (hϖ.maximalIdeal_eq ▸ hm i)
      have hc'0 : ∑ i, c' i • v i = 0 := by
        have h0 : ϖ • ∑ i, c' i • v i = ϖ • (0 : F) := by
          rw [smul_zero, Finset.smul_sum, ← hc]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm, hc' i]
        exact smul_right_injective F hϖ.ne_zero h0
      rw [← hc' i, pow_succ]
      exact Ideal.mul_mem_mul (ih c' hc'0 i)
        (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
  intro c hc i
  have hne : IsLocalRing.maximalIdeal R ≠ ⊤ := Ideal.IsPrime.ne_top'
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R) hne
  have hmem : c i ∈ ⨅ k : ℕ, IsLocalRing.maximalIdeal R ^ k :=
    Submodule.mem_iInf _ |>.mpr fun k => key k c hc i
  rw [this] at hmem
  exact hmem

end Saturation

section Core

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {FP F2 : Type*} [AddCommGroup FP] [Module R FP] [AddCommGroup F2] [Module R F2]
variable {σ : Type*} [Fintype σ] {n m : ℕ}

/-- The comparison map `θ₀ : F₂ → F_P` sending the basis vector `inl i` to `ϖ² bᵢ` and the basis
vector `inr j` to `ϖ dzⱼ`. -/
noncomputable def latticeMap (ϖ : R) (bP : Basis σ R FP) (b2 : Basis (σ ⊕ Fin n) R F2)
    (dz : Fin n → FP) : F2 →ₗ[R] FP :=
  b2.constr R (Sum.elim (fun i => ϖ ^ 2 • bP i) (fun j => ϖ • dz j))

omit [IsDomain R] [IsDiscreteValuationRing R] [Fintype σ] in
theorem latticeMap_basis (ϖ : R) (bP : Basis σ R FP) (b2 : Basis (σ ⊕ Fin n) R F2)
    (dz : Fin n → FP) (k : σ ⊕ Fin n) :
    latticeMap ϖ bP b2 dz (b2 k) = Sum.elim (fun i => ϖ ^ 2 • bP i) (fun j => ϖ • dz j) k :=
  b2.constr_basis R _ k

/-- **Comparison of two presentations.** Let `F_P` and `F₂` be free modules over a discrete
valuation ring with finite bases indexed by a finite type `σ` and by `σ ⊕ Fin n`, and
`α : F_P → F₂` a map sending the first basis to the `inl` part of the second. Let `dz, dw` be a family in `F_P` which is linearly
independent with saturated span. Let `N_P ⊆ F_P` contain the `dwₗ` and `N₂ ⊆ F₂` contain the
`α dwₗ` and the `α dzⱼ - ϖ eⱼ`. Suppose every element of `N_P` is `θ₀ y` modulo the `dwₗ` for some
`y ∈ N₂`, and every element of `N₂` becomes, after multiplication by a power of `ϖ`, of the form
`α x` with `x ∈ N_P` modulo the elements just listed. If `F_P ⧸ N_P` has non-zero torsion, then the
torsion of `F₂ ⧸ N₂` is strictly shorter. -/
theorem torsionLength_lt_of_presentations {ϖ : R} (hϖ : Irreducible ϖ)
    (bP : Basis σ R FP) (b2 : Basis (σ ⊕ Fin n) R F2) (α : FP →ₗ[R] F2)
    (hα : ∀ i, α (bP i) = b2 (Sum.inl i))
    (dz : Fin n → FP) (dw : Fin m → FP)
    (hli : LinearIndependent R (Sum.elim dz dw))
    (hsat : ∀ x, ϖ • x ∈ span R (Set.range (Sum.elim dz dw)) →
      x ∈ span R (Set.range (Sum.elim dz dw)))
    (NP : Submodule R FP) (N2 : Submodule R F2)
    (hwN : ∀ l, dw l ∈ NP) (hwN2 : ∀ l, α (dw l) ∈ N2)
    (hzN2 : ∀ j, α (dz j) - ϖ • b2 (Sum.inr j) ∈ N2)
    (hNP : ∀ x ∈ NP, ∃ y ∈ N2, x - latticeMap ϖ bP b2 dz y ∈ span R (Set.range dw))
    (hN2 : ∀ y ∈ N2, ∃ (v : ℕ) (x : FP), x ∈ NP ∧ ϖ ^ v • y - α x ∈
      span R (Set.range fun l => α (dw l)) ⊔
        span R (Set.range fun j => α (dz j) - ϖ • b2 (Sum.inr j)))
    (hT : torsion R (FP ⧸ NP) ≠ ⊥) :
    torsionLength R (F2 ⧸ N2) < torsionLength R (FP ⧸ NP) := by
  classical
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have : Module.Finite R FP := Module.Finite.of_basis bP
  have : Module.Free R FP := Module.Free.of_basis bP
  set θ0 := latticeMap ϖ bP b2 dz with hθ0def
  set W : Submodule R FP := span R (Set.range dw) with hWdef
  set W2 : Submodule R F2 := span R (Set.range fun l => α (dw l)) ⊔
    span R (Set.range fun j => α (dz j) - ϖ • b2 (Sum.inr j)) with hW2def
  set V : Submodule R FP := span R (Set.range (Sum.elim dz dw)) with hVdef
  have hθb : ∀ k, θ0 (b2 k) = Sum.elim (fun i => ϖ ^ 2 • bP i) (fun j => ϖ • dz j) k :=
    latticeMap_basis ϖ bP b2 dz
  have hθα : ∀ x, θ0 (α x) = ϖ ^ 2 • x := by
    intro x
    have : θ0 ∘ₗ α = ϖ ^ 2 • LinearMap.id := bP.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, hα, hθb, Sum.elim_inl,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    exact LinearMap.congr_fun this x
  have hθz : ∀ j, θ0 (α (dz j) - ϖ • b2 (Sum.inr j)) = 0 := by
    intro j
    rw [map_sub, map_smul, hθα, hθb, Sum.elim_inr, smul_smul, ← pow_two, sub_self]
  have hWN : W ≤ NP := span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hwN l)
  have hW2N : W2 ≤ N2 := sup_le (span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hwN2 l))
    (span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hzN2 j))
  have hθW : W2 ≤ W.comap θ0 := by
    refine sup_le (span_le.mpr ?_) (span_le.mpr ?_)
    · rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, mem_comap, hθα]
      exact W.smul_mem _ (subset_span ⟨l, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_comap, hθz]
      exact W.zero_mem
  have hWV : W ≤ V := span_mono (by rintro _ ⟨l, rfl⟩; exact ⟨Sum.inr l, rfl⟩)
  -- injectivity of `θ₀` modulo `W₂`
  have hinj : ∀ v, θ0 v ∈ W → v ∈ W2 := by
    intro v hv
    set c := b2.repr v
    set y : FP := ∑ i, c (Sum.inl i) • bP i with hy
    have hvdec : v = α y + ∑ j, c (Sum.inr j) • b2 (Sum.inr j) := by
      conv_lhs => rw [← b2.sum_repr v]
      rw [Fintype.sum_sum_type, hy, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hα]
    have hθv : θ0 v = ϖ ^ 2 • y + ∑ j, c (Sum.inr j) • ϖ • dz j := by
      rw [hvdec, map_add, hθα, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hθb, Sum.elim_inr]
    have hzV : ∀ j, dz j ∈ V := fun j => subset_span ⟨Sum.inl j, rfl⟩
    have hsumV : ∑ j, c (Sum.inr j) • ϖ • dz j ∈ V :=
      sum_mem fun j _ => V.smul_mem _ (V.smul_mem _ (hzV j))
    have hyV : y ∈ V := by
      have h2 : ϖ ^ 2 • y ∈ V := by
        have := hWV hv
        rw [hθv] at this
        simpa using V.sub_mem this hsumV
      rw [pow_two, mul_smul] at h2
      exact hsat _ (hsat _ h2)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hyV
    obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hv
    rw [Fintype.sum_sum_type] at ha
    simp only [Sum.elim_inl, Sum.elim_inr] at ha
    -- compare coefficients
    let g : Fin n ⊕ Fin m → R := Sum.elim (fun j => ϖ ^ 2 * a (Sum.inl j) + ϖ * c (Sum.inr j))
      (fun l => ϖ ^ 2 * a (Sum.inr l) - e l)
    have hg : ∑ k, g k • Sum.elim dz dw k = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [g, Sum.elim_inl, Sum.elim_inr, add_smul, sub_smul, mul_smul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h1 : θ0 v = ∑ l, e l • dw l := he.symm
      rw [hθv, ← ha] at h1
      rw [smul_add, Finset.smul_sum, Finset.smul_sum] at h1
      have h1' : ∑ j, c (Sum.inr j) • ϖ • dz j = ∑ j, ϖ • c (Sum.inr j) • dz j :=
        Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      rw [h1'] at h1
      rw [← sub_eq_zero] at h1
      rw [← h1]
      abel
    have hg0 := Fintype.linearIndependent_iff.mp hli g hg
    have hcz : ∀ j, c (Sum.inr j) = -(ϖ * a (Sum.inl j)) := by
      intro j
      have h := hg0 (Sum.inl j)
      simp only [g, Sum.elim_inl] at h
      have : ϖ * (ϖ * a (Sum.inl j) + c (Sum.inr j)) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hϖ0
      · exact eq_neg_of_add_eq_zero_right h'
    have hvW : v = ∑ j, a (Sum.inl j) • (α (dz j) - ϖ • b2 (Sum.inr j)) +
        ∑ l, a (Sum.inr l) • α (dw l) := by
      rw [hvdec, ← ha, map_add, map_sum, map_sum]
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib, hcz, neg_smul, Finset.sum_neg_distrib,
        smul_smul, mul_comm ϖ]
      abel
    rw [hvW]
    refine add_mem (sum_mem fun j _ => W2.smul_mem _ ?_) (sum_mem fun l _ => W2.smul_mem _ ?_)
    · exact mem_sup_right (subset_span ⟨j, rfl⟩)
    · exact mem_sup_left (subset_span ⟨l, rfl⟩)
  -- the quotient data
  let θ : F2 ⧸ W2 →ₗ[R] FP ⧸ W := W2.mapQ W θ0 hθW
  have hθmk : ∀ y, θ (W2.mkQ y) = W.mkQ (θ0 y) := fun y => rfl
  let N : Submodule R (FP ⧸ W) := NP.map W.mkQ
  let N' : Submodule R (F2 ⧸ W2) := N2.map W2.mkQ
  let e1 := quotientQuotientEquivQuotient W NP hWN
  let e2 := quotientQuotientEquivQuotient W2 N2 hW2N
  rw [← torsionLength_congr e1, ← torsionLength_congr e2]
  let θ1 : F2 →ₗ[R] FP := b2.constr R (Sum.elim (fun i => ϖ • bP i) dz)
  have hθ01 : θ0 = ϖ • θ1 := b2.ext fun k => by
    rcases k with i | j
    · simp [θ1, hθb, pow_two, mul_smul]
    · simp [θ1, hθb]
  refine torsionLength_lt_of_lattice hϖ θ ?_ N N' ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨x0, rfl⟩ := W2.mkQ_surjective x
    refine ⟨W.mkQ (θ1 x0), ?_⟩
    rw [hθmk, hθ01, LinearMap.smul_apply, map_smul]
  · rw [map_le_iff_le_comap]
    intro x hx
    obtain ⟨y, hyN, hxy⟩ := hNP x hx
    refine ⟨W2.mkQ y, ?_⟩
    rw [hθmk]
    exact ((Submodule.Quotient.eq W).mpr hxy).symm
  · intro x' hx'
    obtain ⟨y', rfl⟩ := W2.mkQ_surjective x'
    rw [mem_comap, hθmk] at hx'
    obtain ⟨x, hxN, hx⟩ := hx'
    have hdiff : x - θ0 y' ∈ W := (Submodule.Quotient.eq W).mp hx
    obtain ⟨y, hyN, hxy⟩ := hNP x hxN
    have : y' - y ∈ W2 := hinj _ (by
      rw [map_sub]
      have := W.sub_mem hxy hdiff
      rwa [sub_sub_sub_cancel_left] at this)
    refine ⟨y, hyN, ?_⟩
    exact ((Submodule.Quotient.eq W2).mpr this).symm
  · intro x hx
    obtain ⟨y, hyN, rfl⟩ := hx
    obtain ⟨v, x0, hx0, hv⟩ := hN2 y hyN
    refine ⟨v, ?_⟩
    rw [mem_comap, ← map_smul]
    have : W2.mkQ (ϖ ^ v • y) = W2.mkQ (α x0) := (Submodule.Quotient.eq W2).mpr hv
    rw [this, hθmk, hθα]
    exact mem_map_of_mem (NP.smul_mem _ hx0)
  · intro hbot
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have h := mem_torsion_map (f := e1.symm.toLinearMap) ht
    rw [hbot, mem_bot] at h
    rw [mem_bot]
    simpa using congrArg e1 h

end Core

end Langlands.AlgebraicGeometry.DvrSmoothening
