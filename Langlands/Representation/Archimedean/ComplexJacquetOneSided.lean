import Langlands.Representation.Archimedean.ComplexJacquetFinite

/-!
# Nonvanishing of the Jacquet module from one-sided nonvanishing

Through `𝔤𝔩_n(ℂ) ⊗_ℝ ℂ ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module
carries two commuting `𝔤𝔩_n`-actions `E^{(0)}_pq = ee π 0 p q` and `E^{(1)}_pq = ee π 1 p q`. The
Jacquet subspace `𝔫V` is contained in `𝔫^{(0)} V + 𝔫^{(1)} V`, where `𝔫^{(i)} V` is spanned by the
vectors `E^{(i)}_pq v` with `p < q`.

`ComplexJacquetOneSidedStatement` asserts `𝔫^{(0)} V ≠ V`. The main theorem
`ComplexJacquetFinite.jacquet_ne_top_of_sideJacquet_ne_top` shows that it implies `𝔫V ≠ V`. The
converse is immediate from `𝔫^{(0)} V ⊆ 𝔫V`, so the one-sided statement is equivalent to
`ComplexJacquetModuleNonzeroStatement` (`complexJacquetModuleNonzero_iff_oneSided`).

Proof idea: on `Q = V / 𝔫^{(0)} V` let `T = -∑_a a E^{(1)}_aa`, so that `E^{(1)}_pq` with `p < q`
raises generalized `T`-eigenvalues by `q - p > 0`. A finite-dimensional `T`-stable subspace `Y`
of `Q` comes from the Gelfand relations of the first factor. Take the eigenvalue `μ₀` of `T` on
`Y` with minimal real part. The generalized eigenspaces of real part `≥ Re μ₀` fill `Q`, while
`𝔫^{(1)} V` lands in those of real part `> Re μ₀`. Hence `𝔫V = V` would kill a `μ₀`-eigenvector.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexJacquetFinite

open MvPolynomial ComplexGenericLarge

/-! ## One-sided Jacquet subspaces -/

section Side

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- `𝔫^{(i)} V`, the span of the vectors `E^{(i)}_pq v` with `p < q`. -/
def sideJacquet (i : Fin 2) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), p < q ∧ ee π i p q v = w}

theorem ee_mem_sideJacquet (i : Fin 2) {p q : Fin n} (hpq : p < q) (v : V) :
    ee π i p q v ∈ sideJacquet π i :=
  Submodule.subset_span ⟨p, q, v, hpq, rfl⟩

/-- `𝔫^{(i)} V ⊆ 𝔫V`. -/
theorem sideJacquet_le (i : Fin 2) : sideJacquet π i ≤ complexJacquetSubspace n π :=
  Submodule.span_le.2 fun _ ⟨p, q, v, hpq, h⟩ => h ▸ ee_up π i p q hpq v

theorem unitPair_mul_of_ne {i j : Fin 2} (hij : i ≠ j) (a b c d : Fin n) :
    unitPair i a b * unitPair j c d = 0 := by
  funext t
  simp only [Pi.mul_apply, Pi.zero_apply, unitPair]
  by_cases ht : t = i
  · subst ht
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · rw [Pi.single_eq_of_ne ht, zero_mul]

/-- The two factors commute. -/
theorem commute_ee_of_ne {i j : Fin 2} (hij : i ≠ j) (a b c d : Fin n) :
    Commute (ee π i a b) (ee π j c d) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  simp only [ee]
  rw [prodAction_mul_sub, unitPair_mul_of_ne hij, unitPair_mul_of_ne hij.symm, sub_zero,
    map_zero]

/-- `𝔫^{(i)} V` is stable under the diagonal `E^{(i)}_aa`. -/
theorem sideJacquet_diag (i : Fin 2) (a : Fin n) :
    ∀ w ∈ sideJacquet π i, ee π i a a w ∈ sideJacquet π i := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, v, hpq, rfl⟩ := hx
    have h := LinearMap.congr_fun (isGlFamily_ee π i a a p q) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have h' : ee π i a a (ee π i p q v) = ee π i p q (ee π i a a v) +
        ((if a = p then ee π i a q else 0) v - (if q = a then ee π i p a else 0) v) := by
      rw [← h]; abel
    rw [h']
    refine Submodule.add_mem _ (ee_mem_sideJacquet π i hpq _) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs with hap
      · subst hap; exact ee_mem_sideJacquet π i hpq v
      · simp
    · split_ifs with hqa
      · subst hqa; exact ee_mem_sideJacquet π i hpq v
      · simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- `𝔫^{(i)} V` is stable under the other factor. -/
theorem sideJacquet_other {i j : Fin 2} (hij : i ≠ j) (a b : Fin n) :
    ∀ w ∈ sideJacquet π i, ee π j a b w ∈ sideJacquet π i := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, v, hpq, rfl⟩ := hx
    rw [← Module.End.mul_apply, (commute_ee_of_ne π hij.symm a b p q).eq, Module.End.mul_apply]
    exact ee_mem_sideJacquet π i hpq _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- `prodAction π Y = ∑ Y^{(i)}_pq E^{(i)}_pq`. -/
theorem prodAction_eq_sum (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    prodAction π Y = ∑ i, ∑ p, ∑ q, Y i p q • ee π i p q := by
  have hY : Y = ∑ i, ∑ p, ∑ q, Y i p q • unitPair i p q := by
    funext t
    rw [Finset.sum_apply, Fin.sum_univ_two]
    fin_cases t
    · simp only [Finset.sum_apply, unitPair, Pi.smul_apply, Fin.zero_eta, Pi.single_eq_same,
        Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_zero, Finset.sum_const_zero,
        add_zero, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (Y 0)
    · simp only [Finset.sum_apply, unitPair, Pi.smul_apply, Fin.mk_one, Pi.single_eq_same,
        Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_zero, Finset.sum_const_zero,
        zero_add, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (Y 1)
  conv_lhs => rw [hY]
  simp only [map_sum, map_smul, ee]

/-- `π(1 ⊗ X) = ∑ (X_pq E^{(0)}_pq + X̄_pq E^{(1)}_pq)`. -/
theorem pi_eq_sum (X : Matrix (Fin n) (Fin n) ℂ) :
    π ((1 : ℂ) ⊗ₜ[ℝ] X) =
      ∑ p, ∑ q, (X p q • ee π 0 p q + starRingEnd ℂ (X p q) • ee π 1 p q) := by
  rw [← tensorEquiv_symm_pairHom, ← prodAction_apply, prodAction_eq_sum, Fin.sum_univ_two]
  simp only [pairHom_zero, pairHom_one, conjMat_apply, ← Finset.sum_add_distrib]

/-- `𝔫V ⊆ 𝔫^{(0)} V + 𝔫^{(1)} V`. -/
theorem complexJacquetSubspace_le_sup :
    complexJacquetSubspace n π ≤ sideJacquet π 0 ⊔ sideJacquet π 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨X, v, hX, rfl⟩
  rw [pi_eq_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  by_cases hpq : p < q
  · exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (ee_mem_sideJacquet π 0 hpq v))
      (Submodule.smul_mem _ _ (ee_mem_sideJacquet π 1 hpq v))
  · rw [hX p q (Fin.le_iff_val_le_val.1 (not_lt.1 hpq))]
    simp

/-- A subspace stable under every `E^{(i)}_pq`, `p ≤ q`, is stable under `π(1 ⊗ X)` for upper
triangular `X`. -/
theorem upper_stable_of_ee (S : Submodule ℂ V)
    (hS : ∀ i p q, p ≤ q → ∀ s ∈ S, ee π i p q s ∈ S) :
    ∀ X, Upper X → ∀ s ∈ S, π ((1 : ℂ) ⊗ₜ[ℝ] X) s ∈ S := by
  intro X hX s hs
  rw [pi_eq_sum, LinearMap.sum_apply]
  refine S.sum_mem fun p _ => ?_
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun q _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  by_cases hpq : p ≤ q
  · exact S.add_mem (S.smul_mem _ (hS 0 p q hpq s hs)) (S.smul_mem _ (hS 1 p q hpq s hs))
  · rw [hX p q (not_le.1 hpq)]
    simp

/-! ## Polynomial relations of one factor modulo a subspace -/

/-- Polynomials in the diagonal generators of the factor `i`. -/
def sideAct (i : Fin 2) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (diagAct π).comp (rename fun a : Fin n => (i, a))

theorem sideAct_X (i : Fin 2) (a : Fin n) : sideAct π i (X a) = ee π i a a := by
  simp [sideAct, diagAct_X, diagGen]

theorem sideAct_comm (i : Fin 2) (f : MvPolynomial (Fin n) ℂ) (s : Fin 2 × Fin n) (v : V) :
    diagGen π s (sideAct π i f v) = sideAct π i f (diagGen π s v) := by
  rw [← diagAct_X]
  simp only [sideAct, AlgHom.comp_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

/-- The polynomials `f` with `ψ_i(f) V ⊆ N`. -/
def sideAnn (i : Fin 2) (N : Submodule ℂ V) : Ideal (MvPolynomial (Fin n) ℂ) where
  carrier := {f | ∀ v, sideAct π i f v ∈ N}
  add_mem' {f g} hf hg v := by
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem (hf v) (hg v)
  zero_mem' v := by simp
  smul_mem' c f hf v := by
    rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
    exact hf _

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

theorem side_psum_close (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (i : Fin 2) (N : Submodule ℂ V)
    (hup : ∀ a b : Fin n, a < b → ∀ v, ee π i a b v ∈ N)
    (hdiag : ∀ a, ∀ v ∈ N, ee π i a a v ∈ N) :
    ∀ b, 1 ≤ b → b ≤ n → Close (sideAnn π i N) (psum (Fin n) ℂ b) (b - 1) := by
  intro b hb _
  obtain ⟨c, hc⟩ := trace_scalar π hgk hirr hadm i b
  refine ⟨psum (Fin n) ℂ b - (∑ a, gelPoly n b a - C c), ?_, ?_⟩
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h : psum (Fin n) ℂ (b' + 1) - (∑ a, gelPoly n (b' + 1) a - C c) =
        -(∑ a, (gelPoly n (b' + 1) a - X a ^ (b' + 1))) + C c := by
      rw [MvPolynomial.psum, Finset.sum_sub_distrib]
      ring
    rw [h]
    refine (totalDegree_add _ _).trans (max_le ?_ ((totalDegree_C _).trans_le (Nat.zero_le _)))
    rw [totalDegree_neg]
    exact (totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun a _ => (totalDegree_gelPoly_sub b' a).trans (by omega))
  · rw [sub_sub_cancel]
    intro v
    have hsum := Submodule.sum_mem N (t := Finset.univ) fun a _ =>
      diag_pow N (isGlFamily_ee π i) hup hdiag (sideAct π i) (sideAct_X π i) b a v
    rw [Finset.sum_sub_distrib, hc] at hsum
    have heq : sideAct π i (∑ a, gelPoly n b a - C c) v =
        -(c • v - ∑ a, sideAct π i (gelPoly n b a) v) := by
      rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, MvPolynomial.algHom_C,
        Module.algebraMap_end_apply, neg_sub]
    rw [heq]
    exact N.neg_mem hsum

/-- The image of `W` under the box monomials in the diagonal generators of the factor `i`. -/
def sideBox (i : Fin 2) (W : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ α : boxSet (Fin n) n, W.map (sideAct π i (monomial (α : Fin n →₀ ℕ) 1))

theorem finiteDimensional_sideBox (i : Fin 2) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (sideBox π i W) := by
  unfold sideBox
  infer_instance

theorem sideAct_mem_sideBox_sup (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) (i : Fin 2)
    (N : Submodule ℂ V) (hup : ∀ a b : Fin n, a < b → ∀ v, ee π i a b v ∈ N)
    (hdiag : ∀ a, ∀ v ∈ N, ee π i a a v ∈ N) (W : Submodule ℂ V)
    (f : MvPolynomial (Fin n) ℂ) {w : V} (hw : w ∈ W) :
    sideAct π i f w ∈ sideBox π i W ⊔ N := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1
    (mem_boxSpan_sup (sideAnn π i N) (fun a => a.pos)
      (fun a => xpow_close (side_psum_close π hgk hirr hadm i N hup hdiag) a) f)
  rw [map_add, LinearMap.add_apply]
  refine Submodule.add_mem_sup ?_ (hz w)
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    exact Submodule.mem_iSup_of_mem (⟨α, hα⟩ : boxSet (Fin n) n)
      (Submodule.mem_map_of_mem hw)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ c hx

end Side

/-! ## Generalized eigenspaces -/

section Eigen

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- If `[T, R] = h R`, then `R` maps the generalized `μ`-eigenspace of `T` into the generalized
`(μ + h)`-eigenspace. -/
theorem mem_maxGenEigenspace_shift (T R : Module.End ℂ M) (h : ℂ)
    (hTR : ∀ x, T (R x) = R (T x) + h • R x) (μ : ℂ) {x : M}
    (hx : x ∈ T.maxGenEigenspace μ) : R x ∈ T.maxGenEigenspace (μ + h) := by
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  have hs : SemiconjBy R (T - μ • 1) (T - (μ + h) • 1) := by
    refine LinearMap.ext fun y => ?_
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, hTR, add_smul, LinearMap.add_apply]
    abel
  rw [← Module.End.mul_apply, ← (hs.pow_right k).eq, Module.End.mul_apply, hk, map_zero]

/-- A map sending each `F μ` with `s μ` into `G (g μ)` with `t (g μ)` maps `⨆_{s μ} F μ` into
`⨆_{t μ} G μ`. -/
theorem mem_iSup_of_maps (A : Module.End ℂ M) (F G : ℂ → Submodule ℂ M) (s t : ℂ → Prop)
    (g : ℂ → ℂ) (hst : ∀ μ, s μ → t (g μ)) (hA : ∀ μ, ∀ x ∈ F μ, A x ∈ G (g μ)) {x : M}
    (hx : x ∈ ⨆ (μ) (_ : s μ), F μ) : A x ∈ ⨆ (μ) (_ : t μ), G μ := by
  have hle : (⨆ (μ) (_ : s μ), F μ).map A ≤ ⨆ (μ) (_ : t μ), G μ := by
    simp only [Submodule.map_iSup]
    refine iSup₂_le fun μ hμ => le_trans ?_ (le_iSup₂_of_le (g μ) (hst μ hμ) le_rfl)
    rw [Submodule.map_le_iff_le_comap]
    exact fun y hy => hA μ y hy
  exact hle (Submodule.mem_map_of_mem hx)

end Eigen

/-! ## Operators on a quotient -/

section Quot

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M)

theorem mapQ_commute {A B : Module.End ℂ M} (hA : N ≤ N.comap A) (hB : N ≤ N.comap B)
    (h : Commute A B) : Commute (N.mapQ N A hA) (N.mapQ N B hB) := by
  rw [Commute, SemiconjBy]
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := N.mkQ_surjective x
  simp only [Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
  rw [← Module.End.mul_apply A B, h.eq, Module.End.mul_apply]

theorem mapQ_shift {T R : Module.End ℂ M} (hT : N ≤ N.comap T) (hR : N ≤ N.comap R) (h : ℂ)
    (hTR : ∀ x, T (R x) = R (T x) + h • R x) (x : M ⧸ N) :
    N.mapQ N T hT (N.mapQ N R hR x) =
      N.mapQ N R hR (N.mapQ N T hT x) + h • N.mapQ N R hR x := by
  obtain ⟨v, rfl⟩ := N.mkQ_surjective x
  simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, hTR, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]

end Quot

/-! ## The reduction -/

section Reduction

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The weight operator `T = -∑_a a E^{(1)}_aa`. -/
def weightOp (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Module.End ℂ V :=
  ∑ a : Fin n, (-((a : ℕ) : ℂ)) • ee π 1 a a

variable (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- `[T, E^{(1)}_pq] = (q - p) E^{(1)}_pq`. -/
theorem weightOp_comm (p q : Fin n) :
    weightOp π * ee π 1 p q - ee π 1 p q * weightOp π =
      (((q : ℕ) : ℂ) - ((p : ℕ) : ℂ)) • ee π 1 p q := by
  simp only [weightOp, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, smul_mul_assoc,
    mul_smul_comm, ← smul_sub, isGlFamily_ee π 1 _ _ p q]
  simp only [smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← sub_smul]
  congr 1
  ring

theorem weightOp_commute (i : Fin 2) (a : Fin n) : Commute (weightOp π) (ee π i a a) := by
  refine Commute.sum_left _ _ _ fun b _ => ?_
  exact (commute_ee π 1 i b a).smul_left _

theorem weightOp_ee_apply (p q : Fin n) (x : V) :
    weightOp π (ee π 1 p q x) =
      ee π 1 p q (weightOp π x) + (((q : ℕ) : ℂ) - ((p : ℕ) : ℂ)) • ee π 1 p q x := by
  have h := LinearMap.congr_fun (weightOp_comm π p q) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [← h]
  abel

theorem weightOp_mem_sideJacquet : ∀ w ∈ sideJacquet π 0, weightOp π w ∈ sideJacquet π 0 := by
  intro w hw
  rw [weightOp, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (sideJacquet_other π (by decide) a a w hw)

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

/-- On a `U(n)`-stable subspace, `E^{(0)}_aa - E^{(1)}_aa = -i π(1 ⊗ i E_aa)` acts. -/
theorem diag_sub_mem (hgk : IsComplexGKModule n ρ π) (W : Submodule ℂ V)
    (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W) (a : Fin n) {w : V} (hw : w ∈ W) :
    ee π 0 a a w - ee π 1 a a w ∈ W := by
  have hY : star (Matrix.single a a Complex.I) = -Matrix.single a a Complex.I := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, Complex.star_def,
      Complex.conj_I, Matrix.single_neg]
  have h := skew_stable hgk W hWK _ hY w hw
  rw [pi_single_diag_eq] at h
  have he : diagAct π (C Complex.I * X (0, a) + C (starRingEnd ℂ Complex.I) * X (1, a)) w =
      Complex.I • (ee π 0 a a w - ee π 1 a a w) := by
    simp only [map_add, map_mul, MvPolynomial.algHom_C, diagAct_X, diagGen, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Complex.conj_I, neg_smul, smul_sub]
    abel
  rw [he] at h
  have h' := W.smul_mem (-Complex.I) h
  rwa [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] at h'

/-- The span of the vectors `ψ_0(f) w`, `w ∈ W`. -/
def sideSpan (W : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ f, ∃ w ∈ W, u = sideAct π 0 f w}

theorem le_sideSpan (W : Submodule ℂ V) : W ≤ sideSpan π W :=
  fun w hw => Submodule.subset_span ⟨1, w, hw, by simp⟩

theorem ee_one_mem_sideSpan (hgk : IsComplexGKModule n ρ π) (W : Submodule ℂ V)
    (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W) (a : Fin n) {u : V} (hu : u ∈ sideSpan π W) :
    ee π 1 a a u ∈ sideSpan π W := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, w, hw, rfl⟩ := hx
    have h1 : ee π 1 a a (sideAct π 0 f w) = sideAct π 0 (f * X a) w -
        sideAct π 0 f (ee π 0 a a w - ee π 1 a a w) := by
      have hc := sideAct_comm π 0 f (1, a) w
      simp only [diagGen] at hc
      rw [hc, map_sub, map_mul, Module.End.mul_apply, sideAct_X]
      abel
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨f * X a, w, hw, rfl⟩)
      (Submodule.subset_span ⟨f, _, diag_sub_mem π hgk W hWK a hw, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- **Reduction to one side.** If `𝔫^{(0)} V ≠ V`, then `𝔫V ≠ V`. -/
theorem jacquet_ne_top_of_sideJacquet_ne_top (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ)
    (hOS : sideJacquet π 0 ≠ ⊤) : complexJacquetSubspace n π ≠ ⊤ := by
  classical
  set N := sideJacquet π 0 with hNdef
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hup : ∀ a b : Fin n, a < b → ∀ v, ee π 0 a b v ∈ N := fun a b hab v =>
    ee_mem_sideJacquet π 0 hab v
  have hdiag : ∀ a, ∀ v ∈ N, ee π 0 a a v ∈ N := sideJacquet_diag π 0
  have hother : ∀ a b, ∀ v ∈ N, ee π 1 a b v ∈ N := sideJacquet_other π h01
  -- `W`: the `U(n)`-span of a nonzero vector
  have := hirr.1
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  set W := FiniteVectors.orbitSpan ρ v₀ with hWdef
  have hWfin : FiniteDimensional ℂ W := hgk.1 v₀
  have hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W := fun k w hw =>
    (FiniteVectors.orbitSubrepresentation ρ v₀).apply_mem_toSubmodule k hw
  have hW0 : W ≠ ⊥ := fun h => hv₀ ((Submodule.mem_bot ℂ).1
    (h ▸ FiniteVectors.self_mem_orbitSpan ρ v₀))
  have hWtop := upperClosure_eq_top π hgk hirr W hWK (skew_stable hgk W hWK) hW0
  -- a subspace containing `W` and stable under the upper triangular directions is `V`
  have hfill : ∀ S : Submodule ℂ V, W ≤ S →
      (∀ i p q, p ≤ q → ∀ s ∈ S, ee π i p q s ∈ S) → S = ⊤ := by
    intro S hWS hS
    rw [eq_top_iff, ← hWtop]
    exact upperClosure_le π W S hWS (upper_stable_of_ee π S hS)
  -- the finite-dimensional `T`-stable subspace `Y` of `Q = V / 𝔫^{(0)} V`
  set D := sideSpan π W with hDdef
  have hNT : N ≤ N.comap (weightOp π) := fun v hv => weightOp_mem_sideJacquet π v hv
  set TQ : Module.End ℂ (V ⧸ N) := N.mapQ N (weightOp π) hNT with hTQdef
  set Y := D.map N.mkQ with hYdef
  have hYT : ∀ y ∈ Y, TQ y ∈ Y := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨weightOp π u, ?_, by simp [hTQdef]⟩
    rw [weightOp, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (ee_one_mem_sideSpan π hgk W hWK a hu)
  have hYfin : FiniteDimensional ℂ Y := by
    have hDle : D ≤ sideBox π 0 W ⊔ N := Submodule.span_le.2 (by
      rintro _ ⟨f, w, hw, rfl⟩
      exact sideAct_mem_sideBox_sup π hgk hirr hadm 0 N hup hdiag W f hw)
    have hle : Y ≤ (sideBox π 0 W).map N.mkQ := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hDle hu)
      refine ⟨y, hy, ?_⟩
      simp [(Submodule.Quotient.mk_eq_zero _).2 hz]
    have := finiteDimensional_sideBox π 0 W
    exact Submodule.finiteDimensional_of_le hle
  have hY0 : Y ≠ ⊥ := by
    intro hY
    apply hOS
    refine hfill N (fun w hw => ?_) ?_
    · have h : N.mkQ w ∈ Y := ⟨w, le_sideSpan π W hw, rfl⟩
      rw [hY, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      exact h
    · intro i p q hpq s hs
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · rcases hpq.lt_or_eq with h | rfl
        · exact hup p q h s
        · exact hdiag p s hs
      · exact hother p q s hs
  have : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY0
  set TY : Module.End ℂ Y := TQ.restrict hYT with hTYdef
  have hres : ∀ μ, TY.maxGenEigenspace μ = (TQ.maxGenEigenspace μ).comap Y.subtype :=
    fun μ => Module.End.genEigenspace_restrict TQ Y ⊤ μ hYT
  -- the eigenvalue `μ₀` of `T` on `Y` with minimal real part
  obtain ⟨μ₀, hμ₀, hmin⟩ := Set.exists_min_image {μ | TY.HasEigenvalue μ} Complex.re
    (Module.End.finite_hasEigenvalue TY) TY.exists_eigenvalue
  have hμ₀' : TY.HasEigenvalue μ₀ := hμ₀
  set Qge : Submodule ℂ (V ⧸ N) := ⨆ (μ : ℂ) (_ : μ₀.re ≤ μ.re), TQ.maxGenEigenspace μ
    with hQge
  set Qgt : Submodule ℂ (V ⧸ N) := ⨆ (μ : ℂ) (_ : μ₀.re < μ.re), TQ.maxGenEigenspace μ
    with hQgt
  have hgtge : Qgt ≤ Qge := iSup_mono fun μ => iSup_mono' fun h => ⟨le_of_lt h, le_rfl⟩
  -- `Y ⊆ Q_≥`
  have hYge : Y ≤ Qge := by
    intro y hy
    have htop : (⟨y, hy⟩ : Y) ∈ ⨆ μ, TY.maxGenEigenspace μ := by
      rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
    have hle : (⨆ μ, TY.maxGenEigenspace μ).map Y.subtype ≤ Qge := by
      rw [Submodule.map_iSup]
      refine iSup_le fun μ => ?_
      by_cases hμ : TY.maxGenEigenspace μ = ⊥
      · rw [hμ, Submodule.map_bot]
        exact bot_le
      · have hev : TY.HasEigenvalue μ := by
          refine Module.End.hasEigenvalue_of_hasGenEigenvalue (k := Module.finrank ℂ Y) ?_
          rw [Module.End.HasGenEigenvalue, Module.End.HasUnifEigenvalue,
            ← Module.End.maxGenEigenspace_eq_genEigenspace_finrank]
          exact hμ
        refine le_trans ?_ (le_iSup₂_of_le μ (hmin μ hev) le_rfl)
        rw [hres]
        exact Submodule.map_comap_le _ _
    exact hle (Submodule.mem_map_of_mem htop)
  -- induced operators on `Q`
  have hbar : ∀ (A : Module.End ℂ V) (hA : N ≤ N.comap A) (s : V),
      N.mkQ (A s) = N.mapQ N A hA (N.mkQ s) := fun A hA s => by simp
  have hcomm : ∀ (A : Module.End ℂ V) (hA : N ≤ N.comap A), Commute (weightOp π) A →
      ∀ x ∈ Qge, N.mapQ N A hA x ∈ Qge := by
    intro A hA hTA x hx
    have hc : Commute TQ (N.mapQ N A hA) := mapQ_commute N hNT hA hTA
    exact mem_iSup_of_maps (N.mapQ N A hA) TQ.maxGenEigenspace TQ.maxGenEigenspace
      (fun μ => μ₀.re ≤ μ.re) (fun μ => μ₀.re ≤ μ.re) id (fun μ h => h)
      (fun μ y hy => Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hy) hx
  have hshift : ∀ p q : Fin n, p < q → ∀ x ∈ Qge,
      N.mapQ N (ee π 1 p q) (fun v hv => hother p q v hv) x ∈ Qgt := by
    intro p q hpq x hx
    refine mem_iSup_of_maps (N.mapQ N (ee π 1 p q) (fun v hv => hother p q v hv))
      TQ.maxGenEigenspace TQ.maxGenEigenspace (fun μ => μ₀.re ≤ μ.re) (fun μ => μ₀.re < μ.re)
      (fun μ => μ + (((q : ℕ) : ℂ) - ((p : ℕ) : ℂ))) ?_
      (fun μ y hy => mem_maxGenEigenspace_shift TQ _ _
        (mapQ_shift N hNT (fun v hv => hother p q v hv) _ (weightOp_ee_apply π p q)) μ hy) hx
    intro μ (hμ : μ₀.re ≤ μ.re)
    have hpq' : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast hpq
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re]
    linarith
  -- `Q_≥` pulled back to `V` is everything
  have hP : Qge.comap N.mkQ = ⊤ := by
    refine hfill _ (fun w hw => hYge ⟨w, le_sideSpan π W hw, rfl⟩) ?_
    intro i p q hpq s hs
    rw [Submodule.mem_comap] at hs ⊢
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rcases hpq.lt_or_eq with h | rfl
      · rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (hup p q h s)]
        exact Qge.zero_mem
      · rw [hbar _ (fun v hv => hdiag p v hv)]
        exact hcomm _ _ (weightOp_commute π 0 p) _ hs
    · rcases hpq.lt_or_eq with h | rfl
      · rw [hbar _ (fun v hv => hother p q v hv)]
        exact hgtge (hshift p q h _ hs)
      · rw [hbar _ (fun v hv => hother p p v hv)]
        exact hcomm _ _ (weightOp_commute π 1 p) _ hs
  -- if `𝔫V = V`, every class lies in `Q_>`
  intro hJ
  have hsup : N ⊔ sideJacquet π 1 = ⊤ := by
    rw [eq_top_iff, ← hJ]
    exact complexJacquetSubspace_le_sup π
  have hN1 : ∀ u ∈ sideJacquet π 1, N.mkQ u ∈ Qgt := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, q, v, hpq, rfl⟩ := hx
      rw [hbar _ (fun v hv => hother p q v hv)]
      refine hshift p q hpq _ ?_
      exact (show v ∈ Qge.comap N.mkQ by rw [hP]; trivial)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Qgt.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Qgt.smul_mem c hx
  have hallgt : ∀ x : V ⧸ N, x ∈ Qgt := by
    intro x
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    have hv : v ∈ N ⊔ sideJacquet π 1 := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have h0 : N.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero N).2 hy
    rw [map_add, h0, zero_add]
    exact hN1 z hz
  -- an eigenvector for `μ₀` then contradicts the independence of generalized eigenspaces
  obtain ⟨y₀, hy₀⟩ := hμ₀'.exists_hasEigenvector
  have hy₁ : (y₀ : V ⧸ N) ∈ TQ.maxGenEigenspace μ₀ := by
    have h := Module.End.eigenspace_le_maxGenEigenspace hy₀.1
    rw [hres] at h
    exact h
  have hle2 : Qgt ≤ ⨆ (μ) (_ : μ ≠ μ₀), TQ.maxGenEigenspace μ :=
    iSup_mono fun μ => iSup_mono' fun h =>
      ⟨fun he => by rw [he] at h; exact lt_irrefl _ h, le_rfl⟩
  have hy₂ : (y₀ : V ⧸ N) ∈ ⨆ (μ) (_ : μ ≠ μ₀), TQ.maxGenEigenspace μ := hle2 (hallgt y₀)
  have hind := iSupIndep_def.1 (Module.End.independent_maxGenEigenspace TQ) μ₀
  exact hy₀.2 (Submodule.coe_eq_zero.1 (Submodule.disjoint_def.1 hind _ hy₁ hy₂))

end Reduction

end ComplexJacquetFinite

universe uV

/-- **One-sided nonvanishing of the Jacquet module**: for an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module, the span of the vectors `E^{(0)}_pq v` (`p < q`), i.e. the image of the
nilradical `𝔫` acting through the first (holomorphic) factor of `𝔤𝔩_n(ℂ) ⊗_ℝ ℂ ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`,
is a proper subspace. -/
def ComplexJacquetOneSidedStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), p < q ∧ ComplexJacquetFinite.ee π 0 p q v = w}
        ≠ ⊤

/-- One-sided nonvanishing implies nonvanishing of the Jacquet module. -/
theorem complexJacquetModuleNonzero_of_oneSided :
    ComplexJacquetOneSidedStatement.{uV} → ComplexJacquetModuleNonzeroStatement.{uV} :=
  fun h n V _ _ ρ π hgk hirr hadm =>
    ComplexJacquetFinite.jacquet_ne_top_of_sideJacquet_ne_top π hgk hirr hadm
      (h n V ρ π hgk hirr hadm)

/-- Nonvanishing implies one-sided nonvanishing, since `𝔫^{(0)} V ⊆ 𝔫V`. -/
theorem complexJacquetOneSided_of_nonzero :
    ComplexJacquetModuleNonzeroStatement.{uV} → ComplexJacquetOneSidedStatement.{uV} :=
  fun h n V _ _ ρ π hgk hirr hadm htop =>
    h n V ρ π hgk hirr hadm
      (eq_top_iff.2 (le_trans htop.symm.le (ComplexJacquetFinite.sideJacquet_le π 0)))

/-- The two statements are equivalent. -/
theorem complexJacquetModuleNonzero_iff_oneSided :
    ComplexJacquetModuleNonzeroStatement.{uV} ↔ ComplexJacquetOneSidedStatement.{uV} :=
  ⟨complexJacquetOneSided_of_nonzero, complexJacquetModuleNonzero_of_oneSided⟩

/-- One-sided nonvanishing implies `ComplexJacquetModuleFiniteStatement`. -/
theorem complexJacquetModuleFinite_of_oneSided :
    ComplexJacquetOneSidedStatement.{uV} → ComplexJacquetModuleFiniteStatement.{uV} :=
  fun h => complexJacquetModuleFinite_of_nonzero (complexJacquetModuleNonzero_of_oneSided h)

end Langlands.Archimedean
