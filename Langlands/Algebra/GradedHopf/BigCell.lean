import Langlands.Algebra.GradedHopf.Positive
import Langlands.Algebra.GradedHopf.Unitriangular

/-! # The big cell of a graded bialgebra -/

noncomputable section

open DirectSum TensorProduct

namespace Langlands.Algebra.GradedHopf

section NegGrade

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℤ → Submodule k A)

/-- The reversed grading `n ↦ 𝒜 (-n)`. -/
def negGrade (n : ℤ) : Submodule k A := 𝒜 (-n)

variable [GradedAlgebra 𝒜]

instance negGradedAlgebra : GradedAlgebra (negGrade 𝒜) :=
  regradedAlgebra 𝒜 (AddEquiv.neg ℤ)

theorem gradeProj_negGrade (n : ℤ) (a : A) : gradeProj (negGrade 𝒜) n a = gradeProj 𝒜 (-n) a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => rw [map_zero, map_zero]
  | @homogeneous i a =>
    have ha : (a : A) ∈ negGrade 𝒜 (-i) := by
      change (a : A) ∈ 𝒜 (-(-i))
      rw [neg_neg]
      exact a.2
    rw [gradeProj_of_mem (negGrade 𝒜) ha, gradeProj_of_mem 𝒜 a.2]
    exact if_congr neg_eq_iff_eq_neg rfl rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end NegGrade

section BigCell

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] (𝒜 : ℤ → Submodule k A)

/-- The ideal whose quotient is the positive part, for the counit. -/
abbrev plusIdeal : Ideal A := positiveIdeal 𝒜 (Bialgebra.counitAlgHom k A)

/-- The ideal whose quotient is the negative part, for the counit. -/
abbrev minusIdeal : Ideal A := positiveIdeal (negGrade 𝒜) (Bialgebra.counitAlgHom k A)

/-- The comultiplication followed by the projections to the negative and positive parts. -/
def bigCellMap : A →ₐ[k] (A ⧸ minusIdeal 𝒜) ⊗[k] (A ⧸ plusIdeal 𝒜) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (minusIdeal 𝒜))
    (Ideal.Quotient.mkₐ k (plusIdeal 𝒜))).comp (Bialgebra.comulAlgHom k A)

theorem bigCellMap_apply (a : A) :
    bigCellMap 𝒜 a = TensorProduct.map (Ideal.Quotient.mkₐ k (minusIdeal 𝒜)).toLinearMap
      (Ideal.Quotient.mkₐ k (plusIdeal 𝒜)).toLinearMap (Coalgebra.comul (R := k) a) :=
  rfl

variable {𝒜}

theorem mk_minus_of_pos {d : ℤ} (hd : 0 < d) {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk (minusIdeal 𝒜) a = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 (mem_positiveIdeal_of_neg (n := -d) (neg_neg_of_pos hd) ?_)
  change a ∈ 𝒜 (-(-d))
  rwa [neg_neg]

theorem mk_plus_of_neg {d : ℤ} (hd : d < 0) {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk (plusIdeal 𝒜) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (mem_positiveIdeal_of_neg hd ha)

variable [GradedAlgebra 𝒜]

theorem mk_minus_of_zero {a : A} (ha : a ∈ 𝒜 0) :
    Ideal.Quotient.mk (minusIdeal 𝒜) a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  refine mem_positiveIdeal_of_zero ?_ ?_
  · change _ ∈ 𝒜 (-0)
    rw [neg_zero]
    exact Submodule.sub_mem _ ha (algebraMap_mem_zero 𝒜 _)
  · simp

theorem mk_plus_of_zero {a : A} (ha : a ∈ 𝒜 0) :
    Ideal.Quotient.mk (plusIdeal 𝒜) a = algebraMap k _ (Coalgebra.counit (R := k) a) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  refine mem_positiveIdeal_of_zero ?_ ?_
  · exact Submodule.sub_mem _ ha (algebraMap_mem_zero 𝒜 _)
  · simp

variable (𝒜) in
/-- A finite square matrix of homogeneous elements whose comultiplication is given by matrix
multiplication, whose counit is the identity matrix, and whose entries generate the algebra.
The entry `(i, j)` has degree `w j - w i`. -/
structure GradedMatrixCoefficients where
  /-- The size of the matrix. -/
  n : ℕ
  /-- The weights of the rows and columns. -/
  w : Fin n → ℤ
  /-- The matrix. -/
  M : Matrix (Fin n) (Fin n) A
  comul_apply : ∀ i j, Coalgebra.comul (R := k) (M i j) = ∑ l, M i l ⊗ₜ[k] M l j
  counit_apply : ∀ i j, Coalgebra.counit (R := k) (M i j) = if i = j then 1 else 0
  mem : ∀ i j, M i j ∈ 𝒜 (w j - w i)
  adjoin_eq_top : Algebra.adjoin k (Set.range fun p : Fin n × Fin n => M p.1 p.2) = ⊤

theorem bigCellMap_surjective (G : GradedMatrixCoefficients 𝒜) :
    Function.Surjective (bigCellMap 𝒜) := by
  set S := (bigCellMap 𝒜).range
  let L : Matrix (Fin G.n) (Fin G.n) ((A ⧸ minusIdeal 𝒜) ⊗[k] (A ⧸ plusIdeal 𝒜)) :=
    fun i j => Ideal.Quotient.mk _ (G.M i j) ⊗ₜ 1
  let U : Matrix (Fin G.n) (Fin G.n) ((A ⧸ minusIdeal 𝒜) ⊗[k] (A ⧸ plusIdeal 𝒜)) :=
    fun i j => 1 ⊗ₜ Ideal.Quotient.mk _ (G.M i j)
  have hLU : ∀ i j, (L * U) i j ∈ S.toSubring := by
    intro i j
    refine ⟨G.M i j, ?_⟩
    change bigCellMap 𝒜 (G.M i j) = _
    rw [bigCellMap_apply, G.comul_apply, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [TensorProduct.map_tmul, L, U, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  set C : ℤ := ∑ i, |G.w i|
  have hC : ∀ i, 0 ≤ G.w i + C := fun i => by
    have h1 : |G.w i| ≤ C := Finset.single_le_sum (f := fun i => |G.w i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (G.w i)
    omega
  let τ : Fin G.n → ℕ := fun i => (G.w i + C).toNat
  have hτ : ∀ i j, G.w j < G.w i → τ j < τ i := fun i j h => by
    have := hC i
    have := hC j
    simp only [τ]
    omega
  have hL1 : ∀ i, L i i = 1 := fun i => by
    have h := G.mem i i
    rw [sub_self] at h
    simp [L, mk_minus_of_zero h, G.counit_apply, Algebra.TensorProduct.one_def]
  have hU1 : ∀ i, U i i = 1 := fun i => by
    have h := G.mem i i
    rw [sub_self] at h
    simp [U, mk_plus_of_zero h, G.counit_apply, Algebra.TensorProduct.one_def]
  have hL : ∀ i j, L i j ≠ 0 → i = j ∨ τ j < τ i := by
    intro i j hne
    rcases lt_trichotomy (G.w j) (G.w i) with h | h | h
    · exact Or.inr (hτ i j h)
    · by_cases hij : i = j
      · exact Or.inl hij
      · have hm := G.mem i j
        rw [h, sub_self] at hm
        exfalso
        apply hne
        simp [L, mk_minus_of_zero hm, G.counit_apply, hij]
    · exfalso
      apply hne
      simp only [L, mk_minus_of_pos (sub_pos.2 h) (G.mem i j), TensorProduct.zero_tmul]
  have hU : ∀ i j, U i j ≠ 0 → i = j ∨ τ i < τ j := by
    intro i j hne
    rcases lt_trichotomy (G.w i) (G.w j) with h | h | h
    · exact Or.inr (hτ j i h)
    · by_cases hij : i = j
      · exact Or.inl hij
      · have hm := G.mem i j
        rw [h, sub_self] at hm
        exfalso
        apply hne
        simp [U, mk_plus_of_zero hm, G.counit_apply, hij]
    · exfalso
      apply hne
      simp only [U, mk_plus_of_neg (sub_neg.2 h) (G.mem i j), TensorProduct.tmul_zero]
  have hmem := mem_of_mul_mem S.toSubring τ hL1 hU1 hL hU hLU
  have hleft : ∀ a : A, Ideal.Quotient.mk (minusIdeal 𝒜) a ⊗ₜ[k] (1 : A ⧸ plusIdeal 𝒜) ∈ S := by
    have h : Algebra.adjoin k (Set.range fun p : Fin G.n × Fin G.n => G.M p.1 p.2) ≤
        S.comap ((Algebra.TensorProduct.includeLeft (R := k) (S := k)).comp
          (Ideal.Quotient.mkₐ k (minusIdeal 𝒜))) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact (hmem i j).1
    rw [G.adjoin_eq_top] at h
    intro a
    exact h Algebra.mem_top
  have hright : ∀ a : A, (1 : A ⧸ minusIdeal 𝒜) ⊗ₜ[k] Ideal.Quotient.mk (plusIdeal 𝒜) a ∈ S := by
    have h : Algebra.adjoin k (Set.range fun p : Fin G.n × Fin G.n => G.M p.1 p.2) ≤
        S.comap ((Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ minusIdeal 𝒜)).comp
          (Ideal.Quotient.mkₐ k (plusIdeal 𝒜))) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact (hmem i j).2
    rw [G.adjoin_eq_top] at h
    intro a
    exact h Algebra.mem_top
  have hall : ∀ b, b ∈ S := by
    intro b
    induction b using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      have := S.mul_mem (hleft a) (hright c)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    | add x y hx hy => exact S.add_mem hx hy
  intro b
  exact hall b

end BigCell

section Square

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] {ε : A →ₐ[k] k}

/-- The components of nonnegative degree of the elements of the positive ideal lie in the square
of the augmentation ideal. -/
theorem gradeProj_mem_sq_of_mem_positiveIdeal (hε : ∀ n ≠ 0, ∀ a ∈ 𝒜 n, ε a = 0)
    (h0 : ∀ a ∈ 𝒜 0, ε a = 0 → a ∈ RingHom.ker ε ^ 2) {x : A} (hx : x ∈ positiveIdeal 𝒜 ε)
    {d : ℤ} (hd : 0 ≤ d) : gradeProj 𝒜 d x ∈ RingHom.ker ε ^ 2 := by
  have key : ∀ a : A, ∀ d : ℤ, 0 ≤ d → gradeProj 𝒜 d (a * x) ∈ RingHom.ker ε ^ 2 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro g (⟨e, he, hg⟩ | ⟨hg, hεg⟩) a d hd
      · rw [gradeProj_mul_of_right_mem 𝒜 hg, pow_two]
        refine Ideal.mul_mem_mul (RingHom.mem_ker.2 ?_) (RingHom.mem_ker.2 (hε e he.ne g hg))
        exact hε (d - e) (by omega) _ (gradeProj_mem 𝒜 _ a)
      · rw [gradeProj_mul_of_right_mem 𝒜 hg]
        exact Ideal.mul_mem_left _ _ (h0 g hg hεg)
    · intro a d _
      rw [mul_zero, map_zero]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz a d hd
      rw [mul_add, map_add]
      exact Ideal.add_mem _ (hy a d hd) (hz a d hd)
    · intro b y _ hy a d hd
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * b) d hd
  simpa using key 1 d hd

end Square

section Injective

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
theorem IsGradedBialgebra.counitAlgHom_eq_zero (h𝒜 : IsGradedBialgebra 𝒜) :
    ∀ n ≠ 0, ∀ a ∈ 𝒜 n, Bialgebra.counitAlgHom k A a = 0 :=
  fun n hn a ha => h𝒜.counit_eq_zero n hn a ha

omit [GradedAlgebra 𝒜] in
theorem IsGradedBialgebra.counitAlgHom_eq_zero_neg (h𝒜 : IsGradedBialgebra 𝒜) :
    ∀ n ≠ 0, ∀ a ∈ negGrade 𝒜 n, Bialgebra.counitAlgHom k A a = 0 :=
  fun n hn a ha => h𝒜.counit_eq_zero (-n) (neg_ne_zero.2 hn) a ha

omit [GradedAlgebra 𝒜] in
theorem zero_neg_of_zero
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) :
    ∀ a ∈ negGrade 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 := fun a ha =>
  h0 a (by change a ∈ 𝒜 (-0) at ha; rwa [neg_zero] at ha)

/-- The augmentation of the negative part. -/
abbrev minusCounit (h𝒜 : IsGradedBialgebra 𝒜) : A ⧸ minusIdeal 𝒜 →ₐ[k] k :=
  positiveCounit h𝒜.counitAlgHom_eq_zero_neg

/-- The augmentation of the positive part. -/
abbrev plusCounit (h𝒜 : IsGradedBialgebra 𝒜) : A ⧸ plusIdeal 𝒜 →ₐ[k] k :=
  positiveCounit h𝒜.counitAlgHom_eq_zero

omit [GradedAlgebra 𝒜] in
theorem plus_bigCellMap (h𝒜 : IsGradedBialgebra 𝒜) (a : A) :
    Algebra.TensorProduct.productMap ((Algebra.ofId k _).comp (minusCounit h𝒜))
      (AlgHom.id k _) (bigCellMap 𝒜 a) = Ideal.Quotient.mk (plusIdeal 𝒜) a := by
  let ℛ := Coalgebra.Repr.arbitrary k a
  have h := Coalgebra.sum_counit_smul ℛ
  rw [bigCellMap_apply, ← ℛ.eq, map_sum, map_sum]
  conv_rhs => rw [← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    map_mul, Ideal.Quotient.mk_algebraMap]
  rfl

omit [GradedAlgebra 𝒜] in
theorem minus_bigCellMap (h𝒜 : IsGradedBialgebra 𝒜) (a : A) :
    Algebra.TensorProduct.productMap (AlgHom.id k _)
      ((Algebra.ofId k _).comp (plusCounit h𝒜)) (bigCellMap 𝒜 a) =
      Ideal.Quotient.mk (minusIdeal 𝒜) a := by
  let ℛ := Coalgebra.Repr.arbitrary k a
  have h := congrArg (TensorProduct.rid k A) (Coalgebra.sum_tmul_counit_eq ℛ)
  simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h
  rw [bigCellMap_apply, ← ℛ.eq, map_sum, map_sum]
  conv_rhs => rw [← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    map_mul, Ideal.Quotient.mk_algebraMap, mul_comm]
  rfl

omit [GradedAlgebra 𝒜] in
theorem counit_bigCellMap (h𝒜 : IsGradedBialgebra 𝒜) (a : A) :
    Algebra.TensorProduct.productMap (minusCounit h𝒜) (plusCounit h𝒜) (bigCellMap 𝒜 a) =
      Coalgebra.counit (R := k) a := by
  let ℛ := Coalgebra.Repr.arbitrary k a
  have h := Coalgebra.sum_counit_smul ℛ
  rw [bigCellMap_apply, ← ℛ.eq, map_sum, map_sum]
  conv_rhs => rw [← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul, map_smul,
    smul_eq_mul]
  rfl

omit [GradedAlgebra 𝒜] in
theorem ker_bigCellMap_le_plusIdeal (h𝒜 : IsGradedBialgebra 𝒜) :
    RingHom.ker (bigCellMap 𝒜) ≤ plusIdeal 𝒜 := fun x hx => by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← plus_bigCellMap h𝒜, RingHom.mem_ker.1 hx, map_zero]

omit [GradedAlgebra 𝒜] in
theorem ker_bigCellMap_le_minusIdeal (h𝒜 : IsGradedBialgebra 𝒜) :
    RingHom.ker (bigCellMap 𝒜) ≤ minusIdeal 𝒜 := fun x hx => by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← minus_bigCellMap h𝒜, RingHom.mem_ker.1 hx, map_zero]

theorem mem_sq_of_mem_ker_bigCellMap (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2) {x : A}
    (hx : x ∈ RingHom.ker (bigCellMap 𝒜)) :
    x ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 := by
  classical
  rw [← sum_gradeProj 𝒜 x]
  refine Ideal.sum_mem _ fun d _ => ?_
  rcases le_or_gt 0 d with hd | hd
  · exact gradeProj_mem_sq_of_mem_positiveIdeal h𝒜.counitAlgHom_eq_zero h0
      (ker_bigCellMap_le_plusIdeal h𝒜 hx) hd
  · have := gradeProj_negGrade 𝒜 (-d) x
    rw [neg_neg] at this
    rw [← this]
    exact gradeProj_mem_sq_of_mem_positiveIdeal h𝒜.counitAlgHom_eq_zero_neg (zero_neg_of_zero h0)
      (ker_bigCellMap_le_minusIdeal h𝒜 hx) (by omega)

end Injective

section Bijective

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- The big-cell map is injective: its kernel `K` lies in the square of the augmentation ideal
`I`, and an algebra section of the big-cell map (which exists because its target is a
polynomial algebra) shows `K ≤ I • K`; Nakayama's lemma and the absence of zero divisors then
give `K = 0`. -/
theorem bigCellMap_injective [IsDomain A] [Algebra.FiniteType k A] [Algebra.FormallySmooth k A]
    (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2)
    (G : GradedMatrixCoefficients 𝒜) : Function.Injective (bigCellMap 𝒜) := by
  obtain ⟨n₁, -, x₁, -, -, hx₁⟩ := exists_positive_aeval_bijective (𝒜 := negGrade 𝒜)
    h𝒜.counitAlgHom_eq_zero_neg (zero_neg_of_zero h0)
  obtain ⟨n₂, -, x₂, -, -, hx₂⟩ := exists_positive_aeval_bijective h𝒜.counitAlgHom_eq_zero h0
  let Φ : MvPolynomial (Fin n₁ ⊕ Fin n₂) k ≃ₐ[k] (A ⧸ minusIdeal 𝒜) ⊗[k] (A ⧸ plusIdeal 𝒜) :=
    (MvPolynomial.tensorEquivSum k (Fin n₁) (Fin n₂) k).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hx₁) (AlgEquiv.ofBijective _ hx₂))
  have hsurj := bigCellMap_surjective G
  choose z hz using fun p => hsurj (Φ (MvPolynomial.X p))
  let s := (MvPolynomial.aeval z).comp Φ.symm.toAlgHom
  have hms : ∀ b, bigCellMap 𝒜 (s b) = b := by
    have h1 : (bigCellMap 𝒜).comp (MvPolynomial.aeval z) = Φ.toAlgHom :=
      MvPolynomial.algHom_ext fun p => by simp [hz]
    intro b
    have := congrArg (fun f => f (Φ.symm b)) h1
    simpa [s] using this
  set I := RingHom.ker (Bialgebra.counitAlgHom k A)
  set K := RingHom.ker (bigCellMap 𝒜)
  have hεs : ∀ a, Bialgebra.counitAlgHom k A (s (bigCellMap 𝒜 a)) =
      Bialgebra.counitAlgHom k A a := by
    intro a
    simp only [Bialgebra.counitAlgHom_apply]
    rw [← counit_bigCellMap h𝒜, hms, counit_bigCellMap h𝒜]
  have hK : ∀ a, a - s (bigCellMap 𝒜 a) ∈ K := fun a => by
    rw [RingHom.mem_ker, map_sub, hms, sub_self]
  have hI : ∀ a ∈ I, s (bigCellMap 𝒜 a) ∈ I := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hεs, ha]
  have hsq : ∀ y ∈ I ^ 2, y - s (bigCellMap 𝒜 y) ∈ I * K := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have : a * b - s (bigCellMap 𝒜 (a * b)) = b * (a - s (bigCellMap 𝒜 a)) +
          s (bigCellMap 𝒜 a) * (b - s (bigCellMap 𝒜 b)) := by
        rw [map_mul, map_mul]
        ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul hb (hK a)) (Ideal.mul_mem_mul (hI a ha) (hK b))
    · intro y y' hy hy'
      have : y + y' - s (bigCellMap 𝒜 (y + y')) =
          (y - s (bigCellMap 𝒜 y)) + (y' - s (bigCellMap 𝒜 y')) := by
        rw [map_add, map_add]
        ring
      rw [this]
      exact Ideal.add_mem _ hy hy'
  have hle : K ≤ I • K := by
    intro x hx
    rw [Ideal.smul_eq_mul]
    have := hsq x (mem_sq_of_mem_ker_bigCellMap h𝒜 h0 hx)
    rwa [RingHom.mem_ker.1 hx, map_zero, sub_zero] at this
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨r, hr, hrK⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I K (IsNoetherian.noetherian K)
      hle
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_sub, RingHom.mem_ker, map_neg, map_one] at hr
    exact one_ne_zero (neg_eq_zero.1 hr)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := hrK x hx
  rw [smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hr0

theorem bigCellMap_bijective [IsDomain A] [Algebra.FiniteType k A] [Algebra.FormallySmooth k A]
    (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2)
    (G : GradedMatrixCoefficients 𝒜) : Function.Bijective (bigCellMap 𝒜) :=
  ⟨bigCellMap_injective h𝒜 h0 G, bigCellMap_surjective G⟩

end Bijective

section Coordinates

variable {k A : Type*} [CommRing k] [CommRing A] [Bialgebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- The `ℤ`-indexed family of submodules of the negative part: the image of `𝒜 n`. -/
abbrev minusGrade : ℤ → Submodule k (A ⧸ minusIdeal 𝒜) :=
  quotGrade 𝒜 (minusIdeal 𝒜) (AddMonoidHom.id ℤ)

/-- The `ℤ`-indexed family of submodules of the positive part: the image of `𝒜 n`. -/
abbrev plusGrade : ℤ → Submodule k (A ⧸ plusIdeal 𝒜) :=
  quotGrade 𝒜 (plusIdeal 𝒜) (AddMonoidHom.id ℤ)

theorem isHomogeneous_minusIdeal : (minusIdeal 𝒜).IsHomogeneous 𝒜 := by
  intro i r hr
  have h := isHomogeneous_positiveIdeal (negGrade 𝒜) (Bialgebra.counitAlgHom k A) (-i) hr
  have h' := gradeProj_negGrade 𝒜 (-i) r
  rw [neg_neg] at h'
  rw [← gradeProj_apply, ← h']
  exact h

instance minusGradedAlgebra : GradedAlgebra (minusGrade 𝒜) :=
  quotGradedAlgebra (isHomogeneous_minusIdeal 𝒜) Function.injective_id
    fun i hi => absurd ⟨i, rfl⟩ hi

instance plusGradedAlgebra : GradedAlgebra (plusGrade 𝒜) :=
  quotGradedAlgebra (isHomogeneous_positiveIdeal 𝒜 _) Function.injective_id
    fun i hi => absurd ⟨i, rfl⟩ hi

variable {𝒜}

/-- The big-cell map is graded: it intertwines the degree projections of `A` with the
total-degree projections of the tensor product of the negative and positive parts. -/
theorem bigCellMap_gradeProj (h𝒜 : IsGradedBialgebra 𝒜) (n : ℤ) (a : A) :
    bigCellMap 𝒜 (gradeProj 𝒜 n a) =
      tensorProj (minusGrade 𝒜) (plusGrade 𝒜) n (bigCellMap 𝒜 a) := by
  rw [bigCellMap_apply, bigCellMap_apply, h𝒜.comul_gradeProj]
  exact LinearMap.congr_fun (IsGradedMap.map_comp_tensorProj isGradedMap_mkₐ isGradedMap_mkₐ n)
    (Coalgebra.comul (R := k) a)

end Coordinates

section PolynomialCoordinates

variable {k A : Type*} [Field k] [CommRing A] [Bialgebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

/-- A graded bialgebra satisfying the hypotheses of `bigCellMap_bijective` is a polynomial
algebra on finitely many homogeneous generators of nonzero degree. -/
theorem exists_homogeneous_polynomial_coordinates [IsDomain A] [Algebra.FiniteType k A]
    [Algebra.FormallySmooth k A] (h𝒜 : IsGradedBialgebra 𝒜)
    (h0 : ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
      a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2)
    (G : GradedMatrixCoefficients 𝒜) :
    ∃ (n₁ n₂ : ℕ) (w : Fin n₁ ⊕ Fin n₂ → ℤ) (z : Fin n₁ ⊕ Fin n₂ → A), (∀ p, w p ≠ 0) ∧
      (∀ p, z p ∈ 𝒜 (w p)) ∧
      Function.Bijective (MvPolynomial.aeval z : MvPolynomial (Fin n₁ ⊕ Fin n₂) k →ₐ[k] A) := by
  obtain ⟨n₁, d₁, x₁, hd₁, hx₁m, hx₁⟩ := exists_positive_aeval_bijective (𝒜 := negGrade 𝒜)
    h𝒜.counitAlgHom_eq_zero_neg (zero_neg_of_zero h0)
  obtain ⟨n₂, d₂, x₂, hd₂, hx₂m, hx₂⟩ :=
    exists_positive_aeval_bijective h𝒜.counitAlgHom_eq_zero h0
  let Φ : MvPolynomial (Fin n₁ ⊕ Fin n₂) k ≃ₐ[k] (A ⧸ minusIdeal 𝒜) ⊗[k] (A ⧸ plusIdeal 𝒜) :=
    (MvPolynomial.tensorEquivSum k (Fin n₁) (Fin n₂) k).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hx₁) (AlgEquiv.ofBijective _ hx₂))
  have hΦl : ∀ i, Φ (MvPolynomial.X (Sum.inl i)) = x₁ i ⊗ₜ 1 := fun i => by
    have : (MvPolynomial.tensorEquivSum k (Fin n₁) (Fin n₂) k).symm
        (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_X_tmul_one]
    simp [Φ, this]
  have hΦr : ∀ j, Φ (MvPolynomial.X (Sum.inr j)) = 1 ⊗ₜ x₂ j := fun j => by
    have : (MvPolynomial.tensorEquivSum k (Fin n₁) (Fin n₂) k).symm
        (MvPolynomial.X (Sum.inr j)) = 1 ⊗ₜ MvPolynomial.X j := by
      rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_one_tmul_X]
    simp [Φ, this]
  let w : Fin n₁ ⊕ Fin n₂ → ℤ := Sum.elim (fun i => -(d₁ i : ℤ)) (fun j => (d₂ j : ℤ))
  have hw : ∀ p, w p ≠ 0 := by
    rintro (i | j)
    · simpa [w] using (hd₁ i).ne'
    · simpa [w] using (hd₂ j).ne'
  have hΦm : ∀ p, Φ (MvPolynomial.X p) ∈ tensorGrade (minusGrade 𝒜) (plusGrade 𝒜) (w p) := by
    rintro (i | j)
    · rw [hΦl]
      have h := tmul_mem_tensorGrade (minusGrade 𝒜) (plusGrade 𝒜) (i := -(d₁ i : ℤ)) (j := 0)
        (hx₁m i) (SetLike.GradedOne.one_mem)
      rwa [add_zero] at h
    · rw [hΦr]
      have h := tmul_mem_tensorGrade (minusGrade 𝒜) (plusGrade 𝒜) (i := 0) (j := (d₂ j : ℤ))
        (SetLike.GradedOne.one_mem) (hx₂m j)
      rwa [zero_add] at h
  have hbij := bigCellMap_bijective h𝒜 h0 G
  choose z₀ hz₀ using fun p => hbij.2 (Φ (MvPolynomial.X p))
  let z : Fin n₁ ⊕ Fin n₂ → A := fun p => gradeProj 𝒜 (w p) (z₀ p)
  have hz : ∀ p, bigCellMap 𝒜 (z p) = Φ (MvPolynomial.X p) := fun p => by
    simp only [z]
    rw [bigCellMap_gradeProj h𝒜, hz₀, tensorProj_of_mem_tensorGrade_self _ _ (hΦm p)]
  have hcomp : (bigCellMap 𝒜).comp (MvPolynomial.aeval z) = Φ.toAlgHom :=
    MvPolynomial.algHom_ext fun p => by simp [hz]
  have hcomp' : ∀ f, bigCellMap 𝒜 (MvPolynomial.aeval z f) = Φ f := fun f =>
    congrArg (fun F => F f) hcomp
  refine ⟨n₁, n₂, w, z, hw, fun p => gradeProj_mem 𝒜 _ _, ?_, ?_⟩
  · intro f g hfg
    apply Φ.injective
    rw [← hcomp', ← hcomp', hfg]
  · intro a
    refine ⟨Φ.symm (bigCellMap 𝒜 a), hbij.1 ?_⟩
    rw [hcomp', AlgEquiv.apply_symm_apply]

end PolynomialCoordinates

end Langlands.Algebra.GradedHopf
