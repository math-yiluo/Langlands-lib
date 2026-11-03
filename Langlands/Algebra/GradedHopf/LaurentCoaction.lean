import Langlands.Algebra.GradedHopf.Basic
import Langlands.CommutativeAlgebra.GradedFormallySmooth

/-! # The Laurent coaction of a `ℤ`-grading and formal smoothness of quotients -/

noncomputable section

open DirectSum

namespace Langlands.Algebra.GradedHopf

section Idempotent

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- If `B ⧸ N` is formally smooth and `N ≤ J ≤ J ^ 2 ⊔ N`, then `B ⧸ J` is formally smooth. -/
theorem formallySmooth_quotient_of_le_sq_sup {N J : Ideal B}
    [Algebra.FormallySmooth R (B ⧸ N)] (hNJ : N ≤ J) (hJ : J ≤ J ^ 2 ⊔ N) :
    Algebra.FormallySmooth R (B ⧸ J) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun D _ _ K hK x => ?_
  obtain ⟨h, hh⟩ := Algebra.FormallySmooth.comp_surjective R (B ⧸ N) K hK
    (x.comp (Ideal.Quotient.factorₐ R hNJ))
  set φ : B →ₐ[R] D := h.comp (Ideal.Quotient.mkₐ R N) with hφ
  have hφN : N.map φ = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    rw [RingHom.mem_ker, hφ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hφK : J.map φ ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun g => g (Ideal.Quotient.mk N a)) hh
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    change Ideal.Quotient.mk K (h (Ideal.Quotient.mk N a)) = 0
    rw [this]
    change x (Ideal.Quotient.mk J a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hφJ : J.map φ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc J.map φ ≤ (J ^ 2 ⊔ N).map φ := Ideal.map_mono hJ
      _ = (J.map φ) ^ 2 := by rw [Ideal.map_sup, Ideal.map_pow, hφN, sup_bot_eq]
      _ ≤ K ^ 2 := Ideal.pow_right_mono hφK 2
      _ = ⊥ := hK
  have hker : ∀ a ∈ J, φ a = 0 := fun a ha => by
    have : φ a ∈ J.map φ := Ideal.mem_map_of_mem _ ha
    rwa [hφJ, Ideal.mem_bot] at this
  refine ⟨Ideal.Quotient.liftₐ J φ hker, ?_⟩
  apply Ideal.Quotient.algHom_ext
  refine AlgHom.ext fun b => ?_
  have := congrArg (fun g => g (Ideal.Quotient.mk N b)) hh
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  change Ideal.Quotient.mk K (h (Ideal.Quotient.mk N b)) = x (Ideal.Quotient.mk J b)
  rw [this]
  rfl

end Idempotent

section Laurent

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
/-- The additive map `𝒜 n → A[T, T⁻¹]`, `a ↦ a Tⁿ`. -/
def laurentSingle (n : ℤ) : 𝒜 n →+ LaurentPolynomial A :=
  (AddMonoidAlgebra.singleAddHom n).comp (𝒜 n).subtype.toAddMonoidHom

omit [GradedAlgebra 𝒜] in
theorem laurentSingle_apply (n : ℤ) (a : 𝒜 n) :
    laurentSingle 𝒜 n a = AddMonoidAlgebra.single n (a : A) :=
  rfl

theorem laurentSingle_one :
    laurentSingle 𝒜 0 (GradedMonoid.GOne.one (A := fun i => 𝒜 i)) = 1 :=
  (AddMonoidAlgebra.one_def (R := A) (M := ℤ)).symm

theorem laurentSingle_mul {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j) :
    laurentSingle 𝒜 (i + j) (GradedMonoid.GMul.mul (A := fun i => 𝒜 i) a b) =
      laurentSingle 𝒜 i a * laurentSingle 𝒜 j b := by
  rw [laurentSingle_apply, laurentSingle_apply, laurentSingle_apply,
    AddMonoidAlgebra.single_mul_single]
  rfl

/-- The ring map `A → A[T, T⁻¹]` sending `a` to `∑ₙ aₙ Tⁿ`, where `aₙ` is the component of `a`
of degree `n`. -/
def laurentCoaction : A →+* LaurentPolynomial A :=
  (DirectSum.toSemiring (laurentSingle 𝒜) (laurentSingle_one 𝒜) (laurentSingle_mul 𝒜)).comp
    (decomposeRingEquiv 𝒜).toRingHom

theorem laurentCoaction_apply (a : A) :
    laurentCoaction 𝒜 a =
      DirectSum.toSemiring (laurentSingle 𝒜) (laurentSingle_one 𝒜) (laurentSingle_mul 𝒜)
        (decompose 𝒜 a) :=
  rfl

variable {𝒜}

theorem laurentCoaction_of_mem {n : ℤ} {a : A} (ha : a ∈ 𝒜 n) :
    laurentCoaction 𝒜 a = AddMonoidAlgebra.single n a := by
  rw [laurentCoaction_apply, decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

variable (𝒜)

theorem coeff_laurentCoaction (a : A) (n : ℤ) :
    (laurentCoaction 𝒜 a).coeff n = gradeProj 𝒜 n a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [laurentCoaction_of_mem a.2, gradeProj_of_mem 𝒜 a.2, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
  | add a b ha hb => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, map_add]

theorem laurentCoaction_algebraMap (r : k) :
    laurentCoaction 𝒜 (algebraMap k A r) = LaurentPolynomial.C (algebraMap k A r) :=
  laurentCoaction_of_mem (algebraMap_mem_zero 𝒜 r)

theorem sum_coeff_laurentCoaction (a : A) :
    ((laurentCoaction 𝒜 a).coeff.sum fun _ b => b) = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [laurentCoaction_of_mem a.2, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index rfl]
  | add a b ha hb =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (fun _ => rfl)
      (fun _ _ _ => rfl), ha, hb]

theorem laurentCoaction_coeff (a : A) (n : ℤ) :
    laurentCoaction 𝒜 ((laurentCoaction 𝒜 a).coeff n) =
      AddMonoidAlgebra.single n ((laurentCoaction 𝒜 a).coeff n) := by
  rw [coeff_laurentCoaction]
  exact laurentCoaction_of_mem (gradeProj_mem 𝒜 n a)

/-- The ideal generated by the homogeneous elements of negative degree. -/
def negSpan : Ideal A := Ideal.span {a | ∃ n < 0, a ∈ 𝒜 n}

theorem negIdeal_laurentCoaction :
    CommutativeAlgebra.GradedFormallySmooth.negIdeal (laurentCoaction 𝒜) = negSpan 𝒜 := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨b, n, hn, rfl⟩
    rw [coeff_laurentCoaction]
    exact Ideal.subset_span ⟨n, hn, gradeProj_mem 𝒜 n b⟩
  · refine Ideal.span_le.2 ?_
    rintro a ⟨n, hn, ha⟩
    refine Ideal.subset_span ⟨a, n, hn, ?_⟩
    rw [coeff_laurentCoaction, gradeProj_of_mem_self 𝒜 ha]

/-- The quotient of a formally smooth `ℤ`-graded algebra by the ideal generated by its
homogeneous elements of negative degree is formally smooth. -/
theorem formallySmooth_quotient_negSpan [Algebra.FormallySmooth k A] :
    Algebra.FormallySmooth k (A ⧸ negSpan 𝒜) := by
  rw [← negIdeal_laurentCoaction]
  exact CommutativeAlgebra.GradedFormallySmooth.formallySmooth_quotient_negIdeal
    (laurentCoaction_algebraMap 𝒜) (sum_coeff_laurentCoaction 𝒜) (laurentCoaction_coeff 𝒜)

end Laurent

end Langlands.Algebra.GradedHopf
