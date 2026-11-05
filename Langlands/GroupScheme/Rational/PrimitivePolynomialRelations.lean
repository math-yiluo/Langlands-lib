import Langlands.GroupScheme.Rational.TorusLinearization.AdditivePolynomials
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Minimal polynomial relations between primitive elements -/

noncomputable section

universe u v w

open MvPolynomial TensorProduct

namespace Langlands.GroupScheme.PrimitivePolynomial

variable {k : Type u} [Field k] {J : Type v}

/-- The coproduct in which each variable is primitive. -/
def additiveComul : MvPolynomial J k →ₐ[k]
    MvPolynomial J k ⊗[k] MvPolynomial J k :=
  aeval (fun j => X j ⊗ₜ[k] 1 + 1 ⊗ₜ[k] X j)

@[simp] theorem additiveComul_X (j : J) :
    (additiveComul (k := k) (J := J)) (X j : MvPolynomial J k) = X j ⊗ₜ[k] 1 + 1 ⊗ₜ[k] X j := by
  simp [additiveComul]

/-- The coproduct with both boundary terms and their duplicated constant removed. -/
def reducedComul : MvPolynomial J k →ₗ[k]
    MvPolynomial J k ⊗[k] MvPolynomial J k :=
  (additiveComul (k := k) (J := J)).toLinearMap - Algebra.TensorProduct.includeLeft.toLinearMap -
    Algebra.TensorProduct.includeRight.toLinearMap +
      (aeval (fun _ : J => (0 : MvPolynomial J k ⊗[k] MvPolynomial J k))).toLinearMap

@[simp] theorem reducedComul_apply (f : MvPolynomial J k) :
    reducedComul f = (additiveComul (k := k) (J := J)) f - f ⊗ₜ[k] 1 - 1 ⊗ₜ[k] f +
      algebraMap k (MvPolynomial J k ⊗[k] MvPolynomial J k) (constantCoeff f) := by
  simp [reducedComul]

@[simp] theorem reducedComul_C (a : k) :
    reducedComul (C a : MvPolynomial J k) = 0 := by
  have h : (1 : MvPolynomial J k) ⊗ₜ[k] C a = C a ⊗ₜ[k] (1 : MvPolynomial J k) := by
    change 1 ⊗ₜ[k] algebraMap k (MvPolynomial J k) a =
      algebraMap k (MvPolynomial J k) a ⊗ₜ[k] 1
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
  simp [reducedComul, additiveComul, Algebra.TensorProduct.algebraMap_apply, h]

@[simp] theorem reducedComul_X (j : J) :
    reducedComul (X j : MvPolynomial J k) = 0 := by
  simp [reducedComul_apply]

/-- Pure tensors whose two factors have degree strictly below the bound. -/
def lowerTensorSpan (D : ℕ) : Submodule k (MvPolynomial J k ⊗[k] MvPolynomial J k) :=
  Submodule.span k {t | ∃ a b : MvPolynomial J k,
    a.totalDegree < D ∧ b.totalDegree < D ∧ t = a ⊗ₜ[k] b}

theorem tmul_mem_lowerTensorSpan {D : ℕ} {a b : MvPolynomial J k}
    (ha : a.totalDegree < D) (hb : b.totalDegree < D) :
    a ⊗ₜ[k] b ∈ lowerTensorSpan (J := J) (k := k) D :=
  Submodule.subset_span ⟨a, b, ha, hb, rfl⟩

theorem lowerTensorSpan_mono {D E : ℕ} (h : D ≤ E) :
    lowerTensorSpan (J := J) (k := k) D ≤ lowerTensorSpan E := by
  apply Submodule.span_mono
  rintro t ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, b, lt_of_lt_of_le ha h, lt_of_lt_of_le hb h, rfl⟩

theorem mul_additiveComul_X_mem {D : ℕ}
    {t : MvPolynomial J k ⊗[k] MvPolynomial J k}
    (ht : t ∈ lowerTensorSpan (J := J) (k := k) D) (j : J) :
    t * (additiveComul (k := k) (J := J)) (X j : MvPolynomial J k) ∈ lowerTensorSpan (D + 1) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, b, ha, hb, rfl⟩ := ht
    rw [additiveComul_X, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
    apply Submodule.add_mem
    · apply tmul_mem_lowerTensorSpan
      · have := totalDegree_mul a (X j)
        rw [totalDegree_X] at this
        omega
      · omega
    · apply tmul_mem_lowerTensorSpan
      · omega
      · have := totalDegree_mul b (X j)
        rw [totalDegree_X] at this
        omega
  | zero => simp
  | add a b _ _ ha hb => simpa only [add_mul] using Submodule.add_mem _ ha hb
  | smul c t _ ht => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ht

theorem reducedComul_mul_X (f : MvPolynomial J k) (hf : constantCoeff f = 0) (j : J) :
    reducedComul (f * X j) = reducedComul f * (additiveComul (k := k) (J := J)) (X j : MvPolynomial J k) +
      f ⊗ₜ[k] X j + X j ⊗ₜ[k] f := by
  simp only [reducedComul_apply, map_mul, additiveComul_X, constantCoeff_X,
    hf, mul_zero, map_zero, add_zero]
  simp only [sub_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  abel

/-- The reduced coproduct of a monic monomial is supported on lower degrees on both sides. -/
theorem reducedComul_monomial_mem (d : J →₀ ℕ) :
    reducedComul (monomial d (1 : k)) ∈
      lowerTensorSpan (J := J) (k := k) (d.sum fun _ n => n) := by
  classical
  suffices ∀ m : Multiset J, reducedComul (monomial m.toFinsupp (1 : k)) ∈
      lowerTensorSpan (J := J) (k := k) m.card by
    simpa only [Finsupp.toMultiset_toFinsupp, Finsupp.card_toMultiset, Function.id_def]
      using this (Finsupp.toMultiset d)
  intro m
  induction m using Multiset.induction_on with
  | empty =>
    change reducedComul (C (1 : k) : MvPolynomial J k) ∈ lowerTensorSpan 0
    rw [reducedComul_C]
    exact Submodule.zero_mem _
  | @cons j m ih =>
    have hmon : monomial (j ::ₘ m).toFinsupp (1 : k) =
        monomial m.toFinsupp 1 * X j := by
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        X, monomial_mul_monomial, mul_one, add_comm]
    rw [hmon, Multiset.card_cons]
    by_cases hm : m = 0
    · subst m
      simp [Multiset.toFinsupp_zero, ← C_apply]
    · have hc : constantCoeff (monomial m.toFinsupp (1 : k)) = 0 := by
        rw [constantCoeff_monomial, ite_eq_right]
        simpa using hm
      rw [reducedComul_mul_X _ hc]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact mul_additiveComul_X_mem ih j
        · apply tmul_mem_lowerTensorSpan
          · rw [totalDegree_monomial _ one_ne_zero]
            change (m.toFinsupp.sum fun _ => id) < m.card + 1
            rw [Multiset.toFinsupp_sum_eq]
            omega

          · rw [totalDegree_X]
            have := Multiset.card_pos.mpr hm
            omega
      · apply tmul_mem_lowerTensorSpan
        · rw [totalDegree_X]
          have := Multiset.card_pos.mpr hm
          omega
        · rw [totalDegree_monomial _ one_ne_zero]
          change (m.toFinsupp.sum fun _ => id) < m.card + 1
          rw [Multiset.toFinsupp_sum_eq]
          omega

/-- Every reduced coproduct lies in the tensor span of degrees below the input degree. -/
theorem reducedComul_mem (f : MvPolynomial J k) :
    reducedComul f ∈ lowerTensorSpan (J := J) (k := k) f.totalDegree := by
  classical
  have hsum : reducedComul f = ∑ d ∈ f.support, reducedComul (monomial d (f.coeff d)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [hsum]
  apply Submodule.sum_mem
  intro d hd
  have hmon : monomial d (f.coeff d) = f.coeff d • monomial d (1 : k) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul]
  apply Submodule.smul_mem
  exact lowerTensorSpan_mono (le_totalDegree hd) (reducedComul_monomial_mem d)

section Retraction

variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Evaluation injective on the lower-degree subspace is injective on its tensor span. -/
theorem eq_zero_of_tensor_map_eq_zero {D : ℕ}
    (E : MvPolynomial J k →ₗ[k] V)
    (hE : Function.Injective (E.comp (restrictTotalDegree J k (D - 1)).subtype))
    {t : MvPolynomial J k ⊗[k] MvPolynomial J k}
    (ht : t ∈ lowerTensorSpan (J := J) (k := k) D)
    (hz : TensorProduct.map E E t = 0) : t = 0 := by
  let Q := restrictTotalDegree J k (D - 1)
  let e := E.comp Q.subtype
  obtain ⟨r, hr⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE)
  let ρ := Q.subtype.comp r
  have hfix : ∀ a : MvPolynomial J k, a.totalDegree < D → ρ (E a) = a := by
    intro a ha
    have hamem : a ∈ Q := (mem_restrictTotalDegree J (D - 1) a).mpr (by omega)
    exact congrArg Subtype.val (DFunLike.congr_fun hr ⟨a, hamem⟩)
  have hret : TensorProduct.map ρ ρ (TensorProduct.map E E t) = t := by
    clear hz
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ht
      simp only [TensorProduct.map_tmul, hfix a ha, hfix b hb]
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | smul c t _ ht => simp only [map_smul, ht]
  rw [hz, map_zero] at hret
  exact hret.symm

end Retraction

section Bialgebra

variable {B : Type w} [CommRing B] [Bialgebra k B]
  {x : J → B} (hx : ∀ j, Bialgebra.IsPrimitiveElem k (x j))

include hx

/-- Evaluation at primitive elements respects the additive coproduct. -/
theorem map_additiveComul (f : MvPolynomial J k) :
    TensorProduct.map (aeval x).toLinearMap (aeval x).toLinearMap
        ((additiveComul (k := k) (J := J)) f) = Coalgebra.comul (R := k) (aeval x f) := by
  have h : (Algebra.TensorProduct.map (aeval x) (aeval x)).comp
      (additiveComul (k := k) (J := J)) =
      (Bialgebra.comulAlgHom k B).comp (aeval x) := by
    ext j
    simp [hx j |>.comul_eq_tmul_add_tmul, add_comm]
  exact DFunLike.congr_fun h f

/-- A relation in primitive elements has zero constant coefficient. -/
theorem constantCoeff_eq_zero {f : MvPolynomial J k} (hf : aeval x f = 0) :
    constantCoeff f = 0 := by
  have h : (Bialgebra.counitAlgHom k B).comp (aeval x) =
      aeval (fun _ : J => (0 : k)) := by
    ext j
    simp [hx j |>.counit_eq_zero]
  have h' := DFunLike.congr_fun h f
  simpa [hf] using h'.symm

/-- The reduced coproduct of a relation vanishes after evaluation on both factors. -/
theorem map_reducedComul_eq_zero {f : MvPolynomial J k} (hf : aeval x f = 0) :
    TensorProduct.map (aeval x).toLinearMap (aeval x).toLinearMap (reducedComul f) = 0 := by
  rw [reducedComul_apply, map_add, map_sub, map_sub, map_additiveComul hx]
  simp [hf, constantCoeff_eq_zero hx hf]

/-- A nonzero relation of minimum total degree is a primitive polynomial. -/
theorem exists_primitive_relation
    (hrel : ∃ f : MvPolynomial J k, f ≠ 0 ∧ aeval x f = 0) :
    ∃ f : MvPolynomial J k, f ≠ 0 ∧ aeval x f = 0 ∧
      (additiveComul (k := k) (J := J)) f = f ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f := by
  classical
  have hex : ∃ D : ℕ, ∃ f : MvPolynomial J k,
      f.totalDegree = D ∧ f ≠ 0 ∧ aeval x f = 0 := by
    obtain ⟨f, hf, he⟩ := hrel
    exact ⟨f.totalDegree, f, rfl, hf, he⟩
  obtain ⟨f, hdeg, hf, he⟩ := Nat.find_spec hex
  have hmin : ∀ g : MvPolynomial J k,
      g.totalDegree < f.totalDegree → aeval x g = 0 → g = 0 := by
    intro g hg heval
    by_contra hne
    have h := Nat.find_min' hex ⟨g, rfl, hne, heval⟩
    omega
  have hc := constantCoeff_eq_zero hx he
  have hpos : 0 < f.totalDegree := by
    by_contra hn
    have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hn)
    exact hf (by simpa [← constantCoeff_eq, hc] using hC)
  have hinj : Function.Injective ((aeval x).toLinearMap.comp
      (restrictTotalDegree J k (f.totalDegree - 1)).subtype) := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hmin
    · have h := (mem_restrictTotalDegree J (f.totalDegree - 1) (a.val - b.val)).mp
        ((restrictTotalDegree J k (f.totalDegree - 1)).sub_mem a.property b.property)
      omega
    · change aeval x a.val = aeval x b.val at hab
      simpa using sub_eq_zero.mpr hab
  have hzero : reducedComul f = 0 := eq_zero_of_tensor_map_eq_zero
    (aeval x).toLinearMap hinj (reducedComul_mem f) (map_reducedComul_eq_zero hx he)
  refine ⟨f, hf, he, ?_⟩
  rw [reducedComul_apply, hc, map_zero, add_zero] at hzero
  exact sub_eq_zero.mp (by simpa [sub_sub] using hzero)

end Bialgebra

/-- A primitive polynomial is additive on every algebra's tuples. -/
theorem isAddPoly_of_additiveComul_eq {n : ℕ} {f : MvPolynomial (Fin n) k}
    (hf : (additiveComul (k := k) (J := Fin n)) f = f ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f) :
    TorusLinearization.IsAddPoly f := by
  intro A _ _ u v
  let L : MvPolynomial (Fin n) k ⊗[k] MvPolynomial (Fin n) k →ₐ[k] A :=
    Algebra.TensorProduct.lift (aeval u) (aeval v) (fun _ _ => Commute.all _ _)
  have hcomp : L.comp (additiveComul (k := k) (J := Fin n)) = aeval (u + v) := by
    ext j
    simp [L]
  have h := congrArg L hf
  rw [← AlgHom.comp_apply, hcomp] at h
  simpa [L] using h

/-- Any polynomial dependence of finitely many primitive elements contains a
nonzero additive polynomial relation. -/
theorem exists_additive_relation {n : ℕ} {B : Type w} [CommRing B] [Bialgebra k B]
    {x : Fin n → B} (hx : ∀ j, Bialgebra.IsPrimitiveElem k (x j))
    (hrel : ∃ f : MvPolynomial (Fin n) k, f ≠ 0 ∧ aeval x f = 0) :
    ∃ f : MvPolynomial (Fin n) k,
      f ≠ 0 ∧ TorusLinearization.IsAddPoly f ∧ aeval x f = 0 := by
  obtain ⟨f, hf, he, hδ⟩ := exists_primitive_relation hx hrel
  exact ⟨f, hf, isAddPoly_of_additiveComul_eq hδ, he⟩

end Langlands.GroupScheme.PrimitivePolynomial
