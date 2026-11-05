import Langlands.GroupScheme.Unipotent.PolynomialShearGeometry
import Langlands.GroupScheme.Unipotent.PolynomialKernelAffineLine

/-! # Actual coordinate reduction for additive polynomial kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

/-- An actual ambient vector-group coordinate isomorphism after which an
additive polynomial row has a zero entry. -/
def HasPolynomialKernelZeroCoordinate (f : Fin n → k[X])
    (hf : ∀ i, IsAdditive (f i)) : Prop :=
  ∃ (g : Fin n → k[X]) (hg : ∀ i, IsAdditive (g i))
    (e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
      VectorGroup.groupScheme (CommRingCat.of k) n),
    e.hom ≫ polynomialRow f hf = polynomialRow g hg ∧ ∃ j, g j = 0

private theorem hasPolynomialKernelZeroCoordinate_aux (p : ℕ) [ExpChar k p] :
    ∀ N : ℕ, ∀ f : Fin n → k[X], (∑ i, (f i).natDegree) ≤ N →
      ∀ hf : ∀ i, IsAdditive (f i),
      ∀ φ : Fin n → k[X], (∀ i, (φ i).coeff 0 = 0) → φ ≠ 0 →
      (∑ i, (f i).comp (φ i)) = 0 → HasPolynomialKernelZeroCoordinate f hf := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hN hf φ hφ hφ0 hrel
    by_cases hf0 : ∀ i, f i ≠ 0
    · have hφpos : ∃ i, 0 < (φ i).natDegree := by
        by_contra hn
        apply hφ0
        funext i
        have hd : (φ i).natDegree = 0 := by
          have := not_exists.mp hn i
          omega
        rw [eq_C_of_natDegree_eq_zero hd, hφ i, C_0]
        rfl
      obtain ⟨b, hb0, hb⟩ := exists_principalPart_zero_of_sum_comp_eq_zero f φ
        (fun i => (hf i).coeff_zero) hφpos hrel
      obtain ⟨j, a, q, ha, hqj, hq, hlt⟩ :=
        exists_degree_reducing_polynomialShear p f hf hf0 b hb0 hb
      let f' := polynomialShearRow j f q
      have hf' : ∀ i, IsAdditive (f' i) := polynomialShearRow_isAdditive j f q hf hq
      have hsum : (∑ i, (f' i).natDegree) < ∑ i, (f i).natDegree := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hi : i = j
          · simpa [f', polynomialShearRow, hi] using hlt.le
          · simp [f', polynomialShearRow, hi]
        · exact ⟨j, Finset.mem_univ j,
            by simpa [f', polynomialShearRow] using hlt⟩
      let φ' := polynomialShearInverse j a q φ
      have hφ' : ∀ i, (φ' i).coeff 0 = 0 :=
        polynomialShearInverse_coeff_zero j a q φ (fun i => (hq i).coeff_zero) hφ
      have hφ'0 : φ' ≠ 0 := by
        intro hz
        have hinv : polynomialShear j q φ' = φ :=
          polynomialShear_inverse j a ha q φ hqj
        rw [hz, polynomialShear_zero j q hq] at hinv
        exact hφ0 hinv.symm
      have hrel' : (∑ i, (f' i).comp (φ' i)) = 0 := by
        change (∑ i, (if i = j then ∑ l, (f l).comp (q l) else f i).comp (φ' i)) = 0
        rw [← sum_comp_polynomialShear j f q φ' hf]
        change (∑ i, (f i).comp (polynomialShear j q
          (polynomialShearInverse j a q φ) i)) = 0
        rw [polynomialShear_inverse j a ha q φ hqj]
        exact hrel
      obtain ⟨g, hg, e, he, hzero⟩ :=
        ih _ (hsum.trans_le hN) f' le_rfl hf' φ' hφ' hφ'0 hrel'
      refine ⟨g, hg, e ≪≫ polynomialShearIso j a ha q hqj hq, ?_, hzero⟩
      change (e.hom ≫ (polynomialShearIso j a ha q hqj hq).hom) ≫
        polynomialRow f hf = polynomialRow g hg
      rw [Category.assoc, polynomialShearIso_hom_comp_polynomialRow]
      exact he
    · obtain ⟨j, hj⟩ : ∃ j, f j = 0 := by simpa using hf0
      exact ⟨f, hf, Iso.refl _, Category.id_comp _, j, hj⟩

/-- A nonzero pointed polynomial kernel curve yields an actual vector-group
coordinate change with a zero row entry. -/
theorem hasPolynomialKernelZeroCoordinate_of_pointed
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : Fin n → k[X]) (hφ : ∀ i, (φ i).coeff 0 = 0) (hφ0 : φ ≠ 0)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) : HasPolynomialKernelZeroCoordinate f hf :=
  hasPolynomialKernelZeroCoordinate_aux (ringExpChar k) _ f le_rfl hf φ hφ hφ0 hrel

/-- Every nonconstant polynomial kernel curve gives an actual coordinate
isomorphism making one separated-variable row entry zero. -/
theorem hasPolynomialKernelZeroCoordinate_of_nonconstant
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : Fin n → k[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) : HasPolynomialKernelZeroCoordinate f hf := by
  obtain ⟨ψ, hψ0, hψ, hψrel⟩ := exists_additive_kernel_curve f hf φ hφ hrel
  exact hasPolynomialKernelZeroCoordinate_of_pointed f hf ψ
    (fun i => (hψ i).coeff_zero) hψ0 hψrel

/-- Failure of actual affine-line constancy gives the actual coordinate
isomorphism and a zero row entry, over every field. -/
theorem hasPolynomialKernelZeroCoordinate_of_not_hasConstantAffineLineMaps
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hG : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    HasPolynomialKernelZeroCoordinate f hf := by
  obtain ⟨φ, hφ, hrel⟩ :=
    hasNonconstantPolynomialKernelCurve_of_not_hasConstantAffineLineMaps f hf hG
  exact hasPolynomialKernelZeroCoordinate_of_nonconstant f hf φ hφ hrel

/-- A nonconstant polynomial kernel curve over an algebraic Galois extension
already yields an actual coordinate change over the original field. -/
theorem hasPolynomialKernelZeroCoordinate_of_nonconstant_galois
    {K : Type*} [Field K] [Algebra k K] [IsGalois k K]
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : Fin n → K[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0) :
    HasPolynomialKernelZeroCoordinate f hf := by
  have h : HasNonconstantPolynomialKernelCurve f :=
    (hasNonconstantPolynomialKernelCurve_iff_of_isGalois (K := K) f hf).mp ⟨φ, hφ, hrel⟩
  obtain ⟨ψ, hψ, hψrel⟩ := h
  exact hasPolynomialKernelZeroCoordinate_of_nonconstant f hf ψ hψ hψrel

end Langlands.GroupScheme.Unipotent
