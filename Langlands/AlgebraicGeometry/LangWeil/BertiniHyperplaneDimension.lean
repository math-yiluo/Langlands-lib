import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

/-!
# Dimension and generators for the generic hyperplane argument

These internal lemmas preserve the dimension bound and finite generators under
algebraic closure and reduction, and extract two independent generators.
-/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplane

theorem exists_algebraicIndependent_pair_of_two_le_ringKrullDim
    (K : Type u) [Field K] {D : Type u} [CommRing D] [IsDomain D] [Algebra K D]
    {n : ℕ} (g : Fin n → D) (hg : Algebra.adjoin K (Set.range g) = ⊤)
    (hdim : 2 ≤ ringKrullDim D) :
    ∃ j l : Fin n, AlgebraicIndependent K
      ![algebraMap D (FractionRing D) (g j), algebraMap D (FractionRing D) (g l)] := by
  classical
  let : Algebra.FiniteType K D :=
    ⟨⟨Finset.univ.image g, by simpa using hg⟩⟩
  obtain ⟨s, f, hf, -, hs⟩ :=
    P2MW.S_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime.P2mIrredHyp.exists_noether_two_le
      K hdim
  have hi : AlgebraicIndependent K (fun i : Fin s => f (MvPolynomial.X i)) :=
    (MvPolynomial.algebraicIndependent_X (Fin s) K).map' hf
  have htr : (2 : Cardinal) ≤ Algebra.trdeg K D := by
    calc
      (2 : Cardinal) ≤ (s : Cardinal) := by exact_mod_cast hs
      _ ≤ Algebra.trdeg K D := by simpa using hi.lift_cardinalMk_le_trdeg
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range g)) D := by
    rw [hg]
    exact (Algebra.isIntegral_of_surjective
      (R := (⊤ : Subalgebra K D)) (B := D)
      (fun d => ⟨⟨d, Algebra.mem_top⟩, rfl⟩)).isAlgebraic
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range g)
  have hcard : (2 : Cardinal) ≤ Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg]
    exact htr
  obtain ⟨x, y, hxy⟩ := Cardinal.two_le_iff.mp hcard
  obtain ⟨j, hj⟩ := ht x.property
  obtain ⟨l, hl⟩ := ht y.property
  have hι : Function.Injective (![x, y] : Fin 2 → t) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hpair := hb.1.comp (![x, y] : Fin 2 → t) hι
  let ι : D →ₐ[K] FractionRing D := IsScalarTower.toAlgHom K D (FractionRing D)
  have hmap := hpair.map' (f := ι) (IsFractionRing.injective D (FractionRing D))
  refine ⟨j, l, ?_⟩
  convert hmap using 1
  ext i
  fin_cases i <;> simp [ι, hj, hl]

theorem ringKrullDim_le_baseChange_reduction
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] :
    ringKrullDim A ≤
      ringKrullDim ((AlgebraicClosure k ⊗[k] A) ⧸
        nilradical (AlgebraicClosure k ⊗[k] A)) := by
  have hdim : ringKrullDim A = ringKrullDim (A ⊗[k] AlgebraicClosure k) :=
    P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.P2mBertiniHyp.ringKrullDim_eq_of_isIntegral_of_injective
      (Algebra.TensorProduct.includeLeft_injective (S := A)
        (algebraMap k (AlgebraicClosure k)).injective)
  have hred : ringKrullDim ((AlgebraicClosure k ⊗[k] A) ⧸
      nilradical (AlgebraicClosure k ⊗[k] A)) =
      ringKrullDim (AlgebraicClosure k ⊗[k] A) := by
    rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_nilradical]
    exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ
  rw [hred, hdim]
  exact (ringKrullDim_eq_of_ringEquiv
    (Algebra.TensorProduct.comm k A (AlgebraicClosure k)).toRingEquiv).le

theorem adjoin_range_baseChange_reduction
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    {n : ℕ} (g : Fin n → A) (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Algebra.adjoin (AlgebraicClosure k)
      (Set.range fun i => Ideal.Quotient.mk (nilradical (AlgebraicClosure k ⊗[k] A))
        ((1 : AlgebraicClosure k) ⊗ₜ[k] g i)) = ⊤ := by
  let f := Ideal.Quotient.mkₐ (AlgebraicClosure k)
    (nilradical (AlgebraicClosure k ⊗[k] A))
  have hb : Algebra.adjoin (AlgebraicClosure k)
      (Set.range fun i => (1 : AlgebraicClosure k) ⊗ₜ[k] g i) = ⊤ := by
    simpa only [← Set.range_comp'] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
        (R := k) (A := AlgebraicClosure k) (B := A)
        (Set.range g) hg
  have hm := congrArg (Subalgebra.map f) hb
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top f).mpr Ideal.Quotient.mk_surjective] at hm
  simpa only [← Set.range_comp', f, Ideal.Quotient.mkₐ_eq_mk] using hm

/-- The three internal reductions used by the generic hyperplane proof. -/
def dimensionAndGeneratorReductions :
    (∀ (K : Type u) [Field K] (D : Type u) [CommRing D] [IsDomain D] [Algebra K D]
      (n : ℕ) (g : Fin n → D),
      Algebra.adjoin K (Set.range g) = ⊤ → 2 ≤ ringKrullDim D →
      ∃ j l : Fin n, AlgebraicIndependent K
        ![algebraMap D (FractionRing D) (g j), algebraMap D (FractionRing D) (g l)]) ∧
    (∀ (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A],
      ringKrullDim A ≤ ringKrullDim ((AlgebraicClosure k ⊗[k] A) ⧸
        nilradical (AlgebraicClosure k ⊗[k] A))) ∧
    (∀ (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
      (n : ℕ) (g : Fin n → A),
      Algebra.adjoin k (Set.range g) = ⊤ →
      Algebra.adjoin (AlgebraicClosure k)
        (Set.range fun i => Ideal.Quotient.mk (nilradical (AlgebraicClosure k ⊗[k] A))
          ((1 : AlgebraicClosure k) ⊗ₜ[k] g i)) = ⊤) :=
  ⟨fun K _ D _ _ _ _ g hg hdim =>
    exists_algebraicIndependent_pair_of_two_le_ringKrullDim K g hg hdim,
    ringKrullDim_le_baseChange_reduction,
    fun k _ A _ _ _ g hg => adjoin_range_baseChange_reduction k A g hg⟩

end Langlands.AlgebraicGeometry.LangWeil.BertiniGenericHyperplane
