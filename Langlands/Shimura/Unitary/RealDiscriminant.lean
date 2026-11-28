import Langlands.Shimura.Unitary.HermitianDiscriminantComparison
import Langlands.Shimura.Unitary.HarrisLevels
import Mathlib.RingTheory.Complex

/-! # The discriminant invariant of a prescribed real signature -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.GaloisCohomology Langlands.Galois
open Langlands.LocalClassField Langlands.LocalClassField.FiniteArtinTransport
open Langlands.ClassFieldTheory.Local

private theorem det_signatureMatrix {n r : ℕ} (hr : r ≤ n) :
    (signatureMatrix n r).det = (-1 : ℂ) ^ (n - r) := by
  classical
  rw [signatureMatrix, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    one_pow, one_mul]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => i.val < r)
  rw [Fin.card_filter_val_lt, min_eq_right hr, Finset.card_univ, Fintype.card_fin] at h
  congr 1
  omega

private theorem real_mem_normSubgroup_iff_pos (d : ℝˣ) :
    d ∈ normSubgroup ℝ ℂ ↔ 0 < (d : ℝ) := by
  constructor
  · rintro ⟨z, rfl⟩
    change 0 < Algebra.norm ℝ (z : ℂ)
    rw [Algebra.norm_complex_eq]
    exact Complex.normSq_pos.mpr z.ne_zero
  · intro hd
    let a : ℂ := (Real.sqrt (d : ℝ) : ℂ)
    have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hd).ne'
    refine ⟨Units.mk0 a ha, Units.ext ?_⟩
    change Algebra.norm ℝ ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = _
    rw [Algebra.norm_complex_eq]
    change Complex.normSq ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = _
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt hd.le]

private theorem denominatorMap_two_natCast (k : ℕ) :
    denominatorMap 2 (by decide) (k : ZMod 2) =
      if Even k then 0 else rationalClass (1 / 2) := by
  have hzero : (k : ZMod 2) = 0 ↔ Even k := by
    rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]
  by_cases h : Even k
  · simp [h, hzero.mpr h]
  · have hk : (k : ZMod 2) = 1 := by
      apply ZMod.val_injective 2
      have hlt := ZMod.val_lt (k : ZMod 2)
      have hne : (k : ZMod 2).val ≠ 0 := fun hv =>
        h (hzero.mp (ZMod.val_injective 2 (hv.trans ZMod.val_zero.symm)))
      rw [ZMod.val_one'' (by decide)]
      omega
    rw [hk, ite_eq_right h]
    change (denominatorEquiv 2 (by decide) 1 : RationalModIntegers) = _
    simp [denominatorEquiv_one, reciprocalClass, one_div]

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {A : CSA.{v, v} K} [Algebra E A] [IsScalarTower E K A] {m : ℕ}

set_option maxRecDepth 8192 in
/-- The real discriminant invariant is the class of half the parity of
`m + (2m - r)` for a signature with `r` positive lines. -/
theorem realLocalInvariant_discriminant
    (P : EvenDiscriminantPresentation E A m) (D : CentralSimpleUnitaryData E K A (2 * m))
    (ι : PlaceEmbeddings E (AlgebraicClosure E)) (w : InfinitePlace E) (r : ℕ)
    (hr : HasSignature D.toSecondKindInvolution
      (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)) (2 * m) r) :
    realLocalInvariant ι w
      (brauerEquiv E (AlgebraicClosure E) (P.brauerClass D.toSecondKindInvolution)) =
      denominatorMap 2 (by decide) ((m + (2 * m - r) : ℕ) : ZMod 2) := by
  classical
  let F := w.Completion
  let hw : w.IsReal := IsTotallyReal.isReal w
  let τ := InfinitePlace.embedding_of_isReal hw
  let : Algebra E ℝ := τ.toAlgebra
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j : F ≃ₐ[E] ℝ := AlgEquiv.ofRingEquiv (f := ψ) fun a => by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap E F a) = τ a
    rw [InfinitePlace.Completion.algebraMap_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    rfl
  let : Algebra F ℂ := Algebra.compHom ℂ ψ.toRingHom
  let : Algebra E ℂ := Algebra.compHom ℂ τ
  let : IsScalarTower E F ℂ := IsScalarTower.of_algebraMap_eq fun a => by
    change (τ a : ℂ) = (ψ (algebraMap E F a) : ℂ)
    exact congrArg Complex.ofReal (j.commutes a).symm
  let k : K →+* ℂ := embeddingOverReal τ
  let : Algebra K ℂ := k.toAlgebra
  let : IsScalarTower E K ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (embeddingOverReal_apply_algebraMap (K := K) τ a).symm
  have hdeg : Module.finrank F ℂ = 2 :=
    (Algebra.finrank_eq_of_equiv_equiv ψ (RingEquiv.refl ℂ) (RingHom.ext fun _ => rfl)).trans
      Complex.finrank_real_complex
  let : IsQuadraticExtension F ℂ := ⟨hdeg⟩
  let : NeZero (2 * m) := ⟨by have := D.rank_gt_one; omega⟩
  have hk : k.comp (algebraMap E K) = Complex.ofRealHom.comp τ :=
    RingHom.ext (embeddingOverReal_apply_algebraMap (K := K) τ)
  obtain ⟨e₀, he₀, hcenter₀⟩ := hr.exists_centerCompatible k hk
  let e₁ : F ⊗[E] A ≃ₐ[E] ℝ ⊗[E] A := Algebra.TensorProduct.congr j AlgEquiv.refl
  let e : F ⊗[E] A ≃ₐ[F] Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₀.toRingEquiv) fun a => by
      change e₀ (algebraMap ℝ (ℝ ⊗[E] A) (ψ a)) =
        algebraMap ℝ (Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) (ψ a)
      exact e₀.commutes (ψ a)
  have hepure (a : A) : e (1 ⊗ₜ[E] a) = e₀ (1 ⊗ₜ[E] a) := by
    change e₀ ((j 1) ⊗ₜ[E] a) = _
    rw [map_one]
  have he (x : K) : e (1 ⊗ₜ[E] algebraMap K A x) =
      algebraMap ℂ (Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) (algebraMap K ℂ x) :=
    (hepure _).trans (hcenter₀ x)
  let φ : ℂ ≃ₐ[F] ℂ :=
    { Complex.conjAe.toRingEquiv with
      commutes' := fun a => Complex.conj_ofReal (ψ a) }
  have hφ : φ ≠ 1 := by
    intro h
    have hi := congrArg (fun g : ℂ ≃ₐ[F] ℂ => (g Complex.I).im) h
    change (star Complex.I).im = Complex.I.im at hi
    norm_num at hi
  have hφK (x : K) :
      φ (algebraMap K ℂ x) = algebraMap K ℂ (cmConjugation E K x) :=
    (embedding_cmConjugation E K k x).symm
  let H := signatureUnit (2 * m) r
  have hHerm : ((H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ).map φ)ᵀ = H :=
    signatureMatrix_star (2 * m) r
  have hAdj (a : A) : e (1 ⊗ₜ[E] D.involution a) =
      ((H⁻¹ : GL (Fin (2 * m)) ℂ) : Matrix _ _ ℂ) * ((e (1 ⊗ₜ[E] a)).map φ)ᵀ *
        (H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ) := by
    have h := he₀ (1 ⊗ₜ[E] a)
    rw [AlgebraInvolution.baseChange_tmul, ← hepure, ← hepure] at h
    exact h
  let nneg := m + (2 * m - r)
  let d := (-1 : Fˣ) ^ nneg
  have hdet : (GeneralLinearGroup.det H : ℂ) = (-1 : ℂ) ^ (2 * m - r) :=
    det_signatureMatrix hr.1
  have hd : algebraMap F ℂ (d : F) = (-1 : ℂ)^m * (GeneralLinearGroup.det H : ℂ) := by
    change algebraMap F ℂ ((-1 : F) ^ nneg) = _
    rw [map_pow, map_neg, map_one, hdet, ← pow_add]
  have hnorm := discriminantClass_eq_zero_of_hermitian_chart P D φ hφ hφK e he H hHerm hAdj d hd
  have hd_norm : d ∈ normSubgroup F ℂ ↔ Even nneg := by
    rw [← mem_normSubgroup_map_iff ψ (RingEquiv.refl ℂ) (RingHom.ext fun _ => rfl),
      real_mem_normSubgroup_iff_pos]
    change 0 < ψ ((-1 : F)^nneg) ↔ _
    rw [map_pow, map_neg, map_one, neg_one_pow_eq_ite]
    split_ifs with h <;> simp [h]
  rw [realLocalInvariant, realBrauerLocalization_brauerEquiv, realInvariant,
    map_eq_zero_iff _ (brauerEquiv F (AlgebraicClosure F)).injective,
    hnorm, hd_norm, denominatorMap_two_natCast]
  by_cases h : Even nneg <;> simp [nneg] at h ⊢

end Langlands.Shimura.FiniteUnitary
