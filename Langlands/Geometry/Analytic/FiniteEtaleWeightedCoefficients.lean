import Langlands.Geometry.Analytic.FiniteProjectiveNormPolynomial
import Langlands.Geometry.Analytic.WeightedLinearFactors
import Langlands.Geometry.Analytic.EtaleOpenMap.FiniteBanachLyingOver
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Weighted coefficient criterion for finite étale affinoid fibres -/

noncomputable section

universe u

namespace Langlands.Analytic

open MvPolynomial
open scoped TensorProduct

private theorem exists_apply_ne_zero {S L σ : Type*} [CommRing S] [Field L]
    (φ : S →+* L) (b : σ → S) (hb : Ideal.span (Set.range b) = ⊤) :
    ∃ i, φ (b i) ≠ 0 := by
  by_contra! h
  have hs : Ideal.span (Set.range b) ≤ RingHom.ker φ :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  have h1 : (1 : S) ∈ RingHom.ker φ := hs (by rw [hb]; exact Submodule.mem_top)
  exact one_ne_zero ((map_one φ).symm.trans h1)

/-- The coefficients of the norm polynomial generate the unit ideal whenever its input
elements generate the unit ideal in the finite étale algebra. -/
private theorem normPolynomial_span_eq_top {R S : Type u} {σ : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S]
    [Fintype σ] (b : σ → S) (hb : Ideal.span (Set.range b) = ⊤) (P : MvPolynomial σ R)
    (hP : ∀ (L : Type u) [CommRing L] [Algebra R L] (ι : Type u) [Fintype ι]
      (e : L ⊗[R] S ≃ₐ[L] (ι → L)),
      MvPolynomial.map (algebraMap R L) P =
        ∏ j : ι, ∑ i : σ, C (e (1 ⊗ₜ[R] b i) j) * X i) :
    Ideal.span (Set.range P.coeff) = ⊤ := by
  classical
  by_contra h
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal _ h
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let L := AlgebraicClosure (R ⧸ m)
  let : Algebra R L := ((algebraMap (R ⧸ m) L).comp (Ideal.Quotient.mk m)).toAlgebra
  let T := L ⊗[R] S
  let ι := PrimeSpectrum T
  have : IsArtinianRing T := IsArtinianRing.of_finite L T
  let : Fintype ι := Fintype.ofFinite ι
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L T
  have hzero : MvPolynomial.map (algebraMap R L) P = 0 := by
    ext d
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    change algebraMap (R ⧸ m) L (Ideal.Quotient.mk m (P.coeff d)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (hPm (Ideal.subset_span (Set.mem_range_self d))), map_zero]
  have hnonzero : (∏ j : ι, ∑ i : σ, C (e (1 ⊗ₜ[R] b i) j) * X i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    let φ : S →+* L := ((Pi.evalAlgHom L (fun _ : ι => L) j).toRingHom.comp
      e.toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom
    obtain ⟨i, hi⟩ := exists_apply_ne_zero φ b hb
    intro heq
    have hc := congrArg (fun q : MvPolynomial σ L => q.coeff (Finsupp.single i 1)) heq
    simp only [coeff_sum, C_mul_X_eq_monomial, coeff_monomial, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply,
      Finsupp.single_left_inj one_ne_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    exact hi hc
  exact hnonzero ((hP L ι e).symm.trans hzero)

private theorem exists_apply_eq_eval {L ι : Type*} [Field L] [Fintype ι]
    (φ : (ι → L) →ₐ[L] L) : ∃ i, ∀ a, φ a = a i := by
  classical
  have hsum : (∑ i : ι, Pi.single i (1 : L)) = 1 := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨i, hi⟩ : ∃ i, φ (Pi.single i 1) ≠ 0 := by
    by_contra! h
    have heq := congrArg φ hsum
    simp [map_sum, h] at heq
  refine ⟨i, fun a => ?_⟩
  have heq : a * Pi.single i 1 = algebraMap L (ι → L) (a i) * Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hj]
  have h := congrArg φ heq
  simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply] at h
  exact mul_right_cancel₀ hi h

private theorem exists_normPreserving_to_isAlgClosed (F : Type u)
    [NormedField F] [IsUltrametricDist F] [CompleteSpace F] :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : IsAlgClosed L)
      (φ : F →+* L), ∀ c, ‖φ c‖ = ‖c‖ := by
  obtain ⟨E⟩ := FiniteRadiusRealization.nonempty (K := F) (fun _ : Unit => (2 : ℝ))
    (by intro _; norm_num)
  let : NontriviallyNormedField E.L :=
    { (inferInstance : NormedField E.L) with
      non_trivial := ⟨E.c (), by rw [E.norm_c]; norm_num⟩ }
  let L := AlgebraicClosure E.L
  let : NormedField L := spectralNorm.normedField E.L L
  let : NormedAlgebra E.L L := spectralNorm.normedAlgebra E.L L
  have : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := E.L) (L := L))
  refine ⟨L, inferInstance, inferInstance, inferInstance, (algebraMap E.L L).comp E.ι, ?_⟩
  intro c
  change ‖algebraMap E.L L (E.ι c)‖ = ‖c‖
  rw [norm_algebraMap', E.norm_ι]

private theorem weightedCoefficients_iff_exists_algHom {R S L : Type u}
    [CommRing R] [CommRing S] [NormedField L] [IsUltrametricDist L] [IsAlgClosed L]
    [Algebra R S] [Algebra R L] [Module.Finite R S] [Algebra.Etale R S]
    {n : ℕ} (b : Fin (n + 1) → S) (hb : Ideal.span (Set.range b) = ⊤)
    (w : Fin (n + 1) → ℝ) (hw : ∀ j, 0 < w j) (P : MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ (ι : Type u) [Fintype ι] (e : L ⊗[R] S ≃ₐ[L] (ι → L)),
      MvPolynomial.map (algebraMap R L) P =
        ∏ j : ι, ∑ i, C (e (1 ⊗ₜ[R] b i) j) * X i) :
    (∃ d : Fin (n + 1) →₀ ℕ, 0 < d 0 ∧ ∀ k,
        ‖algebraMap R L (P.coeff k)‖ * monomialWeight w k ≤
          ‖algebraMap R L (P.coeff d)‖ * monomialWeight w d) ↔
      ∃ ψ : S →ₐ[R] L, ∀ j, ‖ψ (b j)‖ * w j ≤ ‖ψ (b 0)‖ * w 0 := by
  let T := L ⊗[R] S
  let ι := PrimeSpectrum T
  have : IsArtinianRing T := IsArtinianRing.of_finite L T
  let : Fintype ι := Fintype.ofFinite ι
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L T
  let ψ (i : ι) : S →ₐ[R] L :=
    (((Pi.evalAlgHom L (fun _ : ι => L) i).comp e.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  simp_rw [← MvPolynomial.coeff_map, hP ι e]
  have hweights := exists_maximalWeightedCoeff_pos_iff w hw (fun i j => e (1 ⊗ₜ[R] b j) i)
    (fun i => exists_apply_ne_zero (ψ i).toRingHom b hb)
  dsimp only at hweights
  rw [hweights]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ψ i, hi⟩
  · rintro ⟨φ, hφ⟩
    have hcomm (a : L) (c : S) : Commute ((AlgHom.id L L) a) (φ c) :=
      Commute.all _ _
    let φ' : T →ₐ[L] L := Algebra.TensorProduct.lift (AlgHom.id L L) φ hcomm
    obtain ⟨i, hi⟩ := exists_apply_eq_eval (φ'.comp e.symm.toAlgHom)
    have heq (s : S) : φ s = e (1 ⊗ₜ[R] s) i := by
      have h := hi (e (1 ⊗ₜ[R] s))
      change φ' (e.symm (e (1 ⊗ₜ[R] s))) = _ at h
      rw [e.symm_apply_apply] at h
      change Algebra.TensorProduct.lift (AlgHom.id L L) φ hcomm (1 ⊗ₜ[R] s) = _ at h
      rw [Algebra.TensorProduct.lift_tmul (AlgHom.id L L) φ hcomm,
        AlgHom.id_apply, one_mul] at h
      exact h
    exact ⟨i, fun j => by simpa only [← heq] using hφ j⟩

namespace BanachSpectrum

/-- A weighted finite étale fibre condition is detected by coefficients of a single
polynomial over the base. Its coefficients generate the unit ideal. -/
theorem exists_weightedCoeff_iff {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {A B : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    {n : ℕ} (b : Fin (n + 1) → B) (hb : Ideal.span (Set.range b) = ⊤)
    (w : Fin (n + 1) → ℝ) (hw : ∀ j, 0 < w j) :
    ∃ P : MvPolynomial (Fin (n + 1)) A, Ideal.span (Set.range P.coeff) = ⊤ ∧
      ∀ x : BanachSpectrum A,
        (∃ y : BanachSpectrum B, comap f.toBoundedRingHom y = x ∧
          ∀ j, y (b j) * w j ≤ y (b 0) * w 0) ↔
        (∃ d : Fin (n + 1) →₀ ℕ, 0 < d 0 ∧ ∀ k,
          x (P.coeff k) * monomialWeight w k ≤ x (P.coeff d) * monomialWeight w d) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite A B := he.1
  have : Algebra.Etale A B := he.2
  have : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Fin (n + 1)) A,
      ∀ (L : Type u) [CommRing L] [Algebra A L] (ι : Type u) [Fintype ι]
        (e : L ⊗[A] B ≃ₐ[L] (ι → L)),
        MvPolynomial.map (algebraMap A L) P =
          ∏ j : ι, ∑ i, C (e (1 ⊗ₜ[A] b i) j) * X i :=
    exists_normPolynomial (R := A) b
  refine ⟨P, normPolynomial_span_eq_top (R := A) (S := B) b hb P hP, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨L, _, _, _, ι, hι⟩ := exists_normPreserving_to_isAlgClosed
      (CompletedResidueField K y)
    let ρ : B →+* L := ι.comp (completedResidueMap K y).toAlgHom.toRingHom
    have hρ (c : B) : ‖ρ c‖ = y c :=
      (hι _).trans (norm_completedResidueMap K y c)
    let : Algebra A L := (ρ.comp f.toAlgHom.toRingHom).toAlgebra
    let ψ : B →ₐ[A] L := { ρ with commutes' := fun _ => rfl }
    have hbase (a : A) : ‖algebraMap A L a‖ = x a :=
      (hρ (f a)).trans (congrArg (fun s : BanachSpectrum A => s a) hy)
    have hc := (weightedCoefficients_iff_exists_algHom b hb w hw P (hP L)).mpr
      ⟨ψ, fun j => by simpa only [show ∀ c, ‖ψ c‖ = y c from hρ] using h j⟩
    simpa only [hbase] using hc
  · intro h
    obtain ⟨L, _, _, _, ι, hι⟩ := exists_normPreserving_to_isAlgClosed
      (CompletedResidueField K x)
    let ρ : A →+* L := ι.comp (completedResidueMap K x).toAlgHom.toRingHom
    let : Algebra A L := ρ.toAlgebra
    have hbase (a : A) : ‖algebraMap A L a‖ = x a :=
      (hι _).trans (norm_completedResidueMap K x a)
    obtain ⟨ψ, hψ⟩ := (weightedCoefficients_iff_exists_algHom b hb w hw P (hP L)).mp
      (by simpa only [hbase] using h)
    have hψbase (a : A) : ‖ψ (f a)‖ = x a :=
      (congrArg norm (ψ.commutes a)).trans (hbase a)
    obtain ⟨M, hM, hbound⟩ := hf.exists_norm_bound ψ.toRingHom
      (fun a => (hψbase a).trans_le (x.le_norm a))
    let ψb : BoundedRingHom B L := { ψ.toRingHom with bounded := ⟨M, hM, hbound⟩ }
    exact ⟨comap ψb (fieldPoint L), ext hψbase, hψ⟩

end BanachSpectrum

end Langlands.Analytic
