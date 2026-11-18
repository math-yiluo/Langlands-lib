import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChange
import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Langlands.Geometry.Analytic.FlatTargetDescent
import Langlands.Geometry.Analytic.SpectralMinpoly
import Langlands.Geometry.Analytic.TateNoetherian
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Flatness of the chart algebras of affine analytification -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open GeneralizedTateAlgebra

private theorem completion_factor_eval {R : Type u} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    change Ideal.Quotient.mk (I ^ m) (a n) = Ideal.Quotient.mk (I ^ m) (a m)
    have h : (I ^ m • ⊤ : Ideal R) = I ^ m := by simp
    have ha : Ideal.Quotient.mk (I ^ m • ⊤) (a n) =
        Ideal.Quotient.mk (I ^ m • ⊤) (a m) := a.mk_eq_mk hmn
    simpa only [Ideal.quotientEquivAlgOfEq_mk] using congrArg (Ideal.quotientEquivAlgOfEq R h) ha

/-- Compatible quotient isomorphisms give an isomorphism on the adic completions. -/
private theorem flat_completion_of_quotient_equiv {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (I : Ideal R) (J : Ideal S) (q : (n : ℕ) → (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (hq : ∀ n x, q n (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk (J ^ n) (algebraMap R S x)) :
    Module.Flat R (AdicCompletion J S) := by
  have hn {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hmn (q n x) = q m (Ideal.Quotient.factorPow I hmn x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hq]
    exact (hq m x).symm
  let f (n : ℕ) := (q n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) : (Ideal.Quotient.factorPow J hmn).comp (f n) = f m := by
    ext x
    change Ideal.Quotient.factorPow J hmn (q n (AdicCompletion.evalₐ I n x)) =
      q m (AdicCompletion.evalₐ I m x)
    rw [hn, completion_factor_eval]
  let g (n : ℕ) := (q n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom
  have hg {m n : ℕ} (hmn : m ≤ n) : (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    ext x
    apply (q m).injective
    change q m (Ideal.Quotient.factorPow I hmn ((q n).symm (AdicCompletion.evalₐ J n x))) =
      q m ((q m).symm (AdicCompletion.evalₐ J m x))
    rw [← hn, RingEquiv.apply_symm_apply, completion_factor_eval, RingEquiv.apply_symm_apply]
  let F := AdicCompletion.liftRingHom J f hf
  let G := AdicCompletion.liftRingHom I g hg
  have hF (n : ℕ) (x : AdicCompletion I R) :
      AdicCompletion.evalₐ J n (F x) = q n (AdicCompletion.evalₐ I n x) :=
    AdicCompletion.evalₐ_liftRingHom J f hf n x
  have hG (n : ℕ) (x : AdicCompletion J S) :
      AdicCompletion.evalₐ I n (G x) = (q n).symm (AdicCompletion.evalₐ J n x) :=
    AdicCompletion.evalₐ_liftRingHom I g hg n x
  let Fₐ : AdicCompletion I R →ₐ[R] AdicCompletion J S :=
    ⟨F, fun x => AdicCompletion.ext_evalₐ fun n => by
      change AdicCompletion.evalₐ J n (F (algebraMap R (AdicCompletion I R) x)) =
        AdicCompletion.evalₐ J n (algebraMap R (AdicCompletion J S) x)
      rw [hF, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
      simp only [AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply, hq]⟩
  have hbij : Function.Bijective Fₐ := ⟨
    (show Function.LeftInverse G F from fun x =>
      AdicCompletion.ext_evalₐ fun n => by rw [hG, hF, RingEquiv.symm_apply_apply]).injective,
    (show Function.RightInverse G F from fun x =>
      AdicCompletion.ext_evalₐ fun n => by rw [hF, hG, RingEquiv.apply_symm_apply]).surjective⟩
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofBijective Fₐ hbij).symm.toLinearEquiv

private abbrev unitRadius (n : ℕ) := PositivePolyradius.unit (Fin n)

private def strictPolynomialMap (K : Type u) [NormedField K] [IsUltrametricDist K] (n : ℕ) :
    MvPolynomial (Fin n) K →ₐ[K] StrictTateAlgebra (Fin n) K :=
  (unitAlgEquiv K).toAlgHom.comp (GeneralizedTateAlgebra.polynomialMap (unitRadius n) K)

section Strict

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

private theorem strictPolynomialMap_coeff (p : MvPolynomial (Fin n) K) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff d (strictPolynomialMap K n p).val = p.coeff d :=
  GeneralizedTateAlgebra.coeff_polynomialMap (unitRadius n) K p d

private theorem strictPolynomialMap_injective : Function.Injective (strictPolynomialMap K n) := by
  intro p q he
  ext d
  simpa only [strictPolynomialMap_coeff] using
    congrArg (fun f : StrictTateAlgebra (Fin n) K => MvPowerSeries.coeff d f.val) he

private theorem strictPolynomialMap_dense : DenseRange (strictPolynomialMap K n) :=
  (unitAlgEquiv K).surjective.denseRange.comp
    (denseRange_polynomialMap (unitRadius n) K) (isometry_unitAlgEquiv K).continuous

private theorem norm_strictPolynomialMap_X (i : Fin n) :
    ‖strictPolynomialMap K n (MvPolynomial.X i)‖ = 1 := by
  change ‖unitAlgEquiv K (GeneralizedTateAlgebra.polynomialMap (unitRadius n) K _)‖ = 1
  rw [norm_unitAlgEquiv]
  change ‖MvPolynomial.aeval (X (unitRadius n) K) (MvPolynomial.X i)‖ = 1
  rw [MvPolynomial.aeval_X, norm_X, norm_one, one_mul]
  rfl

variable [CompleteSpace K]

/-- A field quotient of the unit Tate algebra is finite over its coefficient field. -/
private theorem finite_strictFieldQuotient (M : Ideal (StrictTateAlgebra (Fin n) K))
    [M.IsMaximal] : Module.Finite K (StrictTateAlgebra (Fin n) K ⧸ M) := by
  let B : PresentedStrictAffinoidAlgebra K := ⟨n, M, isClosed_ideal_of_noetherian_banach (K := K) M⟩
  have hB : IsField B := by
    change IsField (StrictTateAlgebra (Fin n) K ⧸ M)
    let _ := Ideal.Quotient.field M
    exact Field.toIsField _
  have : Nontrivial B := hB.nontrivial
  obtain ⟨k, _, g, hg, hfinite⟩ := B.exists_noetherNormalization
  let T := StrictTateAlgebra (Fin k) K
  let _ : Algebra T B := g.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K T B := IsScalarTower.of_algebraMap_eq fun x => (g.toAlgHom.commutes x).symm
  have : Module.Finite T B := hfinite
  have hfield : IsField T := isField_of_isIntegral_of_isField hg hB
  have hk : k = 0 := by
    by_contra h
    let i : Fin k := ⟨0, Nat.pos_of_ne_zero h⟩
    let c : T →+* K := MvPowerSeries.constantCoeff.comp
      (Langlands.Analytic.restrictedSubalgebra (Fin k) K).val.toRingHom
    have hX : strictPolynomialMap K k (MvPolynomial.X i) ≠ 0 := by
      intro hzero
      exact MvPolynomial.X_ne_zero i (strictPolynomialMap_injective (hzero.trans (map_zero _).symm))
    have hc : c (strictPolynomialMap K k (MvPolynomial.X i)) = 0 := by
      change MvPowerSeries.coeff (0 : Fin k →₀ ℕ)
        (strictPolynomialMap K k (MvPolynomial.X i)).val = 0
      rw [strictPolynomialMap_coeff, MvPolynomial.coeff_X]
      simp
    let _ : Field T := hfield.toField
    exact hX (c.injective (hc.trans (map_zero c).symm))
  have hsurj : Function.Surjective (algebraMap K T) := by
    subst k
    exact StrictTateAlgebra.zeroVariables_algebraMap_surjective
  have : Module.Finite K T := Module.Finite.of_surjective (Algebra.linearMap K T) hsurj
  exact (show Module.Finite K B from Module.Finite.trans T B)

/-- An element in the norm unit ball of a finite Banach field algebra is integral
    over the scalar norm unit ball. -/
private theorem isIntegral_unitBall_of_finite {E : Type u}
    [NormedCommRing E] [NormedAlgebra K E] [Module.Finite K E]
    (hE : IsField E) (x : E) (hx : ‖x‖ ≤ 1) : IsIntegral (normUnitBallSubring K) x := by
  let _ : Field E := hE.toField
  let C := AlgebraicClosure K
  let _ : NormedField C := spectralNorm.normedField K C
  let _ : NormedAlgebra K C := spectralNorm.normedAlgebra K C
  let _ : IsUltrametricDist C := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K := K) (L := C))
  let p := minpoly K x
  have hp : p.Monic := minpoly.monic (IsIntegral.of_finite K x)
  have hroots : ∀ y ∈ (p.map (algebraMap K C)).roots, ‖y‖ ≤ 1 := by
    intro y hy
    have hy' : Polynomial.aeval y p = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using
        (Polynomial.mem_roots (hp.map (algebraMap K C)).ne_zero).mp hy
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (F := K) (E := E) (K := C)
      (fun z => ⟨IsIntegral.of_finite K z, IsAlgClosed.splits _⟩) hy'
    let L : E →L[K] C :=
      { φ.toLinearMap with cont := φ.toLinearMap.continuous_of_finiteDimensional }
    have hf : φ.toRingHom.IsBounded := ⟨‖L‖ + 1, by positivity, fun a =>
      (L.le_opNorm a).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a))⟩
    let ψ : BoundedRingHom E C := ⟨φ.toRingHom, hf⟩
    let t := BanachSpectrum.comap ψ (BanachSpectrum.fieldPoint C)
    have ht := t.le_norm x
    change ‖φ x‖ ≤ ‖x‖ at ht
    exact hφ ▸ ht.trans hx
  have hcoeff := coeff_norm_le_one_of_roots (p.map (algebraMap K C)) (hp.map _)
    (IsAlgClosed.splits _) hroots
  let U := normUnitBallSubring K
  have hpU : p ∈ Polynomial.lifts U.subtype := (Polynomial.lifts_iff_coeff_lifts p).mpr
    fun j => ⟨⟨p.coeff j, by
      change ‖p.coeff j‖ ≤ 1
      simpa only [Polynomial.coeff_map, norm_algebraMap'] using hcoeff j⟩, rfl⟩
  obtain ⟨q, hq⟩ := hpU
  change q.map U.subtype = p at hq
  have hm : q.Monic := by
    exact Polynomial.monic_of_injective U.subtype_injective (hq ▸ hp)
  refine ⟨q, hm, ?_⟩
  have h := minpoly.aeval K x
  change q.map (algebraMap U K) = p at hq
  rw [show minpoly K x = p from rfl, ← hq, Polynomial.aeval_map_algebraMap] at h
  exact h

/-- Coordinate integrality gives a linear extension of a polynomial quotient map
from the Gauss-normed polynomial ring to its Tate completion. -/
private theorem exists_strictPolynomial_extension {E : Type u} [CommRing E] [Algebra K E]
    (q : MvPolynomial (Fin n) K →ₐ[K] E) (hq : Function.Surjective q)
    (hint : ∀ i, IsIntegral (normUnitBallSubring K) (q (MvPolynomial.X i))) :
    ∃ (d : ℕ) (e : E ≃ₗ[K] (Fin d → K))
      (L : StrictTateAlgebra (Fin n) K →L[K] (Fin d → K)),
      ∀ p, L (strictPolynomialMap K n p) = e (q p) := by
  classical
  let U := normUnitBallSubring K
  let x : Fin n → E := q ∘ MvPolynomial.X
  have hqK : q = MvPolynomial.aeval x := MvPolynomial.aeval_unique q
  have htop : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hqK]
    exact (AlgHom.range_eq_top q).mpr hq
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral (R := K) (Set.finite_range x)
    (fun y ⟨i, hi⟩ => hi ▸ (hint i).tower_top (A := K))
  rw [htop] at hfinite
  have : Module.Finite K E := Module.Finite.of_surjective (⊤ : Subalgebra K E).val.toLinearMap
    (fun y => ⟨⟨y, trivial⟩, rfl⟩)
  let d := Module.finrank K E
  let e : E ≃ₗ[K] (Fin d → K) := (Module.finBasis K E).equivFun
  let V := Algebra.adjoin U (Set.range x)
  have : Module.Finite U V := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x)
    (fun y ⟨i, hi⟩ => hi ▸ hint i)
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := U) (M := V)
  have hg' : Function.Surjective (Fintype.linearCombination U g) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination U g).mp hg
  let C := ∑ j, ‖e (g j : E)‖
  let f := e.toLinearMap.comp q.toLinearMap
  have hunit (p : MvPolynomial (Fin n) K) (hp : ‖strictPolynomialMap K n p‖ ≤ 1) :
      ‖f p‖ ≤ C := by
    have hcoeff (i : Fin n →₀ ℕ) : ‖p.coeff i‖ ≤ 1 := by
      rw [← strictPolynomialMap_coeff p]
      exact (StrictTateAlgebra.norm_le_iff _ _ _ zero_le_one).mp hp i
    obtain ⟨pU, hpU⟩ := (MvPolynomial.mem_range_map_iff_coeffs_subset
      (f := U.subtype) (x := p)).mpr (fun a ha => by
        obtain ⟨i, _, hi⟩ := MvPolynomial.mem_coeffs_iff.mp ha
        exact ⟨⟨a, hi ▸ hcoeff i⟩, rfl⟩)
    have hqU : q p = (MvPolynomial.aeval x : MvPolynomial (Fin n) U →ₐ[U] E) pU := by
      rw [← hpU, hqK, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      rfl
    have hmem : q p ∈ V := by
      rw [hqU, show V = (MvPolynomial.aeval x : MvPolynomial (Fin n) U →ₐ[U] E).range from
        Algebra.adjoin_range_eq_range_aeval U x]
      exact ⟨pU, rfl⟩
    obtain ⟨c, hc⟩ := hg' ⟨q p, hmem⟩
    have he : f p = ∑ j, (c j : K) • e (g j : E) := by
      have h := congrArg (fun y : V => e (y : E)) hc
      rw [Fintype.linearCombination_apply] at h
      change e (V.val (∑ j, c j • g j)) = f p at h
      simp only [map_sum, map_smul] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      change e ((c j : K) • (g j : E)) = _
      exact e.map_smul _ _
    rw [he]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (c j).property)
  have hbound (p : MvPolynomial (Fin n) K) : ‖f p‖ ≤ C * ‖strictPolynomialMap K n p‖ := by
    by_cases hp : p = 0
    · simp [hp]
    have hn : ‖strictPolynomialMap K n p‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (fun h => hp (strictPolynomialMap_injective (h.trans (map_zero _).symm)))
    obtain ⟨i, hi⟩ := StrictTateAlgebra.exists_norm_coeff_eq (strictPolynomialMap K n p)
    let a := p.coeff i
    have ha : ‖a‖ = ‖strictPolynomialMap K n p‖ := by
      simpa only [StrictTateAlgebra.series, strictPolynomialMap_coeff] using hi
    have h := hunit (a⁻¹ • p) (by rw [map_smul, norm_smul, norm_inv, ha, inv_mul_cancel₀ hn])
    rw [map_smul, norm_smul, norm_inv, ha] at h
    calc
      ‖f p‖ = ‖strictPolynomialMap K n p‖ * (‖strictPolynomialMap K n p‖⁻¹ * ‖f p‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      _ ≤ ‖strictPolynomialMap K n p‖ * C := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = C * ‖strictPolynomialMap K n p‖ := mul_comm _ _
  exact ⟨d, e, f.extendOfNorm (strictPolynomialMap K n).toLinearMap,
    LinearMap.extendOfNorm_eq strictPolynomialMap_dense ⟨C, hbound⟩⟩

private theorem isIntegral_strictQuotient_X
    (M : Ideal (StrictTateAlgebra (Fin n) K)) [M.IsMaximal] (a : ℕ) (i : Fin n) :
    IsIntegral (normUnitBallSubring K)
      (Ideal.Quotient.mk ((M.comap (strictPolynomialMap K n).toRingHom) ^ a) (MvPolynomial.X i)) := by
  let P := MvPolynomial (Fin n) K
  let T := StrictTateAlgebra (Fin n) K
  let f := strictPolynomialMap K n
  let I := M.comap f.toRingHom
  let U := normUnitBallSubring K
  have : IsClosed (M : Set T) := isClosed_ideal_of_noetherian_banach (K := K) M
  have : Module.Finite K (T ⧸ M) := finite_strictFieldQuotient M
  have hE : IsField (T ⧸ M) := by
    let _ := Ideal.Quotient.field M
    exact Field.toIsField _
  have hnorm : ‖Ideal.Quotient.mk M (f (MvPolynomial.X i))‖ ≤ 1 :=
    (Ideal.Quotient.norm_mk_le M _).trans_eq (norm_strictPolynomialMap_X i)
  obtain ⟨p, hp, hpzero⟩ := isIntegral_unitBall_of_finite (K := K) hE _ hnorm
  let qM := ((Ideal.Quotient.mkₐ K M).comp f).restrictScalars U
  have hpI : Polynomial.aeval (MvPolynomial.X i : P) p ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem (I := M)).mp
    change qM (Polynomial.aeval (MvPolynomial.X i : P) p) = 0
    rw [← Polynomial.aeval_algHom_apply qM]
    exact hpzero
  let q := (Ideal.Quotient.mkₐ K (I ^ a)).restrictScalars U
  refine ⟨p ^ a, hp.pow a, ?_⟩
  change Polynomial.aeval (q (MvPolynomial.X i : P)) (p ^ a) = 0
  rw [Polynomial.aeval_algHom_apply q, map_pow]
  exact (Ideal.Quotient.eq_zero_iff_mem (I := I ^ a)).mpr (Ideal.pow_mem_pow hpI a)

/-- A polynomial quotient with integral coordinates over the scalar norm unit ball
agrees with the Tate quotient by the extended ideal. -/
private theorem strictQuotientMap_bijective (I : Ideal (MvPolynomial (Fin n) K))
    (hint : ∀ i, IsIntegral (normUnitBallSubring K) (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    Function.Bijective (Ideal.quotientMapₐ (I.map (strictPolynomialMap K n).toRingHom)
      (strictPolynomialMap K n) Ideal.le_comap_map) := by
  let T := StrictTateAlgebra (Fin n) K
  let f := strictPolynomialMap K n
  let J := I.map f.toRingHom
  let q := Ideal.Quotient.mkₐ K I
  let ψ := Ideal.quotientMapₐ J f Ideal.le_comap_map
  obtain ⟨d, e, L, hL⟩ := exists_strictPolynomial_extension q Ideal.Quotient.mk_surjective hint
  have hkill : J ≤ { carrier := {x | ∀ a : T, L (a * x) = 0}
                     zero_mem' := fun a => by rw [mul_zero, map_zero]
                     add_mem' := fun hx hy a => by rw [mul_add, map_add, hx a, hy a, add_zero]
                     smul_mem' := fun b x hx a => by
                       change L (a * (b * x)) = 0
                       rw [← mul_assoc, hx] } := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx a
    refine isClosed_property strictPolynomialMap_dense
      (isClosed_eq (L.continuous.comp (continuous_id.mul continuous_const)) continuous_const)
      (fun p => ?_) a
    change L (strictPolynomialMap K n p * strictPolynomialMap K n x) = 0
    rw [← map_mul, hL, map_mul, show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      mul_zero, map_zero]
  constructor
  · refine (injective_iff_map_eq_zero ψ).mpr fun x hx => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J (f p) = 0 at hx
    have h := hkill (Ideal.Quotient.eq_zero_iff_mem.mp hx) 1
    rw [one_mul, hL] at h
    exact e.injective (h.trans (map_zero e).symm)
  · have : IsClosed (J : Set T) := isClosed_ideal_of_noetherian_banach (K := K) J
    have : Module.Finite K (MvPolynomial (Fin n) K ⧸ I) := Module.Finite.equiv e.symm
    let π := Ideal.Quotient.mk J
    have hπ : Continuous π := AddMonoidHomClass.continuous_of_bound π 1 fun x => by
      simpa only [one_mul] using Ideal.Quotient.norm_mk_le J x
    have hdense : DenseRange ψ :=
      ((Ideal.Quotient.mk_surjective (I := J)).denseRange.comp strictPolynomialMap_dense hπ).of_comp
        (f := ψ) (g := Ideal.Quotient.mk I)
    have hclosed : IsClosed (Set.range ψ) := ψ.toLinearMap.range.closed_of_finiteDimensional
    intro x
    exact (hclosed.closure_eq ▸ hdense x : x ∈ Set.range ψ)

private theorem strictMap_map_comap_eq (M : Ideal (StrictTateAlgebra (Fin n) K)) [M.IsMaximal] :
    (M.comap (strictPolynomialMap K n).toRingHom).map (strictPolynomialMap K n).toRingHom = M := by
  let f := strictPolynomialMap K n
  let I := M.comap f.toRingHom
  let J := I.map f.toRingHom
  have hint (i : Fin n) : IsIntegral (normUnitBallSubring K) (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    let e := Ideal.quotientEquivAlgOfEq K (pow_one I)
    have h : IsIntegral (normUnitBallSubring K)
        (e (Ideal.Quotient.mk (I ^ 1) (MvPolynomial.X i))) :=
      (isIntegral_strictQuotient_X M 1 i).map e
    exact (Ideal.quotientEquivAlgOfEq_mk K (pow_one I) (MvPolynomial.X i)) ▸ h
  refine le_antisymm Ideal.map_comap_le ?_
  intro x hx
  obtain ⟨p, hp⟩ := (strictQuotientMap_bijective I hint).surjective (Ideal.Quotient.mk J x)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  change Ideal.Quotient.mk J (f p) = Ideal.Quotient.mk J x at hp
  have hdiff : f p - x ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, hp, sub_self])
  have hfp : f p ∈ M := by
    simpa only [sub_add_cancel] using M.add_mem (Ideal.map_comap_le hdiff) hx
  have hpJ : f p ∈ J := Ideal.mem_map_of_mem f.toRingHom (show p ∈ I from hfp)
  exact sub_sub_cancel (f p) x ▸ J.sub_mem hpJ hdiff

private theorem strictPolynomialMap_flat : (strictPolynomialMap K n).toRingHom.Flat := by
  let R := MvPolynomial (Fin n) K
  let S := StrictTateAlgebra (Fin n) K
  let f := strictPolynomialMap K n
  let _ : Algebra R S := f.toRingHom.toAlgebra
  change Module.Flat R S
  apply Module.flat_of_isLocalized_maximal S S (fun M => Localization.AtPrime M)
    (fun M => Algebra.linearMap S (Localization.AtPrime M))
  intro M _
  let I := M.comap f.toRingHom
  let L := Localization.AtPrime M
  let N := IsLocalRing.maximalIdeal L
  let C := AdicCompletion N L
  have hmap (a : ℕ) : (I ^ a).map f.toRingHom = M ^ a := by
    rw [Ideal.map_pow, strictMap_map_comap_eq M]
  let q (a : ℕ) : (R ⧸ I ^ a) ≃+* (L ⧸ N ^ a) :=
    (AlgEquiv.ofBijective _ (strictQuotientMap_bijective (I ^ a)
      (isIntegral_strictQuotient_X M a))).toRingEquiv.trans
      ((Ideal.quotientEquivAlgOfEq K (hmap a)).toRingEquiv.trans
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow M L a).toRingEquiv)
  have : Module.Flat R C := by
    apply flat_completion_of_quotient_equiv I N q
    intro a p
    change IsLocalization.AtPrime.equivQuotMaximalIdealPow M L a (Ideal.quotientEquivAlgOfEq K (hmap a)
      (Ideal.Quotient.mk ((I ^ a).map f.toRingHom) (f p))) =
      Ideal.Quotient.mk (N ^ a) (algebraMap S L (f p))
    rw [Ideal.quotientEquivAlgOfEq_mk, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
  have : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat L C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_faithfullyFlat_target R L C

end Strict

section Weighted

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {n : ℕ} (r : PositivePolyradius (Fin n)) (c : Fin n → K) (hc : ∀ i, ‖c i‖ = r i)

private def weightedToStrict : GeneralizedTateAlgebra r K ≃ₐ[K] StrictTateAlgebra (Fin n) K := by
  let b := baseChange r (RingHom.id K) hc (fun _ => rfl)
  let d := descend r hc (AddMonoidHom.id K) (D := 1) (fun x => by simp)
  let bₐ : GeneralizedTateAlgebra r K →ₐ[K] StrictTateAlgebra (Fin n) K :=
    ⟨b, fun x => by
      apply Subtype.ext
      change MvPowerSeries.rescale c (MvPowerSeries.map (RingHom.id K) (MvPowerSeries.C x)) =
        MvPowerSeries.C x
      rw [MvPowerSeries.map_id, RingHom.id_apply, ← MvPowerSeries.rescaleAlgHom_apply]
      exact (MvPowerSeries.rescaleAlgHom c).commutes x⟩
  have hleft : Function.LeftInverse d b :=
    descend_baseChange r (RingHom.id K) hc (fun _ => rfl) (AddMonoidHom.id K)
      (fun _ => by simp) (fun _ _ => rfl) rfl
  have hright : Function.RightInverse d b := by
    intro g
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro a
    change MvPowerSeries.coeff a (StrictTateAlgebra.series (Fin n) K (b (d g))) = _
    rw [coeff_baseChange, coeff_descend]
    simp only [RingHom.id_apply, AddMonoidHom.id_apply, ← mul_assoc,
      mul_inv_cancel₀ (scale_ne_zero hc a), one_mul]
    rfl
  exact AlgEquiv.ofBijective bₐ ⟨hleft.injective, hright.surjective⟩

include hc in
private theorem weightedPolynomialMap_flat :
    (GeneralizedTateAlgebra.polynomialMap r K).toRingHom.Flat := by
  let R := MvPolynomial (Fin n) K
  let rescale (s : Fin n → K) : R →ₐ[K] R :=
    MvPolynomial.aeval fun i => MvPolynomial.C (s i) * MvPolynomial.X i
  have rescale_X (s : Fin n → K) (i : Fin n) :
      rescale s (MvPolynomial.X i) = MvPolynomial.C (s i) * MvPolynomial.X i :=
    MvPolynomial.aeval_X _ _
  have rescale_C (s : Fin n → K) (x : K) : rescale s (MvPolynomial.C x) = MvPolynomial.C x :=
    (rescale s).commutes x
  have rescale_comp (s t : Fin n → K) (hst : ∀ i, t i * s i = 1) :
      (rescale s).comp (rescale t) = AlgHom.id K R := by
    ext i : 1
    change rescale s (rescale t (MvPolynomial.X i)) = MvPolynomial.X i
    rw [rescale_X, map_mul, rescale_C, rescale_X, ← mul_assoc, ← map_mul, hst, map_one,
      one_mul]
  have hc0 (i : Fin n) : c i ≠ 0 := by
    rw [← norm_ne_zero_iff, hc i]
    exact (r.positive i).ne'
  let ρ : R ≃ₐ[K] R := AlgEquiv.ofAlgHom (rescale c) (rescale fun i => (c i)⁻¹)
    (rescale_comp _ _ fun i => inv_mul_cancel₀ (hc0 i))
    (rescale_comp _ _ fun i => mul_inv_cancel₀ (hc0 i))
  let b := weightedToStrict r c hc
  have hfactor : b.toAlgHom.comp (GeneralizedTateAlgebra.polynomialMap r K) =
      (strictPolynomialMap K n).comp ρ.toAlgHom := by
    ext i : 1
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro a
    change MvPowerSeries.coeff a (StrictTateAlgebra.series (Fin n) K
      (baseChange r (RingHom.id K) hc (fun _ => rfl)
        (GeneralizedTateAlgebra.polynomialMap r K (MvPolynomial.X i)))) =
      MvPowerSeries.coeff a (strictPolynomialMap K n (rescale c (MvPolynomial.X i))).val
    rw [coeff_baseChange, coeff_polynomialMap, strictPolynomialMap_coeff, RingHom.id_apply]
    rw [rescale_X, MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_X]
    split_ifs with h
    · subst a
      simp [GeneralizedTateAlgebra.scale, Finsupp.prod_single_index]
    · rw [mul_zero]
  have hfactorRing : b.toRingEquiv.toRingHom.comp (GeneralizedTateAlgebra.polynomialMap r K).toRingHom =
      (strictPolynomialMap K n).toRingHom.comp ρ.toRingEquiv.toRingHom :=
    congrArg AlgHom.toRingHom hfactor
  have hf : ((strictPolynomialMap K n).toRingHom.comp ρ.toRingEquiv.toRingHom).Flat :=
    (RingHom.Flat.of_bijective ρ.bijective).comp strictPolynomialMap_flat
  rw [← hfactorRing] at hf
  exact (RingHom.Flat.comp_iff_of_bijective_left b.bijective).mp hf

end Weighted

open scoped TensorProduct

/-- The map from a finitely presented algebra to each of its analytic chart algebras is flat. -/
theorem affineAnalytificationChart_flat : AffineAnalytificationChartFlatStatement.{u,v} := by
  intro K _ _ _ A _ _ P m
  let r := AnalyticAffineSpace.polyradius K P.arity m
  let c : Fin P.arity → K := fun _ => (AnalyticAffineSpace.scale K)⁻¹ ^ m
  have hc (i : Fin P.arity) : ‖c i‖ = r i := by
    change ‖(AnalyticAffineSpace.scale K)⁻¹ ^ m‖ = ‖AnalyticAffineSpace.scale K‖⁻¹ ^ m
    rw [norm_pow, norm_inv]
  let R := MvPolynomial (Fin P.arity) K
  let T := GeneralizedTateAlgebra r K
  let f : R →+* T := (GeneralizedTateAlgebra.polynomialMap r K).toRingHom
  let I : Ideal R := RingHom.ker P.map.toRingHom
  let J : Ideal T := I.map f
  let Jclosed : Ideal T := (PolynomialLocus.chart P r).ideal
  let _ : J.IsTwoSided := inferInstance
  let _ : Jclosed.IsTwoSided := inferInstance
  let _ : Algebra R T := f.toAlgebra
  have : Module.Flat R T := weightedPolynomialMap_flat r c hc
  have : IsNoetherianRing T :=
    isNoetherianRing_of_ringEquiv _ (weightedToStrict r c hc).symm.toRingEquiv
  have hJ : Jclosed = J := by
    change (Ideal.span (f '' (I : Set R))).closure = J
    rw [← Ideal.map_span, Ideal.span_eq]
    exact J.closure_eq_of_isClosed (isClosed_ideal_of_noetherian_banach (K := K) J)
  let eA : (R ⧸ I) ≃+* A := P.map.toRingHom.quotientKerEquivOfSurjective P.surjective
  let eChart : PolynomialLocus.chart P r ≃+* (R ⧸ I) ⊗[R] T :=
    (Ideal.quotientEquivAlgOfEq (A := T) K hJ).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I).toRingEquiv
  let g := (PolynomialLocus.algebraMap P r).toRingHom
  let baseMap : (R ⧸ I) →+* ((R ⧸ I) ⊗[R] T) := algebraMap _ _
  have hcompare : eChart.toRingHom.comp (g.comp eA.toRingHom) = baseMap := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    change eChart (PolynomialLocus.algebraMap P r (P.map p)) =
      Ideal.Quotient.mk I p ⊗ₜ[R] (1 : T)
    rw [PolynomialLocus.algebraMap_map]
    change Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I
      (Ideal.quotientEquivAlgOfEq (A := T) K hJ (Ideal.Quotient.mk Jclosed (f p))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    change (1 : R ⧸ I) ⊗ₜ[R] f p = _
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := R ⧸ I) (B := T) p).symm
  have hbase : RingHom.Flat (R := R ⧸ I) (S := (R ⧸ I) ⊗[R] T) baseMap := by
    dsimp only [baseMap]
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.baseChange R (R ⧸ I) T
  rw [← hcompare] at hbase
  exact (RingHom.Flat.comp_iff_of_bijective_right eA.bijective).mp
    ((RingHom.Flat.comp_iff_of_bijective_left eChart.bijective).mp hbase)

end Langlands.Analytic.AffineAnalytification
