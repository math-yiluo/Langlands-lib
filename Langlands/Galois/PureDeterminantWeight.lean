import Langlands.Galois.CoefficientIdentification
import Langlands.Galois.PureCyclotomicComparison
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Topology.Instances.Matrix

/-! # Determinant products and equality of pure weights -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Langlands.Global Polynomial Cohomology.Weights Filter
open scoped Valued

universe uK uL uM uE uV uW

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [TopologicalSpace L]

/-- The determinant of the actual Galois action as a multiplicative character. -/
def determinantCharacter (A : Objects.{uK, uL, uV} K L) : Field.absoluteGaloisGroup K →* L :=
  LinearMap.det.comp A.val.representation

theorem determinantCharacter_apply (A : Objects.{uK, uL, uV} K L)
    (g : Field.absoluteGaloisGroup K) :
    determinantCharacter A g = LinearMap.det (A.val.representation g) := rfl

theorem continuous_determinantCharacter [IsTopologicalRing L]
    (A : Objects.{uK, uL, uV} K L) : Continuous (determinantCharacter A) := by
  let b := Module.finBasis L A.val
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L (Module.End L A.val)
  have h : Continuous (fun g => LinearMap.toMatrix b b (A.val.representation g)) :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.toMatrix b b).toLinearMap).comp A.property
  change Continuous (fun g => LinearMap.det (A.val.representation g))
  simpa only [LinearMap.det_toMatrix] using h.matrix_det

theorem determinantCharacter_eq_of_equiv
    {A : Objects.{uK, uL, uV} K L} {B : Objects.{uK, uL, uW} K L}
    (e : FiniteRepresentation.Equiv A.val B.val) (g : Field.absoluteGaloisGroup K) :
    determinantCharacter A g = determinantCharacter B g := by
  rw [determinantCharacter_apply, determinantCharacter_apply,
    ← Representation.Equiv.conj_apply_self g e]
  exact (LinearMap.det_conj (A.val.representation g) e.toLinearEquiv).symm

theorem map_determinantCharacter_eq_prod_roots (A : Objects.{uK, uL, uV} K L)
    (i : L →+* ℂ) (g : Field.absoluteGaloisGroup K) :
    i (determinantCharacter A g) = ((characteristicPolynomial A g).map i).roots.prod := by
  let b := Module.finBasis L A.val
  rw [determinantCharacter_apply, ← LinearMap.det_toMatrix b, RingHom.map_det,
    characteristicPolynomial, ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_map]
  exact Matrix.det_eq_prod_roots_charpoly _

private theorem norm_multiset_prod_eq_pow (s : Multiset ℂ) (r : ℝ)
    (h : ∀ z ∈ s, ‖z‖ = r) :
    ‖s.prod‖ = r ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    rw [Multiset.prod_cons, norm_mul, h _ (Multiset.mem_cons_self _ _),
      ih (fun a ha => h a (Multiset.mem_cons_of_mem ha)), Multiset.card_cons, pow_succ']

private theorem prod_roots_mul_conj_eq_weight {q : ℕ} {m : ℤ}
    (P : ℂ[X]) (hP : HasComplexRootsOfWeight q m P) :
    P.roots.prod * Complex.conjAe.toRingEquiv P.roots.prod = (q : ℂ) ^ ((P.natDegree : ℤ) * m) := by
  have hn : ‖P.roots.prod‖ = radius q m ^ P.natDegree := by
    rw [← IsAlgClosed.card_roots_eq_natDegree]
    exact norm_multiset_prod_eq_pow _ _ hP
  have hr : radius q m ^ 2 = (q : ℝ) ^ m := by
    rw [← Real.rpow_natCast, radius, ← Real.rpow_mul (Nat.cast_nonneg q)]
    rw [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num), Real.rpow_intCast]
  have hreal : ‖P.roots.prod‖ ^ 2 = (q : ℝ) ^ ((P.natDegree : ℤ) * m) := by
    rw [hn, ← pow_mul, mul_comm P.natDegree 2, pow_mul, hr,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [mul_comm]
  change (starRingEnd ℂ) P.roots.prod * P.roots.prod = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    hreal, Complex.ofReal_zpow, Complex.ofReal_natCast]

private theorem monoidHom_conj_eq {G D : Type*} [Group G] [CommMonoid D]
    (f : G →* D) (t g : G) : f (t * g * t⁻¹) = f g := by
  rw [map_mul, map_mul, mul_comm (f t) (f g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

section Families

variable [NumberField K]
variable {F : Type uL} [Field F] [NumberField F]
variable {excluded : Finset (FinitePlace F)}
variable {R : Collection.{uK, uL, uV} K F excluded}

private theorem mapped_charpoly_eq_of_euler_match
    {lam : FinitePlace F} {A : LambdaAdic.{uK, uL, uV} K F lam}
    {v : FinitePlace K} {P : F[X]}
    (hP : HasEulerPolynomialAt A v (P.map (NumberField.FinitePlace.embedding lam)))
    (i : FiniteCompletion F lam →+* ℂ) (ι : F →+* ℂ)
    (hι : ∀ x : F, i (NumberField.FinitePlace.embedding lam x) = ι x) :
    (characteristicPolynomial A (globalGeometricFrobenius v)).map i = P.reverse.map ι := by
  let j : F →+* FiniteCompletion F lam := NumberField.FinitePlace.embedding lam
  have he : eulerPolynomial A (globalGeometricFrobenius v) = P.map j :=
    (hasEulerPolynomialAt_iff.mp hP).2
  have hrev : (P.map j).reverse = P.reverse.map j := by
    rw [Polynomial.reverse, Polynomial.reverse, natDegree_map_eq_of_injective j.injective, reflect_map]
  rw [← reverse_eulerPolynomial, he, hrev, Polynomial.map_map,
    show i.comp j = ι from RingHom.ext hι]

/-- Two embeddings inducing mutually conjugate complex coefficient embeddings
    give determinant characters whose product is the integral cyclotomic
    character prescribed by the rank and weight. -/
theorem determinantProduct_eq_geometricCyclotomicPower
    (p : ℕ) [Fact p.Prime] (ι : F →+* ℂ) {m : ℤ} {d : ℕ}
    (hR : IsPureCompatible excluded R m) (hRank : HasRank excluded R d)
    (lam mu : {lam : FinitePlace F // lam ∉ excluded})
    (hLam : residueCharacteristic lam.val = p) (hMu : residueCharacteristic mu.val = p)
    (e : PadicAlgCl p ≃+* ℂ)
    (j : FiniteCompletion F lam.val →+* PadicAlgCl p)
    (k : FiniteCompletion F mu.val →+* PadicAlgCl p)
    (hj : Continuous j) (hk : Continuous k)
    (hι : ∀ x : F, e (j (NumberField.FinitePlace.embedding lam.val x)) = ι x)
    (hκ : ∀ x : F, e (k (NumberField.FinitePlace.embedding mu.val x)) =
      Complex.conjAe.toRingEquiv (ι x)) :
    (fun g => j (determinantCharacter (R lam) g) * k (determinantCharacter (R mu) g)) =
      fun g => (geometricCyclotomicPower K p (algebraMap ℚ_[p] (PadicAlgCl p))
        ((d : ℤ) * m) g : PadicAlgCl p) := by
  obtain ⟨S, P, hP, hpure⟩ := hR
  have hgood : ∀ᶠ w : FinitePlace K in cofinite, w ∉ S ∧ residueCharacteristic w ≠ p := by
    filter_upwards [S.eventually_cofinite_notMem,
      eventually_residueCharacteristic_not_dvd (K := K) p (Fact.out : p.Prime).ne_zero]
      with w hw hd
    exact ⟨hw, fun h => hd (h ▸ dvd_rfl)⟩
  classical
  let T := (Filter.eventually_cofinite.mp hgood).toFinset
  let c := geometricCyclotomicPower K p (algebraMap ℚ_[p] (PadicAlgCl p)) ((d : ℤ) * m)
  refine eq_of_continuous_of_globalGeometricFrobenius_eq T
    ((hj.comp (continuous_determinantCharacter (R lam))).mul
      (hk.comp (continuous_determinantCharacter (R mu))))
    (continuous_geometricCyclotomicPower K p _ (continuous_algebraMap ℚ_[p] (PadicAlgCl p)) _)
    ?_ (fun t g => congrArg Units.val (monoidHom_conj_eq c t g)) ?_
  · intro t g
    rw [monoidHom_conj_eq (determinantCharacter (R lam)),
      monoidHom_conj_eq (determinantCharacter (R mu))]
  intro w hw _
  have hW : w ∉ S ∧ residueCharacteristic w ≠ p := by
    by_contra h
    exact hw ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr h)
  let a := e.toRingHom.comp j
  let b := e.toRingHom.comp k
  let conj := Complex.conjAe.toRingEquiv.toRingHom
  have ha := mapped_charpoly_eq_of_euler_match
    (hP lam w hW.1 (by simpa only [hLam] using hW.2)) a ι hι
  have hb := mapped_charpoly_eq_of_euler_match
    (hP mu w hW.1 (by simpa only [hMu] using hW.2)) b (conj.comp ι) hκ
  have hd : ((P w).reverse.map ι).natDegree = d := by
    rw [← ha, natDegree_map_eq_of_injective a.injective, characteristicPolynomial_natDegree,
      hRank lam]
  apply e.injective
  rw [map_mul]
  change a (determinantCharacter (R lam) (globalGeometricFrobenius w)) *
    b (determinantCharacter (R mu) (globalGeometricFrobenius w)) = e (c _)
  rw [map_determinantCharacter_eq_prod_roots, map_determinantCharacter_eq_prod_roots, ha, hb,
    ← Polynomial.map_map, (IsAlgClosed.splits _).roots_map_of_injective conj.injective,
    ← map_multiset_prod]
  refine (prod_roots_mul_conj_eq_weight _ ((hpure w hW.1).hasComplexRootsOfWeight ι)).trans ?_
  have hc : (c (globalGeometricFrobenius w) : PadicAlgCl p) =
      (residueCardinality w : PadicAlgCl p) ^ ((d : ℤ) * m) :=
    geometricCyclotomicPower_frobenius p _ hW.2 (geometricFrobeniusLift_spec w) _
  rw [hd, hc, map_zpow₀, map_natCast]

end Families

section Comparison

variable [NumberField K]

/-- Equivalence of the local restrictions over a common coefficient field
    gives equality of their mapped determinants on a geometric lift. -/
theorem mapped_determinantCharacter_eq_of_local_extendCoefficients_equiv
    {M : Type uM} [Field M] [TopologicalSpace M] {E : Type uE} [Field E]
    (A : Objects.{uK, uL, uV} K L) (B : Objects.{uK, uM, uW} K M)
    (i : L →+* E) (j : M →+* E) (v : FinitePlace K)
    (h : letI : Algebra L E := i.toAlgebra
      letI : Algebra M E := j.toAlgebra
      Nonempty (FiniteRepresentation.Equiv
        ((atFinitePlace v A).val.extendCoefficients E)
        ((atFinitePlace v B).val.extendCoefficients E))) :
    i (determinantCharacter A (globalGeometricFrobenius v)) =
      j (determinantCharacter B (globalGeometricFrobenius v)) := by
  let : Algebra L E := i.toAlgebra
  let : Algebra M E := j.toAlgebra
  obtain ⟨e⟩ := h
  let g := geometricFrobeniusLift v
  let a := ((atFinitePlace v A).val.extendCoefficients E).representation
  let b := ((atFinitePlace v B).val.extendCoefficients E).representation
  calc
    i (determinantCharacter A (globalGeometricFrobenius v)) = LinearMap.det (a g) :=
      (LinearMap.det_baseChange (A := E) ((atFinitePlace v A).val.representation g)).symm
    _ = LinearMap.det (b g) := by
      have hb : b g = e.toLinearEquiv.conj (a g) := (Representation.Equiv.conj_apply_self g e).symm
      rw [hb]
      exact (LinearMap.det_conj (a g) e.toLinearEquiv).symm
    _ = j (determinantCharacter B (globalGeometricFrobenius v)) :=
      LinearMap.det_baseChange (A := E) ((atFinitePlace v B).val.representation g)

variable {F : Type uL} [Field F] [NumberField F]
variable {M : Type uM} [Field M] [NumberField M]
variable {R : Collection.{uK, uL, uV} K F ∅}
variable {U : Collection.{uK, uM, uW} K M ∅}

/-- Positive-rank pure families have the same weight when their actual
    determinants agree at a local geometric lift after every compatible
    coefficient identification at one prime away from the place. -/
theorem pureWeights_eq_of_localDeterminants_eq
    (p : ℕ) [Fact p.Prime] (v : FinitePlace K) (hchar : residueCharacteristic v ≠ p)
    (ι : F →+* ℂ) (κ : M →+* ℂ) {m n : ℤ} {d : ℕ} (hd : 0 < d)
    (hR : IsPureCompatible ∅ R m) (hU : IsPureCompatible ∅ U n)
    (hr : HasRank ∅ R d) (hu : HasRank ∅ U d)
    (heq : ∀ (e : PadicAlgCl p ≃+* ℂ) (lam : FinitePlace F) (mu : FinitePlace M)
        (j : FiniteCompletion F lam →+* PadicAlgCl p)
        (k : FiniteCompletion M mu →+* PadicAlgCl p), Continuous j → Continuous k →
      (∀ x : F, e (j (NumberField.FinitePlace.embedding lam x)) = ι x) →
      (∀ x : M, e (k (NumberField.FinitePlace.embedding mu x)) = κ x) →
      j (determinantCharacter (R ⟨lam, by simp⟩) (globalGeometricFrobenius v)) =
        k (determinantCharacter (U ⟨mu, by simp⟩) (globalGeometricFrobenius v))) :
    m = n := by
  let e := padicAlgClComplexEquiv p
  let conj := Complex.conjAe.toRingEquiv
  let e' := e.trans conj
  obtain ⟨lam, j, hLam, hj, hι⟩ := exists_compatibleCoefficientCompletionEmbedding p e ι
  obtain ⟨mu, k, hMu, hk, hκ⟩ := exists_compatibleCoefficientCompletionEmbedding p e κ
  obtain ⟨lam', j', hLam', hj', hι'⟩ := exists_compatibleCoefficientCompletionEmbedding p e' ι
  obtain ⟨mu', k', hMu', hk', hκ'⟩ := exists_compatibleCoefficientCompletionEmbedding p e' κ
  have hιc (x : F) : e (j' (NumberField.FinitePlace.embedding lam' x)) = conj (ι x) := by
    have h := congrArg conj (hι' x)
    change star (star (e (j' (NumberField.FinitePlace.embedding lam' x)))) = star (ι x) at h
    change _ = star (ι x)
    simpa only [star_star] using h
  have hκc (x : M) : e (k' (NumberField.FinitePlace.embedding mu' x)) = conj (κ x) := by
    have h := congrArg conj (hκ' x)
    change star (star (e (k' (NumberField.FinitePlace.embedding mu' x)))) = star (κ x) at h
    change _ = star (κ x)
    simpa only [star_star] using h
  have hprodR := congrFun (determinantProduct_eq_geometricCyclotomicPower p ι hR hr
    ⟨lam, by simp⟩ ⟨lam', by simp⟩ hLam hLam' e j j' hj hj' hι hιc) (globalGeometricFrobenius v)
  have hprodU := congrFun (determinantProduct_eq_geometricCyclotomicPower p κ hU hu
    ⟨mu, by simp⟩ ⟨mu', by simp⟩ hMu hMu' e k k' hk hk' hκ hκc) (globalGeometricFrobenius v)
  have h := hprodR.symm.trans
    ((congrArg₂ (· * ·) (heq e lam mu j k hj hk hι hκ)
      (heq e' lam' mu' j' k' hj' hk' hι' hκ')).trans hprodU)
  have hfrob (z : ℤ) : (geometricCyclotomicPower K p (algebraMap ℚ_[p] (PadicAlgCl p))
      z (globalGeometricFrobenius v) : PadicAlgCl p) = (residueCardinality v : PadicAlgCl p) ^ z :=
    geometricCyclotomicPower_frobenius p _ hchar (geometricFrobeniusLift_spec v) z
  rw [hfrob, hfrob] at h
  have hc := congrArg e h
  simp only [map_zpow₀, map_natCast] at hc
  have hre : (residueCardinality v : ℝ) ^ ((d : ℤ) * m) =
      (residueCardinality v : ℝ) ^ ((d : ℤ) * n) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using hc
  have hq : 1 < (residueCardinality v : ℝ) :=
    Nat.one_lt_cast.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hd.ne')
    (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' hre)

end Comparison
end Langlands.GaloisRepresentation
