import Langlands.Global.AdelicEisensteinCuspidalTestSystemStatement
import Langlands.Global.AdelicEisensteinStandardizationStatement
import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionStatement
import Langlands.Global.AdelicEisensteinRegularUniquenessStatement
import Langlands.Global.AdelicParameterTwistAutomorphyStatement
import Langlands.Global.AdelicLeviCuspFormMajorantStatement
import Langlands.Global.AdelicExponentLocalization
import Langlands.Global.AdelicCuspidalTestAlgebra
import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Global.AdelicEisensteinInducingPairingContinuation
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.Global.AdelicLeviPairingExpansion

/-! # The cuspidal test system from its premises

A conditional proof of `EisensteinCuspidalTestSystemStatement` (Bernstein–Lapid §8.4). The
system consists of the common-point forms of the non-homogeneous cuspidal equations (8.2b) and of
the homogeneous equations (8.3), both written with the unnormalized left translation by one point
`b` of the positive split component and with unnormalized labels. Corollary 6.10 enters through
the uniform expansion premise, to show that the regular Eisenstein series is a solution; the
uniqueness uses the competing-exponent support of (6.21) and (6.22). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Polynomial

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-! ### Lifting positive split-component points to smaller standard parabolics -/

/-- A point of `𝔄_Q` with the same image in `G(𝔸)` as a given point of `𝔄_J`, `Q ≤ J`. -/
def splitComponentLift {Q J : StandardIndex F G 𝓕.i 𝓕.ν} (hQJ : Q ≤ J)
    (b : 𝓕.positiveSplitComponent J) : 𝓕.positiveSplitComponent Q :=
  Classical.choose (𝓕.exists_positiveSplitComponent_lift_with_values hQJ b)

theorem map_splitComponentLift {Q J : StandardIndex F G 𝓕.i 𝓕.ν} (hQJ : Q ≤ J)
    (b : 𝓕.positiveSplitComponent J) :
    map F (𝓕.P Q) G (𝓕.p Q) (𝓕.splitComponentLift hQJ b).val =
      map F (𝓕.P J) G (𝓕.p J) b.val :=
  (Classical.choose_spec (𝓕.exists_positiveSplitComponent_lift_with_values hQJ b)).1

/-! ### The translation polynomials of the system -/

variable {I : StandardIndex F G 𝓕.i 𝓕.ν}

open Classical in
/-- The roots of the cuspidal polynomials along `Q`: competing labels (left summand) and
identity labels, shifted by the restriction of the parameter (right summand). -/
def cuspidalTestRoot (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) :
    Fin data.size ⊕ (Σ _ : Fin m, ComplexCharacterParameter F (𝓕.P Q)) → ℂ
  | Sum.inl k => parameterPower F (𝓕.P Q) (data.label k lam) b.val
  | Sum.inr x => parameterPower F (𝓕.P Q)
      (x.2 + if h : Q ≤ I then parameterRestrict (𝓕.nestedParabolicHom h) lam else 0) b.val

/-- The multiplicities of the roots. -/
def cuspidalTestMultiplicity (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ) :
    Fin data.size ⊕ (Σ _ : Fin m, ComplexCharacterParameter F (𝓕.P Q)) → ℕ
  | Sum.inl _ => nexp
  | Sum.inr x => deg x.1 x.2

/-- The labels of the cuspidal polynomial along `Q`. The identity labels occur only for
`Q ≤ I`. -/
def cuspidalTestLabels (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q))) :
    Finset (Fin data.size ⊕ (Σ _ : Fin m, ComplexCharacterParameter F (𝓕.P Q))) :=
  open Classical in
  Finset.univ.disjSum (if Q ≤ I then Finset.univ.sigma ids else ∅)

/-- The polynomial of the homogeneous equations along `Q`, for one point `b ∈ 𝔄_Q`: the
competing factors and, for `Q ≤ I`, the identity factors, each `X - b^ν` for an unnormalized
label `ν`. Evaluated at the unnormalized left translation by `b`, it is a nonzero scalar
multiple of the common-point form of the operator of Bernstein–Lapid (8.3). -/
def cuspidalTestPolynomial (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) : ℂ[X] :=
  ∏ x ∈ 𝓕.cuspidalTestLabels Q data ids,
    (X - C (𝓕.cuspidalTestRoot Q data lam b x)) ^ (𝓕.cuspidalTestMultiplicity Q data nexp deg x + 1)

/-- The polynomial of the non-homogeneous equations along `J`, for one point `b ∈ 𝔄_J`: the
factors `X - b^ν` of the competing unnormalized labels `ν` only. Evaluated at the unnormalized
left translation by `b`, it is a nonzero scalar multiple of the common-point form of the
operator of Bernstein–Lapid (8.2b). -/
def competingTestPolynomial (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent J) : ℂ[X] :=
  ∏ k ∈ (Finset.univ : Finset (Fin data.size)),
    (X - C (parameterPower F (𝓕.P J) (data.label k lam) b.val)) ^ (nexp + 1)

theorem cuspidalTestPolynomial_monic (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) :
    (𝓕.cuspidalTestPolynomial Q data nexp ids deg lam b).Monic :=
  monic_prod_X_sub_C_pow _ _ _

theorem cuspidalTestPolynomial_natDegree (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) :
    (𝓕.cuspidalTestPolynomial Q data nexp ids deg lam b).natDegree =
      ∑ x ∈ 𝓕.cuspidalTestLabels Q data ids,
        (𝓕.cuspidalTestMultiplicity Q data nexp deg x + 1) :=
  natDegree_prod_X_sub_C_pow _ _ _

theorem cuspidalTestRoot_ne_zero (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q)
    (x : Fin data.size ⊕ (Σ _ : Fin m, ComplexCharacterParameter F (𝓕.P Q))) :
    𝓕.cuspidalTestRoot Q data lam b x ≠ 0 := by
  cases x <;> exact Complex.exp_ne_zero _

theorem cuspidalTestPolynomial_coeff_zero_ne_zero (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) :
    (𝓕.cuspidalTestPolynomial Q data nexp ids deg lam b).coeff 0 ≠ 0 :=
  coeff_zero_prod_X_sub_C_pow_ne_zero _ _ _ fun x _ => 𝓕.cuspidalTestRoot_ne_zero Q data lam b x

theorem cuspidalTestPolynomial_entire (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (𝓕.P I))
    (b : 𝓕.positiveSplitComponent Q) :
    IsEntirePolynomialFamily fun s => 𝓕.cuspidalTestPolynomial Q data nexp ids deg (L s) b := by
  refine IsEntirePolynomialFamily.prod _ fun x _ => ?_
  refine (IsEntirePolynomialFamily.X_sub_C ?_).pow _
  cases x with
  | inl k =>
    change Differentiable ℂ fun s =>
      parameterPower F (𝓕.P Q) ((data.linear k).comp L s + data.offset k) b.val
    exact differentiable_parameterPower_affine _ _ _
  | inr x =>
    simp only [cuspidalTestRoot]
    split_ifs with h
    · have := differentiable_parameterPower_affine
        ((parameterRestrict (𝓕.nestedParabolicHom h)).comp L) x.2 b.val
      simpa only [LinearMap.comp_apply, add_comm] using this
    · exact differentiable_const _

theorem competingTestPolynomial_dvd (Q : StandardIndex F G 𝓕.i 𝓕.ν) {m : ℕ}
    (data : CompetingWeylExponents 𝓕 I Q 1) (nexp : ℕ)
    (ids : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent Q) :
    𝓕.competingTestPolynomial Q data nexp lam b ∣
      𝓕.cuspidalTestPolynomial Q data nexp ids deg lam b := by
  unfold cuspidalTestPolynomial cuspidalTestLabels
  rw [Finset.prod_disjSum]
  exact dvd_mul_right _ _

theorem competingTestPolynomial_monic (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent J) :
    (𝓕.competingTestPolynomial J data nexp lam b).Monic :=
  monic_prod_X_sub_C_pow _ _ _

theorem competingTestPolynomial_natDegree (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent J) :
    (𝓕.competingTestPolynomial J data nexp lam b).natDegree = data.size * (nexp + 1) := by
  unfold competingTestPolynomial
  have h := natDegree_prod_X_sub_C_pow (Finset.univ : Finset (Fin data.size))
    (fun k => parameterPower F (𝓕.P J) (data.label k lam) b.val) (fun _ => nexp)
  simpa using h

theorem competingTestPolynomial_entire (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (𝓕.P I))
    (b : 𝓕.positiveSplitComponent J) :
    IsEntirePolynomialFamily fun s => 𝓕.competingTestPolynomial J data nexp (L s) b := by
  refine IsEntirePolynomialFamily.prod _ fun k _ => ?_
  refine (IsEntirePolynomialFamily.X_sub_C ?_).pow _
  change Differentiable ℂ fun s =>
    parameterPower F (𝓕.P J) ((data.linear k).comp L s + data.offset k) b.val
  exact differentiable_parameterPower_affine _ _ _

theorem exists_eq_of_competingTestPolynomial_eval_eq_zero (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) (b : 𝓕.positiveSplitComponent J) {z : ℂ}
    (hz : (𝓕.competingTestPolynomial J data nexp lam b).eval z = 0) :
    ∃ k ∈ (Finset.univ : Finset (Fin data.size)),
      z = parameterPower F (𝓕.P J) (data.label k lam) b.val :=
  exists_eq_of_eval_prod_pow_eq_zero _ _ (fun _ => nexp) hz

/-! ### Difference equations in cusp tests -/

/-- A polynomial in the translation by `b ∈ 𝔄_Q` applied to `f` lies in the cuspidal
annihilator along `Q` as soon as `f` has absolutely convergent cusp-test pairings and the
corresponding combinations of the translated pairings vanish. -/
theorem translate_mem_cuspidalAnnihilator (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (b : 𝓕.positiveSplitComponent Q) (D : ℂ[X]) {f : AdelicGroupPoints F G → ℂ}
    (hdom : ∀ test, 𝓕.IsLeviCuspForm Kinf rho Q test → f ∈ 𝓕.leviPairingDomain Q test)
    (hzero : ∀ test, 𝓕.IsLeviCuspForm Kinf rho Q test → ∀ g,
      ∑ k ∈ Finset.range (D.natDegree + 1),
        D.coeff k * 𝓕.leviPairing Q f (map F (𝓕.P Q) G (𝓕.p Q) b.val ^ k * g) test = 0) :
    (fun g => ∑ k ∈ Finset.range (D.natDegree + 1),
        D.coeff k * f (map F (𝓕.P Q) G (𝓕.p Q) b.val ^ k * g)) ∈
      𝓕.cuspidalAnnihilator Kinf rho Q := by
  have hfun : (fun g => ∑ k ∈ Finset.range (D.natDegree + 1),
      D.coeff k * f (map F (𝓕.P Q) G (𝓕.p Q) b.val ^ k * g)) =
      Polynomial.aeval (𝓕.splitComponentRepresentation Q b) D f :=
    funext fun g => (𝓕.aeval_splitComponentRepresentation_apply Q b D f g).symm
  rw [hfun]
  intro test ht g
  refine ⟨𝓕.aeval_mem_leviPairingDomain Q test b D (hdom test ht) g, ?_⟩
  rw [𝓕.leviPairing_aeval_splitComponent Q test b D (hdom test ht) g,
    𝓕.aeval_splitComponentRepresentation_apply]
  exact hzero test ht g

/-- Pairing functions of terms with a polynomial orbit of degree `n` are killed by every
multiple of the corresponding power of a linear factor. -/
theorem isTranslationPolynomialSolution_leviPairing_of_polynomialOrbit
    (Q : StandardIndex F G 𝓕.i 𝓕.ν) (test : AdelicGroupPoints F (𝓕.M Q) → ℂ)
    (b : 𝓕.positiveSplitComponent Q) {mu : ComplexCharacterParameter F (𝓕.P Q)} {n : ℕ}
    {f : AdelicGroupPoints F G → ℂ} (hf : 𝓕.HasPolynomialOrbit Q mu n f)
    (hdom : f ∈ 𝓕.leviPairingDomain Q test) {D : ℂ[X]}
    (hD : (X - C (parameterPower F (𝓕.P Q) mu b.val)) ^ (n + 1) ∣ D) :
    IsTranslationPolynomialSolution (map F (𝓕.P Q) G (𝓕.p Q) b.val) D
      (fun g => 𝓕.leviPairing Q f g test) :=
  𝓕.isTranslationPolynomialSolution_leviPairing Q test b D hdom
    ((𝓕.isTranslationPolynomialSolution_pow_of_polynomialOrbit Q hf b).of_dvd hD)

/-! ### From the non-homogeneous equations to the support of the cuspidal exponents -/

/-- The passage from the common-point non-homogeneous equations (8.2b) to the
competing-exponent support of (6.21), the hypothesis of (6.22), along one standard `J`. Let `w` be
automorphic on `G(F) \ G(𝔸)` and `Φ` automorphic on `U_I(𝔸) M_I(F) \ G(𝔸)` (needed only for
`J ≤ I`). If the competing difference polynomial, applied to the tested difference
`C_J w - C_{I,J} Φ`, gives zero against every cusp test, then that difference has a cuspidal
projection with an exponent decomposition whose nonzero components carry competing labels. -/
theorem exists_competing_cuspidalProjection
    (hproj : CuspidalProjectionDecompositionStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν,
      IsMaximalCompactSubgroup F (𝓕.M J')
        (K.comap (map F (𝓕.M J') G (𝓕.l J' ≫ 𝓕.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    (J : StandardIndex F G 𝓕.i 𝓕.ν) (data : CompetingWeylExponents 𝓕 I J 1) (nexp : ℕ)
    (lam : ComplexCharacterParameter F (𝓕.P I)) {w Φ : AdelicGroupPoints F G → ℂ}
    (hw : 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho 𝓕.top w)
    (hΦ : J ≤ I → 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I Φ)
    (heq : ∀ test, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
      ∀ (b : 𝓕.positiveSplitComponent J) (g : AdelicGroupPoints F G),
        ∑ k ∈ Finset.range ((𝓕.competingTestPolynomial J data nexp lam b).natDegree + 1),
          (𝓕.competingTestPolynomial J data nexp lam b).coeff k *
            (𝓕.leviPairing J (𝓕.constantTerm J w)
                (map F (𝓕.P J) G (𝓕.p J) b.val ^ k * g) test -
              𝓕.leviPairing J (𝓕.parabolicConstantTerm I J Φ)
                (map F (𝓕.P J) G (𝓕.p J) b.val ^ k * g) test) = 0) :
    ∃ (vc : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
      (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ),
      𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
          (𝓕.constantTerm J w - 𝓕.parabolicConstantTerm I J Φ) vc ∧
        𝓕.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J vc s c ∧
        ∀ mu ∈ s, c mu ≠ 0 → ∃ k, mu = data.label k lam := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨ψw, hψw, -, sw, cw, hdw⟩ :=
    hproj F G 𝓕 K hKmax hKmin hKlevi rho hsmooth hrho 𝓕.top J (𝓕.le_top J) w hw
  have hproj' : ∃ (vc : AdelicGroupPoints F G → ℂ)
      (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
      (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ),
      𝓕.IsCuspidalProjection hsmooth Kinf rho J
          (𝓕.constantTerm J w - 𝓕.parabolicConstantTerm I J Φ) vc ∧
        𝓕.IsExponentDecomposition hsmooth Kinf rho J vc s c := by
    by_cases hJI : J ≤ I
    · obtain ⟨ψΦ, hψΦ, -, sΦ, cΦ, hdΦ⟩ :=
        hproj F G 𝓕 K hKmax hKmin hKlevi rho hsmooth hrho I J hJI Φ (hΦ hJI)
      have hf : 𝓕.parabolicConstantTerm I J Φ = 𝓕.constantTerm J Φ := by
        simp only [parabolicConstantTerm, ite_eq_left hJI]
      rw [hf]
      exact ⟨_, _, _, IsCuspidalProjection.sub 𝓕 hsmooth Kinf rho hψw hψΦ,
        IsExponentDecomposition.sub 𝓕 hsmooth Kinf rho hdw hdΦ⟩
    · have hf : 𝓕.parabolicConstantTerm I J Φ = 0 := by
        simp only [parabolicConstantTerm, ite_eq_right hJI]
      rw [hf, sub_zero]
      exact ⟨_, _, _, hψw, hdw⟩
  obtain ⟨vc, s, c, hvc, hdec⟩ := hproj'
  refine ⟨vc, s, c, hvc, hdec, fun mu hmu hc => ?_⟩
  have hfdom : ∀ test, 𝓕.IsLeviCuspForm Kinf rho J test →
      𝓕.constantTerm J w - 𝓕.parabolicConstantTerm I J Φ ∈ 𝓕.leviPairingDomain J test :=
    fun test ht g => (hvc.2.2 test ht g).1
  have hwdom : ∀ test, 𝓕.IsLeviCuspForm Kinf rho J test →
      𝓕.constantTerm J w ∈ 𝓕.leviPairingDomain J test :=
    fun test ht g => (hψw.2.2 test ht g).1
  have hΦdom : ∀ test, 𝓕.IsLeviCuspForm Kinf rho J test →
      𝓕.parabolicConstantTerm I J Φ ∈ 𝓕.leviPairingDomain J test := by
    intro test ht
    have h := (𝓕.leviPairingDomain J test).sub_mem (hwdom test ht) (hfdom test ht)
    simpa only [sub_sub_cancel] using h
  have hann : ∀ b : 𝓕.positiveSplitComponent J,
      Polynomial.aeval (𝓕.splitComponentRepresentation J b)
          (𝓕.competingTestPolynomial J data nexp lam b)
          (𝓕.constantTerm J w - 𝓕.parabolicConstantTerm I J Φ) ∈
        𝓕.cuspidalAnnihilator Kinf rho J := by
    intro b test ht g
    refine ⟨𝓕.aeval_mem_leviPairingDomain J test b _ (hfdom test ht) g, ?_⟩
    rw [𝓕.leviPairing_aeval_splitComponent J test b _ (hfdom test ht) g,
      𝓕.aeval_splitComponentRepresentation_apply]
    rw [← heq test ht b g]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [𝓕.leviPairing_sub J _ test (hwdom test ht _) (hΦdom test ht _)]
  obtain ⟨k, -, hk⟩ := 𝓕.exists_eq_of_aeval_mem_cuspidalAnnihilator J hproj K hKmax hKmin hKlevi
    rho hsmooth hrho hvc s c hdec (Finset.univ : Finset (Fin data.size))
    (fun k => data.label k lam) (fun b => 𝓕.competingTestPolynomial J data nexp lam b)
    (fun b z hz => 𝓕.exists_eq_of_competingTestPolynomial_eval_eq_zero J data nexp lam b hz)
    hann mu hmu hc
  exact ⟨k, hk⟩

/-! ### The identity term of the homogeneous equations -/

/-- The tested constant term along `Q ≤ I` of a twisted combination `∑ a i (φ i)_λ` of
automorphic inducing functions is annihilated by every translation polynomial divisible by the
factors of the twisted exponents of the cuspidal projections of the `C_Q (φ i)`. -/
theorem isTranslationPolynomialSolution_identityPairing
    (hproj : CuspidalProjectionDecompositionStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν,
      IsMaximalCompactSubgroup F (𝓕.M J')
        (K.comap (map F (𝓕.M J') G (𝓕.l J' ≫ 𝓕.p J')).toMonoidHom))
    [IsClosedImmersion (𝓕.p I).hom.hom.left] (hK : IsIwasawaCompact (𝓕.p I) K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {Q : StandardIndex F G 𝓕.i 𝓕.ν} (hQI : Q ≤ I) {m : ℕ}
    (φ : Fin m → AdelicGroupPoints F G → ℂ)
    (hφ : ∀ i, 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I (φ i))
    (ψ : Fin m → AdelicGroupPoints F G → ℂ)
    (s : Fin m → Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : Fin m → ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ)
    (deg : Fin m → ComplexCharacterParameter F (𝓕.P Q) → ℕ)
    (hψ : ∀ i, 𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q
      (𝓕.constantTerm Q (φ i)) (ψ i))
    (hdec : ∀ i, 𝓕.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q
      (ψ i) (s i) (c i))
    (hdeg : ∀ i, ∀ mu ∈ s i, 𝓕.HasPolynomialOrbit Q mu (deg i mu) (c i mu))
    (lam : ComplexCharacterParameter F (𝓕.P I)) (a : Fin m → ℂ)
    {test : AdelicGroupPoints F (𝓕.M Q) → ℂ}
    (ht : 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho Q test)
    (b : 𝓕.positiveSplitComponent Q) (D : ℂ[X])
    (hD : ∀ i, ∀ mu ∈ s i, (X - C (parameterPower F (𝓕.P Q)
      (mu + parameterRestrict (𝓕.nestedParabolicHom hQI) lam) b.val)) ^ (deg i mu + 1) ∣ D) :
    IsTranslationPolynomialSolution (map F (𝓕.P Q) G (𝓕.p Q) b.val) D
      (fun h => 𝓕.leviPairing Q (𝓕.parabolicConstantTerm I Q
        (fun x => ∑ i, a i * hK.parameterTwist (φ i) lam x)) h test) := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hcdom : ∀ i, ∀ mu ∈ s i, c i mu ∈ 𝓕.leviPairingDomain Q test := fun i mu hmu =>
    𝓕.mem_leviPairingDomain_of_isAutomorphicOn Q hproj K hKmax hKmin hKlevi rho hsmooth hrho
      ((hdec i).automorphic mu hmu) ht
  have hfun : (fun x => ∑ i, a i * hK.parameterTwist (φ i) lam x) =
      hK.parameterTwist (∑ i, a i • φ i) lam := by
    funext x
    simp only [IsIwasawaCompact.parameterTwist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
  have hpair : ∀ h, 𝓕.leviPairing Q (𝓕.parabolicConstantTerm I Q
      (fun x => ∑ i, a i * hK.parameterTwist (φ i) lam x)) h test =
      ∑ i, a i * ∑ mu ∈ s i, 𝓕.leviPairing Q (hK.parameterTwist (c i mu) lam) h test := by
    intro h
    rw [hfun, 𝓕.leviPairing_parabolicConstantTerm_twist_sum_smul I Q rho hsmooth Kinf hK lam φ hφ
      a test (fun _ i => fun g => ((hψ i).2.2 test ht g).1) h]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [parabolicConstantTerm, ite_eq_left hQI]
    rw [𝓕.leviPairing_constantTerm_parameterTwist I Q hK hQI, ((hψ i).2.2 test ht h).2.2,
      (hdec i).sum_eq]
    have hsum : (∑ mu ∈ s i, c i mu) = fun x => ∑ mu ∈ s i, (1 : ℂ) * c i mu x := by
      funext x
      simp only [Finset.sum_apply, one_mul]
    rw [hsum, 𝓕.leviPairing_finsetSum Q (s i) (fun _ => 1) (c i) h test
      (fun mu hmu => hcdom i mu hmu h), Finset.sum_mul]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [one_mul, 𝓕.leviPairing_parameterTwist_of_le hQI hK]
  refine AdelicGroupPoints.IsTranslationPolynomialSolution.congr ?_ hpair
  refine isTranslationPolynomialSolution_sum_of_dvd Finset.univ _ a fun i _ => ?_
  refine AdelicGroupPoints.IsTranslationPolynomialSolution.congr
    (isTranslationPolynomialSolution_sum_of_dvd (s i)
      (fun mu h => 𝓕.leviPairing Q (hK.parameterTwist (c i mu) lam) h test) (fun _ => 1)
      fun mu hmu => ?_) fun h => by simp only [one_mul]
  exact 𝓕.isTranslationPolynomialSolution_leviPairing_of_polynomialOrbit Q test b
    (HasPolynomialOrbit.parameterTwist 𝓕 hQI hK lam (hdeg i mu hmu))
    (𝓕.parameterTwist_mem_leviPairingDomain hQI hK lam (hcdom i mu hmu)) (hD i mu hmu)

end StandardParabolicFamily

/-- The premises of the conditional proof of `EisensteinCuspidalTestSystemStatement`. -/
def EisensteinCuspidalTestSystemReductionStatement : Prop :=
  EisensteinStandardizationStatement.{u} → EisensteinUniformCuspidalExpansionStatement.{u} →
    EisensteinRegularUniquenessStatement.{u} → CuspidalProjectionDecompositionStatement.{u} →
    LeviCuspFormPairingMajorantStatement.{u} → ParameterTwistAutomorphyStatement.{u} →
    EisensteinCuspidalTestSystemStatement.{u}

set_option maxHeartbeats 800000 in
theorem eisensteinCuspidalTestSystem_of : EisensteinCuspidalTestSystemReductionStatement.{u} := by
  intro hstd hexp huniq hproj hmaj htwist F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU
    K hK N d rho hN hrho hsmooth hcalc φ hKmax hφ
  obtain ⟨fam, I, K', hK', t, iota, m, φ', ℓ, -, -, hK'max, hK'min, hK'levi, hφ', haut, hrest⟩ :=
    hstd F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hrho hKmax hφ
  let instW : Fintype (relativeWeylGroup fam.i) :=
    @Fintype.ofFinite _ (ArthurRelative.finite_relativeWeylGroup fam.connectedReductive
      fam.maximalSplit)
  have instP : IsClosedImmersion (fam.p I).hom.hom.left :=
    (fam.isCompatible I).parabolic.isClosedSubgroup
  have instf : Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left := by
    let := (fam.isCompatible I).splitComponent.1.isSplitSubtorus.mono
    let := (fam.isCompatible I).levi.isClosedSubgroup.mono
    let := (fam.isCompatible I).parabolic.isClosedSubgroup.mono
    have : Mono (fam.a I ≫ fam.l I ≫ fam.p I).hom.hom.left := by
      change Mono ((fam.a I).hom.hom.left ≫ (fam.l I).hom.hom.left ≫ (fam.p I).hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) (fam.isCompatible I).factor_comp)
  have hrest' := @hrest instW instP instf
  dsimp only at hrest'
  obtain ⟨hreg, R1, hE⟩ := hrest'
  set Kinf' := K'.comap (ofInfinite F G).toMonoidHom with hKinf'
  set tG : AdelicGroupPoints F G := ofInfinite F G t with htG
  -- the premises in the standard setting
  have hexp' := hexp F G fam I K' hK' hK'max hK'min hK'levi rho hsmooth hrho m φ' hφ'
  choose R2 data nexp hexpJ using hexp'
  obtain ⟨R3, huniq'⟩ :=
    huniq F G fam I K' hK' hK'max hK'min hK'levi rho hsmooth hrho m φ' hφ' data
  have hmaj' := hmaj F G fam K' hK'max hK'min hK'levi rho hrho
  have hid : ∀ (Q : StandardIndex F G fam.i fam.ν) (i : Fin m),
      ∃ (ψ : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (fam.P Q)))
        (c : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ)
        (deg : ComplexCharacterParameter F (fam.P Q) → ℕ),
        Q ≤ I → (fam.IsCuspidalProjection hsmooth Kinf' rho Q (fam.constantTerm Q (φ' i)) ψ ∧
          fam.IsExponentDecomposition hsmooth Kinf' rho Q ψ s c ∧
          ∀ mu ∈ s, fam.HasPolynomialOrbit Q mu (deg mu) (c mu)) := by
    intro Q i
    by_cases hQI : Q ≤ I
    · obtain ⟨ψ, hψ, -, s, c, hdec⟩ :=
        hproj F G fam K' hK'max hK'min hK'levi rho hsmooth hrho I Q hQI (φ' i) (hφ' i)
      classical
      choose deg hdeg using fun mu (hmu : mu ∈ s) => hdec.exponent mu hmu
      refine ⟨ψ, s, c, fun mu => if h : mu ∈ s then deg mu h else 0,
        fun _ => ⟨hψ, hdec, fun mu hmu => ?_⟩⟩
      simp only [dite_eq_left hmu]
      exact hdeg mu hmu
    · exact ⟨0, ∅, 0, 0, fun h => absurd h hQI⟩
  choose ψid sid cid degid hidd using hid
  -- thresholds
  have hfinI : Finite (StandardIndex F G fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i
      fam.ν).finite_subsets.to_subtype
  let _ : Fintype (StandardIndex F G fam.i fam.ν) := Fintype.ofFinite _
  obtain ⟨R', hR'⟩ := hreg ((∑ J, |R2 J|) + |R3|)
  let r' : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
    ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
  have hreg0 : ∀ lam : ComplexCharacterParameter F P,
      r.IsRegularParameter hA hT (max R1 R') lam →
        r.IsRegularParameter hA hT R1 lam ∧
        (∀ J, r'.IsRegularParameter (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 (R2 J) (iota lam)) ∧
        r'.IsRegularParameter (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 R3 (iota lam) := by
    intro lam hlam
    have h1 : r.IsRegularParameter hA hT R1 lam :=
      fun α hα => (le_max_left R1 R').trans_lt (hlam α hα)
    have h2 := hR' lam fun α hα => (le_max_right R1 R').trans_lt (hlam α hα)
    refine ⟨h1, fun J α hα => ?_, fun α hα => ?_⟩
    · refine lt_of_le_of_lt ?_ (h2 α hα)
      refine (le_abs_self (R2 J)).trans (le_add_of_le_of_nonneg ?_ (abs_nonneg _))
      exact Finset.single_le_sum (f := fun J => |R2 J|) (fun J _ => abs_nonneg _)
        (Finset.mem_univ J)
    · refine lt_of_le_of_lt ?_ (h2 α hα)
      exact (le_abs_self R3).trans (le_add_of_nonneg_left
        (Finset.sum_nonneg fun J _ => abs_nonneg _))
  have hEmin : ∀ (Q : StandardIndex F G fam.i fam.ν), IsIwasawaCompact (fam.p Q) K' := fun Q =>
    fam.isIwasawaCompact_of_le (show (⟨∅, Set.empty_subset _⟩ : StandardIndex F G fam.i fam.ν) ≤ Q
      from Set.empty_subset _) hK'min
  refine ⟨max R1 R', fam, K', hK'max, hEmin, fun n e => ?_⟩
  -- the polynomials
  let lamOf : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (fam.P I) :=
    iota.toLinearMap.comp e.toLinearMap
  have hlamOf : ∀ s, lamOf s = iota (e s) := fun _ => rfl
  let DA : ∀ Q : StandardIndex F G fam.i fam.ν, fam.positiveSplitComponent Q → (Fin n → ℂ) →
      Polynomial ℂ := fun Q b s =>
    fam.cuspidalTestPolynomial Q (data Q) (nexp Q) (sid Q) (degid Q) (lamOf s) b
  let degA : StandardIndex F G fam.i fam.ν → ℕ := fun Q =>
    ∑ x ∈ fam.cuspidalTestLabels Q (data Q) (sid Q),
      (fam.cuspidalTestMultiplicity Q (data Q) (nexp Q) (degid Q) x + 1)
  have hDAdeg : ∀ Q b s, (DA Q b s).natDegree = degA Q := fun Q b s =>
    fam.cuspidalTestPolynomial_natDegree Q (data Q) (nexp Q) (sid Q) (degid Q) (lamOf s) b
  let PB : ∀ J : StandardIndex F G fam.i fam.ν, fam.positiveSplitComponent J → (Fin n → ℂ) →
      Polynomial ℂ := fun J b s => fam.competingTestPolynomial J (data J) (nexp J) (lamOf s) b
  have hPBdeg : ∀ J b s, (PB J b s).natDegree = (data J).size * (nexp J + 1) := fun J b s =>
    fam.competingTestPolynomial_natDegree J (data J) (nexp J) (lamOf s) b
  classical
  refine ⟨fun J b Q s => if h : Q ≤ J then DA Q (fam.splitComponentLift h b) s else X - C 1,
    fun J b Q => if Q ≤ J then degA Q else 1, ?_, ?_, fun L _ _ R => ?_⟩
  · intro J b Q s
    by_cases h : Q ≤ J
    · simp only [dite_eq_left h, ite_eq_left h]
      exact ⟨fam.cuspidalTestPolynomial_monic _ _ _ _ _ _ _, hDAdeg _ _ _,
        fam.cuspidalTestPolynomial_coeff_zero_ne_zero _ _ _ _ _ _ _⟩
    · simp only [dite_eq_right h, ite_eq_right h]
      refine ⟨monic_X_sub_C 1, natDegree_X_sub_C 1, ?_⟩
      simp
  · intro J b Q k
    by_cases h : Q ≤ J
    · simp only [dite_eq_left h]
      exact fam.cuspidalTestPolynomial_entire Q (data Q) (nexp Q) (sid Q) (degid Q) lamOf _ k
    · simp only [dite_eq_right h]
      exact differentiable_const _
  -- the system
  let 𝔉 := UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
  let value : 𝔉 → AdelicGroupPoints F G → ℂ :=
    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
  let pairCLM : ∀ Q : StandardIndex F G fam.i fam.ν,
      {ψ : AdelicGroupPoints F (fam.M Q) → ℂ // fam.IsLeviCuspForm Kinf' rho Q ψ} →
      AdelicGroupPoints F G → (𝔉 →L[ℂ] ℂ) := fun Q ψ g =>
    fam.constantTermLeviPairingCLM Q ψ.1 ψ.2.1.1 g rho hN hrho hsmooth hcalc R L ψ.2.1.2.1.1
      (hmaj' Q ψ.1 ψ.2 g R)
  have hpairCLM : ∀ Q ψ g (v : 𝔉),
      pairCLM Q ψ g v = fam.leviPairing Q (fam.constantTerm Q (value v)) g ψ.1 :=
    fun _ _ _ _ => rfl
  have hdomv : ∀ Q (ψ : {ψ : AdelicGroupPoints F (fam.M Q) → ℂ //
      fam.IsLeviCuspForm Kinf' rho Q ψ}) (v : 𝔉),
      fam.constantTerm Q (value v) ∈ fam.leviPairingDomain Q ψ.1 := fun Q ψ v g =>
    ((fam.exists_leviPairing_constantTerm_bound Q ψ.1 ψ.2.1.1 g rho hN hrho hsmooth hcalc R L
      ψ.2.1.2.1.1 (hmaj' Q ψ.1 ψ.2 g R)).choose_spec v).1
  let Φs : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ := fun s x =>
    ∑ i, Complex.exp (ℓ i (e s)) * hK'.parameterTwist (φ' i) (lamOf s) x
  let IdxA := Σ J : StandardIndex F G fam.i fam.ν, Σ _ : fam.positiveSplitComponent J,
    Σ Q : {Q : StandardIndex F G fam.i fam.ν // Q ≤ J},
    Σ _ : {ψ : AdelicGroupPoints F (fam.M Q.1) → ℂ // fam.IsLeviCuspForm Kinf' rho Q.1 ψ},
    AdelicGroupPoints F G
  let IdxB := Σ J : StandardIndex F G fam.i fam.ν, Σ _ : fam.positiveSplitComponent J,
    Σ _ : {ψ : AdelicGroupPoints F (fam.M J) → ℂ // fam.IsLeviCuspForm Kinf' rho J ψ},
    AdelicGroupPoints F G
  let eqnA : IdxA → (Fin n → ℂ) → 𝔉 →L[ℂ] ℂ := fun x s =>
    ∑ k ∈ Finset.range (degA x.2.2.1.1 + 1),
      (DA x.2.2.1.1 (fam.splitComponentLift x.2.2.1.2 x.2.1) s).coeff k •
        pairCLM x.2.2.1.1 x.2.2.2.1 (map F (fam.P x.1) G (fam.p x.1) x.2.1.val ^ k * x.2.2.2.2)
  let eqnB : IdxB → (Fin n → ℂ) → 𝔉 →L[ℂ] ℂ := fun y s =>
    ∑ k ∈ Finset.range ((data y.1).size * (nexp y.1 + 1) + 1),
      (PB y.1 y.2.1 s).coeff k •
        pairCLM y.1 y.2.2.1 (map F (fam.P y.1) G (fam.p y.1) y.2.1.val ^ k * y.2.2.2)
  let cB : IdxB → (Fin n → ℂ) → ℂ := fun y s =>
    ∑ k ∈ Finset.range ((data y.1).size * (nexp y.1 + 1) + 1),
      (PB y.1 y.2.1 s).coeff k * fam.leviPairing y.1 (fam.parabolicConstantTerm I y.1 (Φs s))
        (map F (fam.P y.1) G (fam.p y.1) y.2.1.val ^ k * y.2.2.2 * tG⁻¹) y.2.2.1.1
  -- holomorphy of the right-hand sides
  have hΦpair : ∀ (J : StandardIndex F G fam.i fam.ν)
      (ψ : {ψ : AdelicGroupPoints F (fam.M J) → ℂ // fam.IsLeviCuspForm Kinf' rho J ψ})
      (h : AdelicGroupPoints F G), Differentiable ℂ fun s =>
        fam.leviPairing J (fam.parabolicConstantTerm I J (Φs s)) h ψ.1 := by
    intro J ψ h
    have hrw : ∀ s, fam.leviPairing J (fam.parabolicConstantTerm I J (Φs s)) h ψ.1 =
        ∑ i, Complex.exp (ℓ i (e s)) * fam.leviPairing J (fam.parabolicConstantTerm I J
          (hK'.parameterTwist (φ' i) (lamOf s))) h ψ.1 := by
      intro s
      have hfun : Φs s = hK'.parameterTwist (∑ i, Complex.exp (ℓ i (e s)) • φ' i) (lamOf s) := by
        funext x
        simp only [Φs, IsIwasawaCompact.parameterTwist, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_mul, mul_assoc]
      rw [hfun]
      exact fam.leviPairing_parabolicConstantTerm_twist_sum_smul I J rho hsmooth Kinf' hK'
        (lamOf s) φ' hφ' _ ψ.1 (fun hJI i g => ((hidd J i hJI).1.2.2 ψ.1 ψ.2 g).1) h
    simp only [hrw]
    refine Differentiable.fun_sum fun i _ => ?_
    have hexp : Differentiable ℂ fun s => Complex.exp (ℓ i (e s)) :=
      (LinearMap.toContinuousLinearMap ((ℓ i).comp e.toLinearMap)).differentiable.cexp
    refine hexp.mul ?_
    by_cases hJI : J ≤ I
    · simp only [StandardParabolicFamily.parabolicConstantTerm, ite_eq_left hJI,
        fam.leviPairing_constantTerm_parameterTwist I J hK' hJI]
      refine (differentiable_const _).mul ?_
      exact (LinearMap.toContinuousLinearMap
        (((complexParameterPairing F (fam.P I)).flip (hK'.height h)).comp lamOf)).differentiable.cexp
    · simp only [StandardParabolicFamily.parabolicConstantTerm, ite_eq_right hJI]
      exact differentiable_const _
  refine ⟨IdxA ⊕ IdxB, fun i s => Sum.elim (fun x => eqnA x s) (fun y => eqnB y s) i,
    fun i s => Sum.elim (fun _ => (0 : ℂ)) (fun y => cB y s) i, ⟨fun i => ?_, fun i => ?_⟩,
    ?_, ?_, ?_⟩
  · -- the operators are holomorphic
    intro v lf
    refine (Differentiable.mdifferentiable ?_).mdifferentiableOn
    refine lf.differentiable.comp ?_
    rcases i with x | y
    · change Differentiable ℂ fun s => eqnA x s v
      simp only [eqnA, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact Differentiable.fun_sum fun k _ =>
        (fam.cuspidalTestPolynomial_entire _ _ _ _ _ lamOf _ k).mul_const _
    · change Differentiable ℂ fun s => eqnB y s v
      simp only [eqnB, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact Differentiable.fun_sum fun k _ =>
        (fam.competingTestPolynomial_entire _ _ _ lamOf _ k).mul_const _
  · -- the right-hand sides are holomorphic
    intro lf
    refine (Differentiable.mdifferentiable ?_).mdifferentiableOn
    refine lf.differentiable.comp ?_
    rcases i with x | y
    · exact differentiable_const _
    · change Differentiable ℂ fun s => cB y s
      exact Differentiable.fun_sum fun k _ =>
        (fam.competingTestPolynomial_entire _ _ _ lamOf _ k).mul (hΦpair _ _ _)
  · -- clause (8.3): the homogeneous equations are part of the system
    intro s v hv J b Q hQJ
    change (fun g => ∑ k ∈ Finset.range ((if h : Q ≤ J then DA Q (fam.splitComponentLift h b) s
        else X - C 1).natDegree + 1), (if h : Q ≤ J then DA Q (fam.splitComponentLift h b) s
        else X - C 1).coeff k * fam.constantTerm Q (value v)
          (map F (fam.P J) G (fam.p J) b.val ^ k * g)) ∈ fam.cuspidalAnnihilator Kinf' rho Q
    simp only [dite_eq_left hQJ]
    rw [← fam.map_splitComponentLift hQJ b]
    refine fam.translate_mem_cuspidalAnnihilator Kinf' rho Q (fam.splitComponentLift hQJ b)
      (DA Q (fam.splitComponentLift hQJ b) s) (fun test ht => hdomv Q ⟨test, ht⟩ v)
      (fun test ht g => ?_)
    have h := hv (Sum.inl ⟨J, b, ⟨Q, hQJ⟩, ⟨test, ht⟩, g⟩)
    change eqnA ⟨J, b, ⟨Q, hQJ⟩, ⟨test, ht⟩, g⟩ s v = 0 at h
    simp only [eqnA, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hpairCLM] at h
    rw [hDAdeg, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fam.map_splitComponentLift hQJ b]
  · -- regular solution (Corollary 6.10, through the uniform expansion premise): a stage vector
    -- equal to the Eisenstein series is a solution
    intro s hs v hv i
    obtain ⟨hs1, hs2, -⟩ := hreg0 (e s) hs
    let aco : Fin m → ℂ := fun i => Complex.exp (ℓ i (e s))
    let ES : AdelicGroupPoints F G → ℂ := fun x =>
      ∑ i, aco i * hK'.eisensteinSeries (φ' i) (lamOf s) x
    have hvE : value v = fun x => ES (x * tG⁻¹) := by
      funext x
      change UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v x = _
      rw [hv]
      have h := hE (e s) hs1 (x * tG⁻¹)
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have hpairE : ∀ Q (ψ : {ψ : AdelicGroupPoints F (fam.M Q) → ℂ //
        fam.IsLeviCuspForm Kinf' rho Q ψ}) h,
        pairCLM Q ψ h v = fam.leviPairing Q (fam.constantTerm Q ES) (h * tG⁻¹) ψ.1 := by
      intro Q ψ h
      rw [hpairCLM, hvE]
      have hc : fam.constantTerm Q (fun x => ES (x * tG⁻¹)) =
          fun g => fam.constantTerm Q ES (g * tG⁻¹) :=
        funext fun g => fam.constantTerm_mul_right Q ES tG⁻¹ g
      rw [hc, fam.leviPairing_mul_right]
    rcases i with ⟨J, b, ⟨Q, hQJ⟩, ψ, g⟩ | ⟨J, b, ψ, g⟩
    · -- the homogeneous equations
      change eqnA ⟨J, b, ⟨Q, hQJ⟩, ψ, g⟩ s v = 0
      obtain ⟨terms, hpoly, hpair⟩ := hexpJ Q (lamOf s) (hs2 Q) aco
      let b' := fam.splitComponentLift hQJ b
      have hid : IsTranslationPolynomialSolution (map F (fam.P Q) G (fam.p Q) b'.val)
          (DA Q b' s) (fun h => fam.leviPairing Q (fam.parabolicConstantTerm I Q (Φs s)) h ψ.1) := by
        by_cases hQI : Q ≤ I
        · refine fam.isTranslationPolynomialSolution_identityPairing hproj K' hK'max hK'min
            hK'levi hK' rho hsmooth hrho hQI φ' hφ' (ψid Q) (sid Q) (cid Q) (degid Q)
            (fun i => (hidd Q i hQI).1) (fun i => (hidd Q i hQI).2.1)
            (fun i => (hidd Q i hQI).2.2) (lamOf s) aco ψ.2 b' (DA Q b' s) ?_
          intro i mu hmu
          have hmem : (Sum.inr ⟨i, mu⟩ : Fin (data Q).size ⊕
              (Σ _ : Fin m, ComplexCharacterParameter F (fam.P Q))) ∈
              fam.cuspidalTestLabels Q (data Q) (sid Q) := by
            simp only [StandardParabolicFamily.cuspidalTestLabels, Finset.inr_mem_disjSum, ite_eq_left hQI, Finset.mem_sigma,
              Finset.mem_univ, true_and]
            exact hmu
          have hdvd : (X - C (fam.cuspidalTestRoot Q (data Q) (lamOf s) b' (Sum.inr ⟨i, mu⟩))) ^
              (fam.cuspidalTestMultiplicity Q (data Q) (nexp Q) (degid Q) (Sum.inr ⟨i, mu⟩) + 1) ∣
              DA Q b' s :=
            Finset.dvd_prod_of_mem (fun x => (X - C (fam.cuspidalTestRoot Q (data Q)
              (lamOf s) b' x)) ^ (fam.cuspidalTestMultiplicity Q (data Q) (nexp Q) (degid Q) x + 1))
              hmem
          have hroot : fam.cuspidalTestRoot Q (data Q) (lamOf s) b' (Sum.inr ⟨i, mu⟩) =
              parameterPower F (fam.P Q)
                (mu + parameterRestrict (fam.nestedParabolicHom hQI) (lamOf s)) b'.val := by
            simp only [StandardParabolicFamily.cuspidalTestRoot, dite_eq_left hQI]
          have hmult : fam.cuspidalTestMultiplicity Q (data Q) (nexp Q) (degid Q)
              (Sum.inr ⟨i, mu⟩) = degid Q i mu := rfl
          rw [hroot, hmult] at hdvd
          exact hdvd
        · refine AdelicGroupPoints.IsTranslationPolynomialSolution.congr
            (AdelicGroupPoints.IsTranslationPolynomialSolution.zero _ _) fun h => ?_
          simp only [StandardParabolicFamily.parabolicConstantTerm, ite_eq_right hQI, Pi.zero_apply]
          simp [StandardParabolicFamily.leviPairing, StandardParabolicFamily.leviPairingIntegrand]
      have hterms : IsTranslationPolynomialSolution (map F (fam.P Q) G (fam.p Q) b'.val)
          (DA Q b' s) (fun h => ∑ k ∈ Finset.univ, (1 : ℂ) * fam.leviPairing Q (terms k) h ψ.1) :=
        isTranslationPolynomialSolution_sum_of_dvd Finset.univ _ _ fun k _ =>
          fam.isTranslationPolynomialSolution_leviPairing_of_polynomialOrbit Q ψ.1 b' (hpoly k)
            (fun h => (hpair ψ.1 ψ.2 h).1 k)
            ((Finset.dvd_prod_of_mem (fun k => (X - C (parameterPower F (fam.P Q)
              ((data Q).label k (lamOf s)) b'.val)) ^ (nexp Q + 1)) (Finset.mem_univ k)).trans
              (fam.competingTestPolynomial_dvd Q (data Q) (nexp Q) (sid Q) (degid Q) (lamOf s) b'))
      have hsol := (hid.add hterms).congr (ψ := fun h =>
        fam.leviPairing Q (fam.constantTerm Q ES) h ψ.1) fun h => by
          rw [← sub_eq_iff_eq_add', (hpair ψ.1 ψ.2 h).2]
          simp only [one_mul]
      have h0 := hsol (g * tG⁻¹)
      rw [hDAdeg] at h0
      simp only [eqnA, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hpairE]
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fam.map_splitComponentLift hQJ b, mul_assoc]
    · -- the non-homogeneous equations
      change eqnB ⟨J, b, ψ, g⟩ s v = cB ⟨J, b, ψ, g⟩ s
      obtain ⟨terms, hpoly, hpair⟩ := hexpJ J (lamOf s) (hs2 J) aco
      have hterms : IsTranslationPolynomialSolution (map F (fam.P J) G (fam.p J) b.val)
          (PB J b s) (fun h => ∑ k ∈ Finset.univ, (1 : ℂ) * fam.leviPairing J (terms k) h ψ.1) :=
        isTranslationPolynomialSolution_sum_of_dvd Finset.univ _ _ fun k _ =>
          fam.isTranslationPolynomialSolution_leviPairing_of_polynomialOrbit J ψ.1 b (hpoly k)
            (fun h => (hpair ψ.1 ψ.2 h).1 k)
            (Finset.dvd_prod_of_mem (fun k => (X - C (parameterPower F (fam.P J)
              ((data J).label k (lamOf s)) b.val)) ^ (nexp J + 1)) (Finset.mem_univ k))
      have h0 := hterms (g * tG⁻¹)
      rw [hPBdeg] at h0
      simp only [eqnB, cB, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hpairE]
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_sub, (hpair ψ.1 ψ.2 _).2, mul_assoc]
      simp only [one_mul]
  · -- clause (6.22): uniqueness among automorphic solutions, through the competing-exponent
    -- support of (6.21)
    intro s hs v hv hautv
    obtain ⟨hs1, -, hs3⟩ := hreg0 (e s) hs
    let aco : Fin m → ℂ := fun i => Complex.exp (ℓ i (e s))
    let w : AdelicGroupPoints F G → ℂ := fun x => value v (x * tG)
    have hw : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf' rho w :=
      haut _ hautv
    have hwtop : fam.IsAutomorphicOn hsmooth Kinf' rho fam.top w :=
      (fam.isAutomorphicOn_top_iff rho hsmooth hcalc Kinf' w).mpr hw
    have hw' : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
        (rationalSubgroup F G) Kinf' rho w :=
      (fam.isAutomorphicOn_top_iff rho hsmooth _ Kinf' w).mp hwtop
    have hvw : value v = fun x => w (x * tG⁻¹) := by
      funext x
      simp only [w, mul_assoc, inv_mul_cancel, mul_one]
    have hΦaut : ∀ J : StandardIndex F G fam.i fam.ν, J ≤ I →
        fam.IsAutomorphicOn hsmooth Kinf' rho I (Φs s) := by
      intro _ _
      have hfun : Φs s = hK'.parameterTwist (∑ i, aco i • φ' i) (lamOf s) := by
        funext x
        simp only [Φs, aco, IsIwasawaCompact.parameterTwist, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_mul, mul_assoc]
      rw [hfun]
      exact htwist F G fam I K' hK' hK'max hK'min hK'levi rho hsmooth hrho _
        (fam.isAutomorphicOn_sum_smul hsmooth Kinf' rho I hφ' aco) (lamOf s)
    have hcomp := fun J => fam.exists_competing_cuspidalProjection hproj K' hK'max hK'min hK'levi
      rho hsmooth hrho J (data J) (nexp J) (lamOf s) hwtop (hΦaut J) (fun test ht b g => by
        have h := hv (Sum.inr ⟨J, b, ⟨test, ht⟩, g * tG⟩)
        change eqnB ⟨J, b, ⟨test, ht⟩, g * tG⟩ s v = cB ⟨J, b, ⟨test, ht⟩, g * tG⟩ s at h
        simp only [eqnB, cB, FunLike.coe_sum, Finset.sum_apply,
          FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hpairCLM] at h
        change ∑ k ∈ Finset.range ((PB J b s).natDegree + 1), (PB J b s).coeff k * _ = 0
        rw [hPBdeg]
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        convert h using 2 with k _ k _
        · have hc : fam.constantTerm J (value v) = fun x => fam.constantTerm J w (x * tG⁻¹) := by
            rw [hvw]
            exact funext fun x => fam.constantTerm_mul_right J w tG⁻¹ x
          rw [hc, fam.leviPairing_mul_right, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
        · rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one])
    have hwE := huniq' (lamOf s) hs3 aco w hw' hcomp
    funext x
    change value v x = _
    rw [hvw]
    change w (x * tG⁻¹) = _
    rw [hwE]
    have h := hE (e s) hs1 (x * tG⁻¹)
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm

end Langlands.Global
