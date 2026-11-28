import Langlands.Global.AdelicEisensteinFamilyLinearity

/-! # From one inducing function to finite families in the uniform cuspidal expansion

`EisensteinUniformCuspidalExpansionOneStatement` is the case of one inducing function of
`EisensteinUniformCuspidalExpansionStatement`, strengthened by the absolute convergence of the
two tested constant terms on the left. `eisensteinUniformCuspidalExpansion_of_one` derives the
statement for finite families from it. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The uniform cuspidal expansion for one automorphic inducing function `φ`, together with the
absolute convergence of the tested constant terms of `E(φ, λ)` and of `φ_λ`: for every
standard `J` there are a threshold, competing labels of the identity element and a degree bound
such that for every sufficiently regular `λ` the tested constant term along `J` of `E(φ, λ)`,
minus that of `φ_λ`, is a finite sum of tested terms with the competing exponents, each of
polynomial degree at most the bound. -/
def EisensteinUniformCuspidalExpansionOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (I : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p I) K),
      IsMaximalCompactSubgroup F G K →
      IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G fam.i fam.ν,
        IsMaximalCompactSubgroup F (fam.M J)
          (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom),
        IsClosedSubgroup rho →
        let Kinf := K.comap (ofInfinite F G).toMonoidHom
        let r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
          ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
        let hA := (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
        let hT := fam.maximalSplit.isSplitSubtorus.1
        ∀ phi : AdelicGroupPoints F G → ℂ, fam.IsAutomorphicOn hsmooth Kinf rho I phi →
          ∀ J : StandardIndex F G fam.i fam.ν,
            ∃ (R : ℝ) (data : CompetingWeylExponents fam I J 1) (n : ℕ),
              ∀ lam : ComplexCharacterParameter F (fam.P I), r.IsRegularParameter hA hT R lam →
                ∃ terms : Fin data.size → AdelicGroupPoints F G → ℂ,
                  (∀ k, fam.HasPolynomialOrbit J (data.label k lam) n (terms k)) ∧
                  ∀ test : AdelicGroupPoints F (fam.M J) → ℂ,
                    fam.IsLeviCuspForm Kinf rho J test →
                    ∀ g : AdelicGroupPoints F G,
                      (∀ k, Integrable (fam.leviPairingIntegrand J (terms k) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J))) ∧
                      Integrable (fam.leviPairingIntegrand J
                          (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      Integrable (fam.leviPairingIntegrand J
                          (fam.parabolicConstantTerm I J (hK.parameterTwist phi lam)) g test)
                        (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
                      fam.leviPairing J (fam.constantTerm J (hK.eisensteinSeries phi lam)) g test -
                          fam.leviPairing J (fam.parabolicConstantTerm I J
                            (hK.parameterTwist phi lam)) g test =
                        ∑ k, fam.leviPairing J (terms k) g test

/-- The finite-family statement follows from the statement for one inducing function: choose a
common threshold dominating the one-function expansion thresholds and the convergence thresholds
of the `φ_i` (the sum of their absolute values), take the supremum of the degree bounds,
concatenate the competing labels, and scale the terms of `φ_i` by `a_i`. -/
theorem eisensteinUniformCuspidalExpansion_of_one
    (h : EisensteinUniformCuspidalExpansionOneStatement.{u}) :
    EisensteinUniformCuspidalExpansionStatement.{u} := by
  intro F _ _ G _ _ _ fam I _ _ _ K hK hKmax hK0 hKJ N d rho hsmooth hrho Kinf r hA hT m phi
    hphi J
  classical
  have hone := fun i => h F G fam I K hK hKmax hK0 hKJ rho hsmooth hrho (phi i) (hphi i) J
  choose R data n hmain using hone
  have hconv := fun i => eisensteinAbsoluteConvergence F G (fam.P I) (fam.M I) (fam.U I)
    (fam.A I) (fam.p I) (fam.iU I) (fam.l I) (fam.a I) r hA hT fam.connectedReductive
    (fam.isUnipotentRadical I) K hK rho hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
    (phi i) hKmax hrho (hphi i)
  choose R' hR' using hconv
  obtain ⟨nP, ⟨e⟩⟩ := exists_complexParameterEquiv fam.connectedReductive
    (fam.isCompatible I).parabolic
  let R₀ : ℝ := ∑ i, (|R i| + |R' i|)
  have hRle : ∀ i, R i ≤ R₀ ∧ R' i ≤ R₀ := by
    intro i
    have hsingle : |R i| + |R' i| ≤ R₀ :=
      Finset.single_le_sum (f := fun i => |R i| + |R' i|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    exact ⟨((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))).trans hsingle,
      ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))).trans hsingle⟩
  let n₀ : ℕ := Finset.univ.sup n
  refine ⟨R₀, CompetingWeylExponents.sigma data, n₀, fun lam hlam a => ?_⟩
  have hreg : ∀ i, r.IsRegularParameter hA hT (R i) lam := fun i α hα =>
    (hRle i).1.trans_lt (hlam α hα)
  have hreg' : ∀ i, r.IsRegularParameter hA hT (R' i) lam := fun i α hα =>
    (hRle i).2.trans_lt (hlam α hα)
  have hterms := fun i => hmain i lam (hreg i)
  choose T hTpoly hTtest using hterms
  -- continuity and rational invariance of the summands
  have hEcont : ∀ i, Continuous (hK.eisensteinSeries (phi i) lam) := by
    intro i
    refine fam.continuous_eisensteinSeries_of_compactBound I hK (hphi i).2.1.1 lam
      fun C hC => ?_
    obtain ⟨b, hb, hbd⟩ := hR' i C hC nP e {e.symm lam} isCompact_singleton (by
      rintro s rfl
      simpa using hreg' i)
    exact ⟨b, hb, fun c g hg => by simpa using hbd c g hg (e.symm lam) rfl⟩
  have hEinv : ∀ i, IsLeftInvariantUnder F G (rationalSubgroup F G)
      (hK.eisensteinSeries (phi i) lam) := fun i =>
    eisensteinSeries_leftRationalInvariant hK (hphi i).1 (fam.isUnipotentRadical I)
      (fam.isCompatible I).levi lam
  have hCE : fam.constantTerm J (fun x => ∑ i, a i * hK.eisensteinSeries (phi i) lam x) =
      fun g => ∑ i, a i * fam.constantTerm J (hK.eisensteinSeries (phi i) lam) g :=
    fam.constantTerm_finset_sum J Finset.univ a _ fun i _ g =>
      fam.integrable_constantTermIntegrand_of_rationalInvariant J (hEcont i) (hEinv i) g
  have hCT : fam.parabolicConstantTerm I J
        (fun x => ∑ i, a i * hK.parameterTwist (phi i) lam x) =
      fun g => ∑ i, a i * fam.parabolicConstantTerm I J (hK.parameterTwist (phi i) lam) g :=
    fam.parabolicConstantTerm_finset_sum J I Finset.univ a _ fun hJI i _ g =>
      fam.integrable_constantTermIntegrand_parameterTwist I hK J hJI (hphi i).2.1.1 (hphi i).1
        lam g
  let σ := (finSigmaFinEquiv (n := fun i => (data i).size)).symm
  refine ⟨fun k x => a (σ k).1 * T (σ k).1 (σ k).2 x, fun k => ?_, fun test htest g => ?_⟩
  · exact fam.hasPolynomialOrbit_const_mul J
      (fam.hasPolynomialOrbit_of_degree_le J (Finset.le_sup (Finset.mem_univ _))
        (hTpoly (σ k).1 (σ k).2)) _
  have hi := fun i => hTtest i test htest g
  refine ⟨fun k => ?_, ?_⟩
  · rw [fam.leviPairingIntegrand_const_mul J]
    exact ((hi (σ k).1).1 (σ k).2).const_mul _
  rw [hCE, hCT, fam.leviPairing_finsetSum J Finset.univ a _ g test fun i _ => (hi i).2.1,
    fam.leviPairing_finsetSum J Finset.univ a _ g test fun i _ => (hi i).2.2.1,
    ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, fun i => (hi i).2.2.2, Finset.mul_sum, fam.leviPairing_const_mul J]
  calc ∑ i, ∑ j, a i * fam.leviPairing J (T i j) g test
      = ∑ q : (i : Fin m) × Fin (data i).size,
          a q.1 * fam.leviPairing J (T q.1 q.2) g test :=
        (Fintype.sum_sigma (fun q : (i : Fin m) × Fin (data i).size =>
          a q.1 * fam.leviPairing J (T q.1 q.2) g test)).symm
    _ = _ := (Fintype.sum_equiv σ _ _ fun k => rfl).symm

end Langlands.Global
