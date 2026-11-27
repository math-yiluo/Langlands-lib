import Langlands.Global.AdelicStandardFamilyPresentation
import Langlands.Global.AdelicLeviPairingAutomorphicTests
import Langlands.Global.AdelicExponentPolynomials
import Langlands.Global.AdelicEisensteinInducingPairingContinuation
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Global.AdelicSelfWeylParameters
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicStandardTopAutomorphy

/-! # Exponent terms of nested twists and of convergent Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local instance farRegionTermsSplitCommGroup (J : StandardIndex F G fam.i fam.ν) :
    CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.2 b.2)

/-- Twisting by the height of a larger standard parabolic `Q ⊇ J` adds the restriction of
the twisting parameter to an unnormalized exponent along `J`. -/
theorem hasUnnormalizedExponent_parameterTwist_of_le {J Q : StandardIndex F G fam.i fam.ν}
    (hJQ : J ≤ Q) [IsClosedImmersion (fam.p Q).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hKQ : IsIwasawaCompact (fam.p Q) K)
    (mu : ComplexCharacterParameter F (fam.P Q)) {lam : ComplexCharacterParameter F (fam.P J)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : fam.HasUnnormalizedExponent J lam φ) :
    fam.HasUnnormalizedExponent J (lam + parameterRestrict (fam.nestedParabolicHom hJQ) mu)
      (hKQ.parameterTwist φ mu) := by
  obtain ⟨m, hm⟩ := hφ
  refine ⟨m, fun g => ?_⟩
  obtain ⟨P, hP, hval⟩ := hm g
  let s := parameterRestrict (fam.nestedParabolicHom hJQ) mu
  refine ⟨hKQ.heightPower mu g • P, Submodule.smul_mem _ _ hP, ?_⟩
  intro x hx
  have hheight : hKQ.heightPower mu (map F (fam.P J) G (fam.p J) x * g) =
      parameterPower F (fam.P J) s x * hKQ.heightPower mu g := by
    have hx' : map F (fam.P J) G (fam.p J) x =
        map F (fam.P Q) G (fam.p Q) (map F (fam.P J) (fam.P Q) (fam.nestedParabolicHom hJQ) x) := by
      rw [← map_comp_apply_of_hom, fam.nestedParabolicHom_comp hJQ]
    rw [hx', parameterPower_parameterRestrict]
    simp only [IsIwasawaCompact.heightPower, hKQ.height_map_mul, map_add, Complex.exp_add,
      parameterPower]
  have hcancel : parameterPower F (fam.P J) s x * parameterPower F (fam.P J) (-s) x = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  calc
    _ = hKQ.heightPower mu g *
        (fam.unnormalizedAction J x φ g * parameterPower F (fam.P J) (-lam) x) *
        (parameterPower F (fam.P J) s x * parameterPower F (fam.P J) (-s) x) := by
      simp only [unnormalizedAction, IsIwasawaCompact.parameterTwist, hheight, neg_add_rev,
        parameterPower_add, s]
      ring
    _ = _ := by rw [hcancel, mul_one, hval x hx]; rfl

variable (Q J : StandardIndex F G fam.i fam.ν)
  [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p Q).hom.hom.left]
  [Mono (CommGroupScheme.groupHom (fam.f Q)).hom.hom.left]

/-- **Identity Weyl element in the convergence region.** For finitely many inducing forms
on `X_Q`, one threshold and finitely many identity-element competing label families serve
all coefficient vectors: the scalar test of `C_J` of the combination of convergent
`Q`-series, minus the test of the nested constant term of the twisted combination, is a
finite sum of joint generalized eigenvectors with exponents among the labels. -/
theorem exists_identityWeyl_support (hExp : ConvergentCuspidalTestExpansionStatement.{u})
    {K : Subgroup (AdelicGroupPoints F G)} (hKQ : IsIwasawaCompact (fam.p Q) K)
    (hKmax : IsMaximalCompactSubgroup F G K)
    (hK0 : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J')
      (K.comap (map F (fam.M J') G (fam.l J' ≫ fam.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {k : ℕ} (ψ : Fin k → AdelicGroupPoints F G → ℂ)
    (hψ : ∀ i, fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q (ψ i))
    (hψint : J ≤ Q → ∀ i (test : AdelicGroupPoints F (fam.M J) → ℂ),
      fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
        fam.constantTerm J (ψ i) ∈ fam.leviPairingDomain J test) :
    ∃ (R : ℝ) (data : Fin k → CompetingWeylExponents fam Q J
        (QuotientGroup.mk (1 : normalizerPoints fam.i))),
      ∀ mu : ComplexCharacterParameter F (fam.P Q),
        (fam.standardPresentation Q).IsRegularParameter (fam.isSplitTorus_splitComponent Q)
          fam.isSplitTorus_torus R mu →
        (∀ i, fam.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho fam.top
          (hKQ.eisensteinSeries (ψ i) mu)) →
        (∀ i (test : AdelicGroupPoints F (fam.M J) → ℂ),
          fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
            fam.constantTerm J (hKQ.eisensteinSeries (ψ i) mu) ∈ fam.leviPairingDomain J test) →
        ∀ (a : Fin k → ℂ) (test : AdelicGroupPoints F (fam.M J) → ℂ),
          fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
          IsJointlySupportedIn (fam.splitComponentRepresentation J)
            ((fun (ν : ComplexCharacterParameter F (fam.P J))
              (b : fam.positiveSplitComponent J) => parameterPower F (fam.P J) ν b.val) ''
                {ν | ∃ i j, ν = (data i).label j mu})
            (fun g => fam.leviPairing J
                (fam.constantTerm J (∑ i, a i • hKQ.eisensteinSeries (ψ i) mu)) g test -
              fam.leviPairing J (fam.parabolicConstantTerm Q J
                (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) := by
  classical
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hc1 : IsWeylConjugation (fam.p Q) (fam.l Q) (fam.p Q) (fam.l Q)
      (1 : normalizerPoints fam.i).val (𝟙 (fam.M Q)) :=
    isWeylConjugation_one (p := fam.p Q) (l := fam.l Q)
  have hone : ∀ α ∈ Q.val, schemeWeylCharacterAction fam.i
      (QuotientGroup.mk (1 : normalizerPoints fam.i) : relativeWeylGroup fam.i) α ∈ Q.val := by
    intro α hα
    rw [QuotientGroup.mk_one, map_one]
    exact hα
  have hone' : ∀ α ∈ Q.val, schemeWeylCharacterAction fam.i
      ((QuotientGroup.mk (1 : normalizerPoints fam.i) : relativeWeylGroup fam.i)⁻¹) α ∈ Q.val := by
    intro α hα
    rw [QuotientGroup.mk_one, inv_one, map_one]
    exact hα
  have hexp := fun i => hExp F G fam Q Q 1 (𝟙 (fam.M Q)) hc1 hone hone' K hKQ hKmax hK0 hKlevi
    rho hsmooth hrho (ψ i) (hψ i) J
  choose R data hdata using hexp
  refine ⟨∑ i, |R i|, data, fun mu hmu hEaut hEint a test ht => ?_⟩
  have hreg (i : Fin k) : (fam.standardPresentation Q).IsRegularParameter
      (fam.isSplitTorus_splitComponent Q) fam.isSplitTorus_torus (R i) mu := by
    have hle : R i ≤ ∑ j, |R j| := (le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))
    exact fun α hα => hle.trans_lt (hmu α hα)
  let S : Set (fam.positiveSplitComponent J → ℂ) :=
    (fun (ν : ComplexCharacterParameter F (fam.P J)) (b : fam.positiveSplitComponent J) =>
      parameterPower F (fam.P J) ν b.val) '' {ν | ∃ i j, ν = (data i).label j mu}
  have hterm (i : Fin k) : IsJointlySupportedIn (fam.splitComponentRepresentation J) S
      (fun g => fam.leviPairing J (fam.constantTerm J (hKQ.eisensteinSeries (ψ i) mu)) g test -
        fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist (ψ i) mu)) g test) := by
    obtain ⟨terms, hexpo, htests⟩ := hdata i mu (hreg i)
    have heq : (fun g => fam.leviPairing J (fam.constantTerm J (hKQ.eisensteinSeries (ψ i) mu)) g
        test - fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist (ψ i) mu)) g
          test) = ∑ j, fun g => fam.leviPairing J (terms j) g test := by
      funext g
      have h := (htests test ht g).2
      have hone_int : hKQ.intertwiningIntegral (fam.iU Q) (fam.iU Q ≫ fam.p Q)
          (1 : normalizerPoints fam.i).val (ψ i) mu = hKQ.parameterTwist (ψ i) mu :=
        funext fun g' => IsIwasawaCompact.intertwiningIntegral_one_self (iU := fam.iU Q) hKQ
          (fam.isUnipotentRadical Q) (ψ i)
          (fun x hx g'' => (hψ i).1 x (Subgroup.mem_sup_left hx) g'') mu g'
      rw [hone_int] at h
      simp only [Finset.sum_apply]
      exact h
    rw [heq]
    refine IsJointlySupportedIn.finset_sum _ _ fun j _ => IsJointlySupportedIn.of_mem (S := S)
      (δ := fun b : fam.positiveSplitComponent J => parameterPower F (fam.P J)
        ((data i).label j mu) b.val) (Set.mem_image_of_mem _ ⟨i, j, rfl⟩) ?_
    exact fam.leviPairing_mem_jointGenEigenspace J (fun g => (htests test ht g).1 j) (hexpo j)
  have hsplit : (fun g => fam.leviPairing J
        (fam.constantTerm J (∑ i, a i • hKQ.eisensteinSeries (ψ i) mu)) g test -
      fam.leviPairing J (fam.parabolicConstantTerm Q J
        (hKQ.parameterTwist (∑ i, a i • ψ i) mu)) g test) =
      ∑ i, a i • (fun g => fam.leviPairing J
          (fam.constantTerm J (hKQ.eisensteinSeries (ψ i) mu)) g test -
        fam.leviPairing J (fam.parabolicConstantTerm Q J (hKQ.parameterTwist (ψ i) mu)) g test) := by
    funext g
    rw [fam.leviPairing_constantTerm_sum_smul fam.top J rho hsmooth Kinf (fam.le_top J)
        (fun i => hKQ.eisensteinSeries (ψ i) mu) hEaut a test (fun i => hEint i test ht) g,
      fam.leviPairing_parabolicConstantTerm_twist_sum_smul Q J rho hsmooth Kinf hKQ mu ψ hψ a test
        (fun hJQ i => hψint hJQ i test ht) g]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hsplit]
  exact IsJointlySupportedIn.finset_sum _ _ fun i _ => (hterm i).smul (a i)

end Langlands.Global.StandardParabolicFamily
