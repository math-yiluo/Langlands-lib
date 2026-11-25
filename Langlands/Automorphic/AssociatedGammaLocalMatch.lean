import Langlands.Automorphic.AssociatedGammaPreservation
import Langlands.Automorphic.AssociatedGammaArithmeticGamma
import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.LocalFactor.UnitaryRationalGamma
import Langlands.Automorphic.AssociatedTemperedLocalProof

/-!
# From a local pair gamma match to equal family gamma factors

If at a finite place the twisted local classes of the two families satisfy `IsPairGammaMatch`,
then the gamma factors of the automorphic and arithmetic Hecke families at that place are
meromorphically equal: both agree, as germs, with the rational spectral value of the common
gamma factor.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

section Local

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

/-- The gamma factor of twisted pair data is germ-equal to the rational spectral value of
every certified gamma factor of the twisted pair. -/
theorem meromorphicEq_pairDataFactors_gamma
    {ψ : Correspondence.NontrivialAdditiveCharacter K}
    {ν : Correspondence.LocalAdditiveHaarMeasure K} {r t : ℕ}
    {π : Correspondence.AutomorphicClass.{u, u} K r.succPNat}
    {π' : Correspondence.AutomorphicClass.{u, u} K t.succPNat}
    {η : Correspondence.QuasiCharacter K} {d : ℂ[X] × ℂ[X] × (ℂˣ × ℤ)}
    (hd : Correspondence.IsTwistedPairData K ψ ν π π' η d)
    {πη : Correspondence.AutomorphicClass.{u, u} K r.succPNat}
    (hπη : Correspondence.IsCharacterTwist K η π πη) {G : RatFunc ℂ}
    (hG : Correspondence.IsAutomorphicPairGammaFactor K ψ ν πη π' G) :
    MeromorphicEq (pairDataFactors K.canonicalTopologicalData.residueCardinality d).gamma
      (LocalFactor.rationalSpectralValue K.canonicalTopologicalData.residueCardinality G) := by
  obtain ⟨πη₀, πd, πd', htw, hdual, hdual', hP, hPd, he⟩ := hd
  obtain rfl : πη₀ = πη := htw.unique hπη
  have hGeq : G = RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K)
      d.2.2.1 d.2.2.2 d.1 d.2.1 :=
    hG.unique (Correspondence.automorphicPairGammaFactor hdual hdual' hP hPd he).property
  have hPd0 : d.2.1 ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hL⟩ := hPd
    exact hL.ne_zero
  rw [hGeq, pairDataFactors_gamma]
  intro s
  exact (RankinSelberg.rationalSpectralValue_eventuallyEq_polynomialGammaExpression _
    K.canonicalTopologicalData.residueCardinality_gt_one _ _
    (LocalFactor.coe_residueReflection K) _ _ _ hPd0 s).symm

/-- The gamma factor of arithmetic local factors is germ-equal to the rational spectral value
of every arithmetic pair gamma factor of the pair. -/
theorem meromorphicEq_arithmeticLocalFactors_gamma
    {eC : LocalFactor.CommonClosure.ReciprocityFamily K}
    {ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K}
    {hε : LocalFactor.NonabelianSystem.IsSystem K eC ε}
    {ψ : Correspondence.NontrivialAdditiveCharacter K}
    {B B' : Weil.Local.LocalWeilDeligneRepresentation.{u, uV} K} {f : LocalFactors}
    (hf : IsArithmeticPairLocalFactors.{u, uV, uE} K eC ε hε ψ
      (WeilDeligneRepresentation.classOf B) (WeilDeligneRepresentation.classOf B')
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf B))
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf B')) f)
    {G : RatFunc ℂ} (hG : Correspondence.IsArithmeticPairGammaFactor K eC ε hε ψ
      (WeilDeligneRepresentation.classOf B) (WeilDeligneRepresentation.classOf B') G) :
    MeromorphicEq f.gamma
      (LocalFactor.rationalSpectralValue K.canonicalTopologicalData.residueCardinality G) := by
  obtain ⟨hL, hLd, c₀, m₀, he₀, hεf⟩ := hf
  obtain ⟨c₁, m₁, he₁, rfl⟩ := hG
  obtain ⟨rfl, rfl⟩ := Correspondence.IsArithmeticPairEpsilonFactor.unique K he₁ he₀
  set q := K.canonicalTopologicalData.residueCardinality
  set I := Weil.Local.localInertia K
  set g := Weil.Local.localGeometricFrobenius K
  set T := WeilDeligneRepresentation.tensor B B'
  set P := LocalFactor.WeilDeligne.eulerPolynomial T I g with hP_def
  set Pd := LocalFactor.WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual T) I g
    with hPd_def
  have hLeq : ∀ s, f.lFactor s = RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s)
      ((algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) := hL
  have hLdeq : ∀ s, f.dualLFactor s = RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint q s) ((algebraMap ℂ[X] (RatFunc ℂ) Pd)⁻¹) := by
    intro s
    rw [hLd s]
    congr 1
    change LocalFactor.WeilDeligne.rationalLFactor
        (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.dual B)
          (WeilDeligneRepresentation.dual B')) I g =
      LocalFactor.WeilDeligne.rationalLFactor (WeilDeligneRepresentation.dual T) I g
    exact LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv I
      (WeilDeligneRepresentation.tensorDualEquiv B B') g
  have hPdne : Pd ≠ 0 := fun h => by
    have := LocalFactor.WeilDeligne.eulerPolynomial_coeff_zero
      (WeilDeligneRepresentation.dual T) I g
    rw [← hPd_def, h, Polynomial.coeff_zero] at this
    exact zero_ne_one this
  have hH : ((RankinSelberg.rationalEpsilonMonomial c₁ m₁ : RankinSelberg.RationalFunctions) *
      LocalFactor.WeilDeligne.rationalLRatioClass I g (LocalFactor.residueReflection K)
        (WeilDeligneRepresentation.tensorClass (WeilDeligneRepresentation.classOf B)
          (WeilDeligneRepresentation.classOf B'))) =
      RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K) c₁ m₁ P Pd := by
    change _ * LocalFactor.WeilDeligne.rationalLRatio T I g _ = _
    rw [LocalFactor.WeilDeligne.rationalLRatio_eq, RankinSelberg.rationalGammaExpression,
      mul_div_assoc]
  have hfun : f.gamma = RankinSelberg.polynomialGammaExpression q c₁ m₁ P Pd := by
    funext s
    change f.epsilonFactor s * f.dualLFactor (1 - s) / f.lFactor s = _
    rw [hεf s, hLeq s, hLdeq (1 - s), eval_inv_algebraMap_total, eval_inv_algebraMap_total]
    rfl
  rw [hH, hfun]
  intro s
  exact (RankinSelberg.rationalSpectralValue_eventuallyEq_polynomialGammaExpression _
    K.canonicalTopologicalData.residueCardinality_gt_one _ _
    (LocalFactor.coe_residueReflection K) _ _ _ hPdne s).symm

end Local

/-- **Local gamma comparison** of the two families at a finite place `z`, from a pair gamma
match of the twisted local classes. -/
theorem meromorphicEq_gamma_of_isPairGammaMatch
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (arch : NumberField.InfinitePlace F → LocalFactors) (χ : HeckeCharacter F)
    (z : FinitePlace F) (hadd : A.additive z = D.additive z)
    {πη : Correspondence.AutomorphicClass.{u, u} (padicField z) r.succPNat}
    (htw : Correspondence.IsCharacterTwist (padicField z)
      (quasicharacterBase z (χ.finiteComponent z)) (localClass D.P D.h z) πη)
    (hmatch : IsPairGammaMatch.{u, uV, uE} (padicField z) (A.family z) (A.system z)
      (A.system_spec z) (D.additive z) πη (localClass D.P' D.h' z)
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
        (A.localMap z))
      (localPairClass S' (A.localMap z))) :
    MeromorphicEq (D.localFactors χ (.inr z)).gamma (A.localFactors arch χ (.inr z)).gamma := by
  obtain ⟨-, hall⟩ := hmatch
  obtain ⟨G, hGa, hGr⟩ := hall (D.measure z) (D.measure_spec z)
  have hD := meromorphicEq_pairDataFactors_gamma
    (Correspondence.twistedPairData_spec (D.additive z) (D.measure_spec z) _ _ _) htw hGa
  have hfs := A.finiteFactors_spec hEps χ z
  rw [hadd, localPairClass_dual, localPairClass_dual] at hfs
  have hA := meromorphicEq_arithmeticLocalFactors_gamma hfs hGr
  intro s
  exact (hD s).trans (hA s).symm

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
