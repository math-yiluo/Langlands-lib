import Langlands.LocalFactor.UnitaryRationalGamma
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Automorphic.AssociatedFactorStatement

/-! # Punctured spectral germs of certified automorphic gamma factors -/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.RankinSelberg

open Polynomial LocalFactor

/-- The epsilon times reflected reciprocal L-polynomial over reciprocal
L-polynomial expression, as an actual function of the spectral variable. -/
def polynomialGammaExpression (q : ℕ) (c : ℂˣ) (m : ℤ) (P Pd : ℂ[X]) : ℂ → ℂ :=
  fun s => epsilonMonomial q c m s *
    (Pd.eval (spectralPoint q (1 - s)))⁻¹ / (P.eval (spectralPoint q s))⁻¹

theorem analyticAt_polynomial_spectralPoint (q : ℕ) (hq : 1 < q)
    (P : ℂ[X]) (s : ℂ) :
    AnalyticAt ℂ (fun z => P.eval (spectralPoint q z)) s := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have he : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (-z * (Real.log (q : ℝ) : ℂ))) s :=
    (analyticAt_id.neg.mul analyticAt_const).cexp
  simp_rw [spectralPoint_eq_spectralParameter q hq0]
  change AnalyticAt ℂ
    (fun z : ℂ => P.eval (Complex.exp (-z * (Real.log (q : ℝ) : ℂ)))) s
  simpa [Polynomial.aeval_def] using he.aeval_polynomial P

/-- A nonzero polynomial stays nonzero on a sufficiently small punctured
spectral neighborhood, including around one of its zeros. -/
theorem polynomial_spectralPoint_eventually_ne_zero (q : ℕ) (hq : 1 < q)
    (P : ℂ[X]) (hP : P ≠ 0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, P.eval (spectralPoint q z) ≠ 0 := by
  let D : ReciprocalEntire := {
    denominator := fun z => P.eval (spectralPoint q z)
    entire := fun z => (analyticAt_polynomial_spectralPoint q hq P z).differentiableAt
    nonzero := by
      obtain ⟨t, ht⟩ := (finite_spectralPoint_roots hq hP).exists_notMem
      exact ⟨(t : ℂ), ht⟩ }
  exact D.denominator_eventually_ne_zero s

theorem polynomial_reflected_spectralPoint_eventually_ne_zero (q : ℕ) (hq : 1 < q)
    (P : ℂ[X]) (hP : P ≠ 0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, P.eval (spectralPoint q (1 - z)) ≠ 0 := by
  let D : ReciprocalEntire := {
    denominator := fun z => P.eval (spectralPoint q (1 - z))
    entire := fun z =>
      ((analyticAt_polynomial_spectralPoint q hq P (1 - z)).comp
        (analyticAt_const.sub analyticAt_id)).differentiableAt
    nonzero := by
      obtain ⟨t, ht⟩ := (finite_reflected_spectralPoint_roots hq hP).exists_notMem
      exact ⟨(t : ℂ), ht⟩ }
  exact D.denominator_eventually_ne_zero s

/-- The displayed expression is meromorphic at every complex point, including
at zeros of either reciprocal L-polynomial. -/
theorem meromorphicAt_polynomialGammaExpression (q : ℕ) (hq : 1 < q)
    (c : ℂˣ) (m : ℤ) (P Pd : ℂ[X]) (s : ℂ) :
    MeromorphicAt (polynomialGammaExpression q c m P Pd) s := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hP := (analyticAt_polynomial_spectralPoint q hq P s).meromorphicAt
  have hPd := ((analyticAt_polynomial_spectralPoint q hq Pd (1 - s)).comp
    (analyticAt_const.sub analyticAt_id)).meromorphicAt
  exact ((epsilonMonomial_analyticAt q hq0 c m s).meromorphicAt.mul hPd.inv).div hP.inv

/-- Rational evaluation has the intended gamma germ at every complex point.
The equality is punctured, so cancelled zeros and displayed poles are retained. -/
theorem rationalSpectralValue_eventuallyEq_polynomialGammaExpression
    (q : ℕ) (hq : 1 < q) (δ c : ℂˣ)
    (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (m : ℤ) (P Pd : ℂ[X])
    (hPd : Pd ≠ 0) (s : ℂ) :
    rationalSpectralValue q (rationalGammaExpression δ c m P Pd) =ᶠ[𝓝[≠] s]
      polynomialGammaExpression q c m P Pd := by
  filter_upwards [polynomial_reflected_spectralPoint_eventually_ne_zero
    q hq Pd hPd s] with z hz
  have href : (δ : ℂ) / spectralPoint q z = spectralPoint q (1 - z) := by
    rw [hδ, spectralPoint_one_sub hq]
  have heval := eval_rationalGammaExpression δ c m P Pd
    (spectralPoint_ne_zero hq z) (by rwa [href])
  change RatFunc.eval (RingHom.id ℂ) (spectralPoint q z)
    (rationalGammaExpression δ c m P Pd) = _
  rw [heval, href]
  simp only [polynomialGammaExpression, epsilonMonomial, div_eq_mul_inv, inv_inv]
  ring

end Langlands.RankinSelberg

namespace Langlands.Correspondence

universe uF uA

open LocalFactor RankinSelberg Polynomial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : NontrivialAdditiveCharacter F} {ν : LocalAdditiveHaarMeasure F}
  {r t : ℕ}
  {π πd : AutomorphicClass.{uF, uA} F r.succPNat}
  {π' πd' : AutomorphicClass.{uF, uA} F t.succPNat}
  {P Pd : ℂ[X]} {e : ℂˣ × ℤ} {G : RatFunc ℂ}

/-- Any supplied dual, L and epsilon certificates give the same rational
expression as the existential witnesses in a gamma certificate. -/
theorem IsAutomorphicPairGammaFactor.eq_rationalGammaExpression
    (hG : IsAutomorphicPairGammaFactor F ψ ν π π' G)
    (hd : IsSmoothDual F π πd) (hd' : IsSmoothDual F π' πd')
    (hP : IsAutomorphicPairLPolynomial F ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor F ψ ν π π' e) :
    G = rationalGammaExpression (residueReflection F) e.1 e.2 P Pd := by
  obtain ⟨δ, δ', Q, Qd, f, hδ, hδ', hQ, hQd, hf, hG⟩ := hG
  have hδeq : δ = πd :=
    ((isSmoothDual_iff_eq_contragredient F π δ).mp hδ).trans
      ((isSmoothDual_iff_eq_contragredient F π πd).mp hd).symm
  have hδ'eq : δ' = πd' :=
    ((isSmoothDual_iff_eq_contragredient F π' δ').mp hδ').trans
      ((isSmoothDual_iff_eq_contragredient F π' πd').mp hd').symm
  subst δ
  subst δ'
  simpa only [hQ.unique hP, hQd.unique hPd, hf.unique he] using hG

/-- Certified automorphic gamma factors have the punctured spectral germ
computed from any supplied genuine dual and factor certificates. -/
theorem IsAutomorphicPairGammaFactor.rationalSpectralValue_eventuallyEq
    (hG : IsAutomorphicPairGammaFactor F ψ ν π π' G)
    (hd : IsSmoothDual F π πd) (hd' : IsSmoothDual F π' πd')
    (hP : IsAutomorphicPairLPolynomial F ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor F ψ ν π π' e) (s : ℂ) :
    rationalSpectralValue F.canonicalTopologicalData.residueCardinality G =ᶠ[𝓝[≠] s]
      polynomialGammaExpression F.canonicalTopologicalData.residueCardinality
        e.1 e.2 P Pd := by
  rw [hG.eq_rationalGammaExpression hd hd' hP hPd he]
  exact rationalSpectralValue_eventuallyEq_polynomialGammaExpression
    F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one
    (residueReflection F) e.1 (coe_residueReflection F) e.2 P Pd hPd.ne_zero s

end Langlands.Correspondence

namespace Langlands.ClassField.Global.RelativeWeilGroup

universe u uV uE

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Correspondence LocalFactor LocalFactor.CommonClosure RankinSelberg Polynomial Weil.Local

section Local

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}
  {eC : ReciprocityFamily K} {ε : NonabelianSystem.Assignment.{u, uE} K}
  {hε : NonabelianSystem.IsSystem K eC ε} {ψ : NontrivialAdditiveCharacter K}
  {ν : LocalAdditiveHaarMeasure K} {r t : ℕ}
  {π πd : AutomorphicClass.{u, u} K r.succPNat}
  {π' πd' : AutomorphicClass.{u, u} K t.succPNat}
  {A B : LocalWeilDeligneRepresentation.{u, uV} K}
  {P Pd : ℂ[X]} {e : ℂˣ × ℤ}

/-- A supplied pair gamma match transfers the unitary arithmetic order bound
to the displayed automorphic expression, at every point off the imaginary axis. -/
theorem IsPairGammaMatch.polynomialGammaExpression_order_nonpos
    (hmatch : IsPairGammaMatch K eC ε hε ψ π π'
      (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B))
    (hν : IsSelfDualMeasure K ψ ν)
    (hd : IsSmoothDual K π πd) (hd' : IsSmoothDual K π' πd')
    (hP : IsAutomorphicPairLPolynomial K ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial K ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor K ψ ν π π' e)
    (hA : A.toFiniteRepresentation.IsUnitary) (hB : B.toFiniteRepresentation.IsUnitary)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (polynomialGammaExpression K.canonicalTopologicalData.residueCardinality
        e.1 e.2 P Pd) s ≤ 0 := by
  obtain ⟨G, hGa, hGw⟩ := hmatch.2 ν hν
  rw [← meromorphicOrderAt_congr
    (hGa.rationalSpectralValue_eventuallyEq hd hd' hP hPd he s)]
  exact hGw.order_nonpos_of_isUnitary hA hB s hs

end Local

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- A self-pair gamma match for a unitary relative Weil representation rules
out positive automorphic orders away from the imaginary axis. -/
theorem localSelfPair_polynomialGammaExpression_order_nonpos
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)}
    {ν : LocalAdditiveHaarMeasure (padicField v)} {r t : ℕ}
    {π πd : AutomorphicClass.{u, u} (padicField v) r.succPNat}
    {π' πd' : AutomorphicClass.{u, u} (padicField v) t.succPNat}
    {P Pd : ℂ[X]} {e : ℂˣ × ℤ}
    (hmatch : IsPairGammaMatch (padicField v) eC ε hε ψ π π'
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι))
    (hν : IsSelfDualMeasure (padicField v) ψ ν)
    (hd : IsSmoothDual (padicField v) π πd) (hd' : IsSmoothDual (padicField v) π' πd')
    (hP : IsAutomorphicPairLPolynomial (padicField v) ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial (padicField v) ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor (padicField v) ψ ν π π' e)
    (s : ℂ) (hs : s.re ≠ 0) :
    meromorphicOrderAt
      (polynomialGammaExpression (padicField v).canonicalTopologicalData.residueCardinality
        e.1 e.2 P Pd) s ≤ 0 :=
  hmatch.polynomialGammaExpression_order_nonpos hν hd hd' hP hPd he
    (localComponent_isUnitary ι hS)
    (localComponent_isUnitary ι (FiniteRepresentation.isUnitary_dual S hS)) s hs

/-- The real positive-order constraint needed by pole counting follows from
the actual self-pair match and any supplied automorphic factor certificates. -/
theorem localSelfPair_polynomialGammaExpression_real_positive_order_only_zero
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {eC : ReciprocityFamily (padicField v)}
    {ε : NonabelianSystem.Assignment.{u, uE} (padicField v)}
    {hε : NonabelianSystem.IsSystem (padicField v) eC ε}
    {ψ : NontrivialAdditiveCharacter (padicField v)}
    {ν : LocalAdditiveHaarMeasure (padicField v)} {r t : ℕ}
    {π πd : AutomorphicClass.{u, u} (padicField v) r.succPNat}
    {π' πd' : AutomorphicClass.{u, u} (padicField v) t.succPNat}
    {P Pd : ℂ[X]} {e : ℂˣ × ℤ}
    (hmatch : IsPairGammaMatch (padicField v) eC ε hε ψ π π'
      (localPairClass S ι) (localPairClass (FiniteRepresentation.dual S) ι))
    (hν : IsSelfDualMeasure (padicField v) ψ ν)
    (hd : IsSmoothDual (padicField v) π πd) (hd' : IsSmoothDual (padicField v) π' πd')
    (hP : IsAutomorphicPairLPolynomial (padicField v) ψ ν π π' P)
    (hPd : IsAutomorphicPairLPolynomial (padicField v) ψ ν πd πd' Pd)
    (he : IsAutomorphicPairEpsilonFactor (padicField v) ψ ν π π' e)
    (t₀ : ℝ)
    (ht₀ : 0 < meromorphicOrderAt
      (polynomialGammaExpression (padicField v).canonicalTopologicalData.residueCardinality
        e.1 e.2 P Pd) (t₀ : ℂ)) :
    t₀ = 0 := by
  by_contra ht
  exact (not_lt_of_ge
    (localSelfPair_polynomialGammaExpression_order_nonpos
      ι hS hmatch hν hd hd' hP hPd he t₀ (by simpa using ht))) ht₀

end Langlands.ClassField.Global.RelativeWeilGroup
