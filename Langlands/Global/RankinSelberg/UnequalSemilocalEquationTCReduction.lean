import Langlands.Global.RankinSelberg.UnequalSemilocalEquationReduction
import Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationTCStatement
import Langlands.Global.RankinSelberg.SemilocalEquationTCStatements

/-! # Conditional proof of the unequal-rank semi-local functional equation, totally complex fields

`unequalSemilocalEquationTC_of_factorizationTC` proves `UnequalSemilocalEquationTCStatement`
from the retained premise `UnequalSemilocalFactorizationTCStatement`: Cogdell 2004, proof of
Theorem 4.1, pp.219–220. The argument is that of `unequalSemilocalEquation_of_factorization`
(module `Langlands.Global.RankinSelberg.UnequalSemilocalEquationReduction`), with the premise
applied at the same totally complex field. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open UnequalSemilocalReduction

local instance unequalSemilocalTCReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalSemilocalTCReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, proof of Theorem 4.1, pp.219–220** (conditional, totally complex
fields): the premise `UnequalSemilocalFactorizationTCStatement`, with the Library's local
gamma factors of the generic local components, implies `UnequalSemilocalEquationTCStatement`.
The premise is used only at the given totally complex field. -/
theorem unequalSemilocalEquationTC_of_factorizationTC
    (hFac : UnequalSemilocalFactorizationTCStatement.{u, uQ}) :
    UnequalSemilocalEquationTCStatement.{u, uQ} := by
  classical
  intro F _ _ _ _ ψ hdiag r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hψS aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  -- the canonical additive components and self-dual measures
  let ψ0 : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v) :=
    fun v => canonicalFiniteAdditiveComponent ψ hdiag v
  have hψ0 : ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψ0 v) := fun v =>
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hdiag v
  let ν0 : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v) :=
    fun v => Correspondence.localSelfDualHaar (padicField v) (ψ0 v)
  have hν0 : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψ0 v) (ν0 v) := fun v =>
    Correspondence.isSelfDual_localSelfDualHaar (padicField v) (ψ0 v)
  have hq : ∀ v : FinitePlace F, 1 < residueCardinality v := fun v =>
    (padicField v).canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨x, x', hx, hx', hrest⟩ := hFac F ψ hdiag r t h T Td T' Td' hTd hTd' P P' hI hI' S
    hPS hP'S hψS aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd' ψ0 hψ0 ν0 hν0
  obtain ⟨σ0, Ainf, Binf, D, hAm, hBm, hA0, hB0, hcont, hfacA, hfacB, hsign⟩ := hrest
  -- the local gamma factors of the generic local components
  have hG0 : ∀ v : S, ∃ G : RankinSelberg.RationalFunctions, G ≠ 0 ∧
      letI := (padicField v.1).canonicalTopologicalData.topology
      letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
      letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
      RankinSelberg.IsPadicPairGammaFactor (padicField v.1) (ψ0 v.1) (ν0 v.1)
        ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
        ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation G := by
    intro v
    let := (padicField v.1).canonicalTopologicalData.topology
    let := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
    let := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
    have hπ := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F r T P v.1
      (hI v.1).1 (hI v.1).2 (ψ0 v.1)
    have hσ := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, uQ} F t T' P' v.1
      (hI' v.1).1 (hI' v.1).2 (ψ0 v.1)
    exact ⟨_, Units.ne_zero _,
      RankinSelberg.genericPairGammaFactor_isPadic (padicField v.1) h.le (ψ0 v.1) (ν0 v.1)
        (hν0 v.1) _ _ hπ hσ⟩
  choose G0 hG0ne hG0 using hG0
  choose R hRne hRc using hcont
  have hloc := fun v : S => PadicUnequalTestData.exists_gammaEquation h (D v) (hG0 v)
  choose ζ0 hζ0 R' Rd hR' hRd hFE0 using hloc
  have hRR' : ∀ v : S, R' v = R v := fun v => (hR' v).unique (hq v.1) (hRc v)
  have hRdne : ∀ v : S, Rd v ≠ 0 := fun v =>
    rdual_ne_zero (hq v.1) (hG0ne v) (hRne v) (hRR' v ▸ hFE0 v)
  -- half-planes of the continuations
  choose a ha using hRc
  choose ad had using hRd
  obtain ⟨M, hM⟩ := Finite.exists_le (fun v : S => max (a v) (ad v))
  intro infiniteL dualInfiniteL infiniteEpsilon
  refine ⟨x, x', hx, hx', ?_⟩
  intro W W' Wdual W'dual
  refine ⟨max σ0 M,
    fun s => Ainf s * ∏ v : S, RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint (residueCardinality v.1) s) (R v),
    fun s => Binf s * ∏ v : S, RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint (residueCardinality v.1) s) (Rd v), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAm.mul (MeromorphicOn.fun_prod fun v _ =>
      meromorphicOn_eval_spectralPoint (hq v.1) (R v))
  · exact hBm.mul (MeromorphicOn.fun_prod fun v _ =>
      meromorphicOn_eval_spectralPoint (hq v.1) (Rd v))
  · intro s hs
    have hs0 : σ0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    rw [hfacA s hs0]
    beta_reduce
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    have hav : a v < s.re :=
      lt_of_le_of_lt ((le_max_left _ _).trans ((hM v).trans (le_max_right _ _))) hs
    exact ((ha v s hav).2).symm
  · intro s hs
    have hs0 : σ0 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    rw [hfacB s hs0]
    beta_reduce
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    have hav : ad v < s.re :=
      lt_of_le_of_lt ((le_max_right _ _).trans ((hM v).trans (le_max_right _ _))) hs
    exact ((had v s hav).2).symm
  · have hall : ∀ᶠ s in Filter.codiscrete ℂ, ∀ v : S,
        RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) s) (R v) ≠ 0 :=
      Filter.eventually_all.mpr fun v => eventually_eval_ne_zero (hq v.1) (hRne v)
    filter_upwards [hA0, hall] with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.mpr fun v _ => h2 v)
  · have hall : ∀ᶠ s in Filter.codiscrete ℂ, ∀ v : S,
        RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) s) (Rd v) ≠ 0 :=
      Filter.eventually_all.mpr fun v => eventually_eval_ne_zero (hq v.1) (hRdne v)
    filter_upwards [hB0, hall] with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.mpr fun v _ => h2 v)
  · intro ψv hψv νv hνv G hG
    have hψeq : ψv = ψ0 := funext fun v =>
      canonicalFiniteAdditiveComponent_unique (hψv v) (hψ0 v)
    subst hψeq
    have hνeq : νv = ν0 := funext fun v =>
      Correspondence.eq_localSelfDualHaar (padicField v) (ψ0 v) (νv v) (hνv v)
    subst hνeq
    -- the local functional equations for the given gamma factors
    have hGv : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicPairGammaFactor (padicField v.1) (ψ0 v.1) (ν0 v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation
          (G v.1) := fun v =>
      (RankinSelberg.isPadicSymmetricGammaFactor_of_le h.le).mp (hG v.1 v.2)
    have hloc := fun v : S => PadicUnequalTestData.exists_gammaEquation h (D v) (hGv v)
    choose ζ hζ R'' Rd'' hR'' hRd'' hFE using hloc
    have hR'' : ∀ v : S, R'' v = R v := fun v =>
      (hR'' v).unique (hq v.1) ⟨a v, ha v⟩
    have hRd'' : ∀ v : S, Rd'' v = Rd v := fun v =>
      (hRd'' v).unique (hq v.1) ⟨ad v, had v⟩
    have hev : ∀ᶠ s in Filter.codiscrete ℂ, ∀ v : S,
        (R v).denom.eval (RankinSelberg.spectralPoint (residueCardinality v.1) s) ≠ 0 ∧
        (Rd v).denom.eval (RankinSelberg.spectralPoint (residueCardinality v.1) (1 - s)) ≠ 0 ∧
        (G v.1).denom.eval (RankinSelberg.spectralPoint (residueCardinality v.1) s) ≠ 0 :=
      Filter.eventually_all.mpr fun v =>
        ((eventually_denom_ne_zero (hq v.1) (R v)).and
          ((eventually_denom_reflected_ne_zero (hq v.1) (Rd v)).and
            (eventually_denom_ne_zero (hq v.1) (G v.1))))
    filter_upwards [hsign ζ hζ, hev] with s hs hd
    have hloc : ∀ v : S,
        RatFunc.eval (RingHom.id ℂ)
            (RankinSelberg.spectralPoint (residueCardinality v.1) (1 - s)) (Rd v) =
          (ζ v : ℂ) ^ r *
            (RatFunc.eval (RingHom.id ℂ)
                (RankinSelberg.spectralPoint (residueCardinality v.1) s) (G v.1) *
              RatFunc.eval (RingHom.id ℂ)
                (RankinSelberg.spectralPoint (residueCardinality v.1) s) (R v)) :=
      fun v => by
        have := hFE v
        rw [hR'' v, hRd'' v] at this
        exact this s (hd v).1 (hd v).2.1 (hd v).2.2
    have hprod :
        (∏ v : S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) (1 - s)) (Rd v)) =
        (∏ v : S, (ζ v : ℂ) ^ r) *
          ((∏ v : S, RatFunc.eval (RingHom.id ℂ)
            (RankinSelberg.spectralPoint (residueCardinality v.1) s) (G v.1)) *
          ∏ v : S, RatFunc.eval (RingHom.id ℂ)
            (RankinSelberg.spectralPoint (residueCardinality v.1) s) (R v)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => hloc v
    have hGS : (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) =
        ∏ v : S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) s) (G v.1) :=
      (Finset.prod_coe_sort S _).symm
    simp only [hGS, infiniteL, dualInfiniteL, infiniteEpsilon]
    rw [hprod]
    linear_combination
      ((∏ v : S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) s) (G v.1)) *
        ∏ v : S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v.1) s) (R v)) * hs

/-- **Conditional reduction, totally complex fields** (Cogdell 2004, proof of Theorem 4.1,
pp.219–220): the retained premise `UnequalSemilocalFactorizationTCStatement` implies
`UnequalSemilocalEquationTCStatement`. Proved below by
`unequalSemilocalEquationTCReduction`. -/
def UnequalSemilocalEquationTCReductionStatement : Prop :=
  UnequalSemilocalFactorizationTCStatement.{u, uQ} → UnequalSemilocalEquationTCStatement.{u, uQ}

/-- Proof of `UnequalSemilocalEquationTCReductionStatement`. -/
theorem unequalSemilocalEquationTCReduction :
    UnequalSemilocalEquationTCReductionStatement.{u, uQ} :=
  unequalSemilocalEquationTC_of_factorizationTC

end Langlands.Global.RankinSelbergGlobal
