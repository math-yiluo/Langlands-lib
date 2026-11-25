import Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor

/-! # Conditional proof of the unequal-rank semi-local functional equation

`unequalSemilocalEquation_of_factorization` proves `UnequalSemilocalEquationStatement`
from the retained premise `UnequalSemilocalFactorizationStatement`: Cogdell 2004, proof of
Theorem 4.1, pp.219–220. The local functional equations at the places of `S` (Theorem 3.2,
p.214) come from the Library: the gamma factor of the generic local components and its
defining functional equation. See the paired Markdown.
-/

noncomputable section
universe u uQ uF uV uW
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace UnequalSemilocalReduction

open Langlands.RankinSelberg

/-- `s ↦ R(q^(-s))` is meromorphic on `ℂ`. -/
theorem meromorphicOn_eval_spectralPoint {q : ℕ} (hq : 1 < q) (R : RationalFunctions) :
    MeromorphicOn (fun s => RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) Set.univ := by
  intro s _
  have h := (analyticAt_polynomial_spectralPoint q hq R.num s).meromorphicAt.div
    (analyticAt_polynomial_spectralPoint q hq R.denom s).meromorphicAt
  have he : (fun s => RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) =
      (fun z => R.num.eval (spectralPoint q z)) / fun z => R.denom.eval (spectralPoint q z) := by
    funext z
    simp only [RatFunc.eval, Polynomial.eval₂_id, Pi.div_apply]
  rw [he]
  exact h

/-- The denominator of `R` does not vanish at `q^(-s)` off a discrete set. -/
theorem eventually_denom_ne_zero {q : ℕ} (hq : 1 < q) (R : RationalFunctions) :
    ∀ᶠ s in Filter.codiscrete ℂ, R.denom.eval (spectralPoint q s) ≠ 0 := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  exact polynomial_spectralPoint_eventually_ne_zero q hq _ (RatFunc.denom_ne_zero R) x

/-- The denominator of `R` does not vanish at `q^(-(1-s))` off a discrete set. -/
theorem eventually_denom_reflected_ne_zero {q : ℕ} (hq : 1 < q) (R : RationalFunctions) :
    ∀ᶠ s in Filter.codiscrete ℂ, R.denom.eval (spectralPoint q (1 - s)) ≠ 0 := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  exact polynomial_reflected_spectralPoint_eventually_ne_zero q hq _ (RatFunc.denom_ne_zero R) x

/-- A nonzero `R` has `R(q^(-s)) ≠ 0` off a discrete set. -/
theorem eventually_eval_ne_zero {q : ℕ} (hq : 1 < q) {R : RationalFunctions} (hR : R ≠ 0) :
    ∀ᶠ s in Filter.codiscrete ℂ, RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R ≠ 0 := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro x
  filter_upwards [polynomial_spectralPoint_eventually_ne_zero q hq _ (RatFunc.num_ne_zero hR) x,
    polynomial_spectralPoint_eventually_ne_zero q hq _ (RatFunc.denom_ne_zero R) x]
    with s h1 h2
  simp only [RatFunc.eval, Polynomial.eval₂_id]
  exact div_ne_zero h1 h2

/-- A nonzero gamma factor and a nonzero continuation force a nonzero dual continuation. -/
theorem rdual_ne_zero {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ} {G R Rdual : RationalFunctions}
    (hG : G ≠ 0) (hR : R ≠ 0) (h : GammaFunctionalEquation q ζ e G R Rdual) : Rdual ≠ 0 := by
  rintro rfl
  apply hG
  refine GammaFunctionalEquation.gamma_unique hq hR h ?_
  intro s _ _ _
  simp only [RatFunc.eval_zero, zero_mul, mul_zero]

/-- Two canonical finite components of `ψ` at the same place agree. -/
theorem canonicalFiniteAdditiveComponent_unique {F : Type u} [Field F] [NumberField F]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {v : FinitePlace F}
    {ψv ψv' : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    (h : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h' : IsCanonicalFiniteAdditiveComponent ψ v ψv') : ψv = ψv' := by
  rcases ψv with ⟨χ, hc, hn⟩
  rcases ψv' with ⟨χ', hc', hn'⟩
  have hχ : χ = χ' := DFunLike.ext χ χ' fun x => (h x).trans (h' x).symm
  subst hχ
  rfl

section Local

open HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p}
  {ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W}

/-- A gamma factor of `(π, σ)` gives the block-zero functional equation of the chosen test
data: the minus-one scalar, the rational continuations of the block-zero integral and of
its transformed integral, and the gamma functional equation relating them. -/
theorem PadicUnequalTestData.exists_gammaEquation (h : t < r)
    {ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
      AdditiveHaarMeasure K.Carrier}
    {G : RationalFunctions} (D : PadicUnequalTestData K ψ π σ)
    (hG : IsPadicPairGammaFactor K ψ ν π σ G) :
    ∃ ζ : ℂˣ, D.HasMinusOneScalar ζ ∧ ∃ R Rdual : RationalFunctions,
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality
        (D.integral h ν) R ∧
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality
        (D.dualIntegral h ν) Rdual ∧
      GammaFunctionalEquation K.canonicalTopologicalData.residueCardinality ζ r G R Rdual := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) K.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t K.Carrier)
  unfold IsPadicPairGammaFactor IsPairGammaFactor at hG
  rw [dite_eq_left_of_eq_true (eq_true h)] at hG
  let := D.invariant
  obtain ⟨ζ, hζ, hblocks⟩ := hG.2.2.2 D.measure D.compatible D.functional D.inverseFunctional
    D.functional_ne_zero D.inverseFunctional_ne_zero
  obtain ⟨R, Rdual, hR, hRdual, hFE⟩ :=
    (hblocks 0 (r - t - 1) (by omega)).2 D.vector D.inverseVector
  exact ⟨ζ, hζ, R, Rdual, hR, hRdual, hFE⟩

end Local

end UnequalSemilocalReduction

open UnequalSemilocalReduction

local instance unequalSemilocalReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalSemilocalReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, proof of Theorem 4.1, pp.219–220** (conditional): the factorization and
archimedean premise `UnequalSemilocalFactorizationStatement`, with the Library's local
gamma factors of the generic local components, implies the semi-local functional equation
`UnequalSemilocalEquationStatement`. -/
theorem unequalSemilocalEquation_of_factorization
    (hFac : UnequalSemilocalFactorizationStatement.{u, uQ}) :
    UnequalSemilocalEquationStatement.{u, uQ} := by
  classical
  intro F _ _ _ ψ hdiag r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hψS aR haR aC haC
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


/-- **Conditional reduction** (Cogdell 2004, proof of Theorem 4.1, pp.219–220): the retained
premise `UnequalSemilocalFactorizationStatement` implies the semi-local functional equation
`UnequalSemilocalEquationStatement`. Proved below by
`unequalSemilocalEquationReduction`. -/
def UnequalSemilocalEquationReductionStatement : Prop :=
  UnequalSemilocalFactorizationStatement.{u, uQ} → UnequalSemilocalEquationStatement.{u, uQ}

/-- Proof of `UnequalSemilocalEquationReductionStatement`. -/
theorem unequalSemilocalEquationReduction :
    UnequalSemilocalEquationReductionStatement.{u, uQ} :=
  unequalSemilocalEquation_of_factorization

end Langlands.Global.RankinSelbergGlobal
