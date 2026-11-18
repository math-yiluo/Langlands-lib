import Langlands.Global.RankinSelberg.ArchimedeanDeterminantProducts
import Langlands.Global.RankinSelberg.EqualArchimedeanFactorizationReduction

/-! # Equal-rank integrand products from paired Whittaker products -/

noncomputable section
universe u uK uV uW
open NumberField MeasureTheory Langlands.RankinSelberg Langlands.GeneralLinear
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.EqualIntegrandProducts

section Local

variable {K : Type uK} [Field K] [TopologicalSpace K]

omit [TopologicalSpace K] in
/-- The local complex power convention agrees with the real-logarithm convention. -/
theorem determinantWeight_eq_detPower (abv : AbsoluteValue K ℝ) (n : ℕ)
    (g : Langlands.GeneralLinear n K) (s : ℂ) :
    RankinSelberg.determinantWeight abv g s = ArchimedeanLocal.detPower abv g s := by
  have ha : 0 < abv (Matrix.det g.val) := abv.pos_iff.mpr g.det_ne_zero
  rw [RankinSelberg.determinantWeight,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le, mul_comm]
  rfl

omit [TopologicalSpace K] in
theorem local_detPower_unipotent_mul (nabs : K → ℝ) (r : ℕ)
    (u : Langlands.GeneralLinear.upperUnipotent (r + 1) K)
    (g : Langlands.GeneralLinear (r + 1) K) (s : ℂ) :
    ArchimedeanLocal.detPower nabs (u.val * g) s = ArchimedeanLocal.detPower nabs g s := by
  simp [ArchimedeanLocal.detPower, Matrix.det_mul]

/-- A paired unipotent-invariant Whittaker product makes the local integrand
independent of the representative chosen by the quotient. -/
theorem equalIntegrand_mk_of_pair_invariant (nabs : K → ℝ) (r : ℕ)
    (W W' : Langlands.GeneralLinear (r + 1) K → ℂ)
    (hpair : ∀ (u : Langlands.GeneralLinear.upperUnipotent (r + 1) K) (g : Langlands.GeneralLinear (r + 1) K),
      W (u.val * g) * W' (u.val * g) = W g * W' g)
    (Φ : (Fin (r + 1) → K) → ℂ) (s : ℂ) (g : Langlands.GeneralLinear (r + 1) K) :
    ArchimedeanLocal.equalIntegrand nabs W W' Φ s (Quotient.mk'' g) =
      W g * W' g * Φ (RankinSelberg.lastRow g) * ArchimedeanLocal.detPower nabs g s := by
  let q : LeftUnipotentQuotient r K := Quotient.mk'' g
  have hq : Quotient.mk'' q.out = Quotient.mk'' g := Quotient.out_eq q
  have hu : q.out * g⁻¹ ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) K :=
    (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hq.symm
  let u : Langlands.GeneralLinear.upperUnipotent (r + 1) K := ⟨q.out * g⁻¹, hu⟩
  have he : q.out = u.val * g := by dsimp [u]; group
  change W q.out * W' q.out * Φ (RankinSelberg.lastRow q.out) *
    ArchimedeanLocal.detPower nabs q.out s = _
  rw [he, hpair, RankinSelberg.lastRow_unipotent_mul,
    local_detPower_unipotent_mul]

/-- For actual Whittaker functions the two quotient integrand APIs agree. -/
theorem equalIntegrand_eq_rankinSelberg
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K) (abv : AbsoluteValue K ℝ) (r : ℕ)
    (W : RankinSelberg.WhittakerFunctions ψ r) (W' : RankinSelberg.InverseWhittakerFunctions ψ r)
    (Φ : HarmonicAnalysis.SchwartzBruhat (Fin (r + 1) → K)) (s : ℂ)
    (q : LeftUnipotentQuotient r K) :
    ArchimedeanLocal.equalIntegrand abv W.val W'.val Φ s q =
      RankinSelberg.equalRankIntegrand ψ abv W W' Φ s q := by
  calc
    _ = W.val q.out * W'.val q.out * Φ (RankinSelberg.lastRow q.out) *
        RankinSelberg.determinantWeight abv q.out s := by
      dsimp only [ArchimedeanLocal.equalIntegrand]
      rw [determinantWeight_eq_detPower]
    _ = RankinSelberg.equalRankIntegrand ψ abv W W' Φ s (Quotient.mk'' q.out) :=
      (RankinSelberg.equalRankIntegrand_mk ψ abv W W' Φ s q.out).symm
    _ = _ := congrArg (RankinSelberg.equalRankIntegrand ψ abv W W' Φ s) (Quotient.out_eq q)

/-- Agreement of the actual integrands also identifies their total integrals. -/
theorem equalIntegral_eq_rankinSelberg
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter K) (abv : AbsoluteValue K ℝ) (r : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient r K)] (μ : Measure (LeftUnipotentQuotient r K))
    (W : RankinSelberg.WhittakerFunctions ψ r) (W' : RankinSelberg.InverseWhittakerFunctions ψ r)
    (Φ : HarmonicAnalysis.SchwartzBruhat (Fin (r + 1) → K)) (s : ℂ) :
    ArchimedeanLocal.equalIntegral abv μ W.val W'.val Φ s =
      RankinSelberg.equalRankIntegral ψ abv μ W W' Φ s := by
  unfold ArchimedeanLocal.equalIntegral RankinSelberg.equalRankIntegral
  exact integral_congr_ae (Filter.Eventually.of_forall
    (equalIntegrand_eq_rankinSelberg ψ abv r W W' Φ s))

end Local

variable (F : Type u) [Field F] [NumberField F]

/-- On the partial domain the last row is integral outside `S`. -/
theorem lastRow_mem_integralOutside (r : ℕ) (S : Finset (FinitePlace F))
    (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
    lastRow F r g ∈ integralOutside F (r + 1) S := by
  intro v hv j
  let gv := finiteComponent F (r + 1) v g
  obtain ⟨k, hk, hdiag, hlow⟩ := hg v hv
  have hu : gv * k ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v) := ⟨hlow, hdiag⟩
  let u : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v) := ⟨gv * k, hu⟩
  have he : gv = u.val * k⁻¹ := by dsimp [u]; group
  have hrow : RankinSelberg.lastRow gv = RankinSelberg.lastRow k⁻¹ := by
    rw [he, RankinSelberg.lastRow_unipotent_mul]
  change RankinSelberg.lastRow gv j ∈ v.adicCompletionIntegers F
  rw [hrow]
  exact ((FiniteAdelicGL.mem_localIntegral F (r + 1) v k).mp hk).2 (Fin.last r) j

@[simp] theorem realRowCoordinates_lastRow (r : ℕ)
    (v : {v : InfinitePlace F // v.IsReal}) (g : Points F (r + 1)) :
    realRowCoordinates F (r + 1) v (lastRow F r g) =
      RankinSelberg.lastRow (realComponent F (r + 1) v g) := rfl

@[simp] theorem complexRowCoordinates_lastRow (r : ℕ)
    (w : {v : InfinitePlace F // v.IsComplex}) (g : Points F (r + 1)) :
    complexRowCoordinates F (r + 1) w (lastRow F r g) =
      RankinSelberg.lastRow (complexComponent F (r + 1) w g) := rfl

@[simp] theorem localCoordinates_lastRow (r : ℕ) (v : FinitePlace F)
    (g : Points F (r + 1)) :
    localCoordinates F (r + 1) v (lastRow F r g) =
      RankinSelberg.lastRow (finiteComponent F (r + 1) v g) := rfl

/-- A supplied paired Whittaker product and test product imply the exact
equal-rank integrand product at the local quotient projections. -/
def PairedWhittakerIntegrandProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (S : Finset (FinitePlace F))
    (κ : ℂ) (W W' : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ)
    (WR WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (WC WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (WS WS' : ∀ v : S, FiniteLocalGL F (r + 1) v.1 → ℂ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → (Fin (r + 1) → ℝ) → ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → (Fin (r + 1) → ℂ) → ℂ)
    (ΦS : ∀ v : S, (Fin (r + 1) → FiniteCompletion F v.1) → ℂ),
    (∀ v (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) g,
      WR v (u.val * g) * WR' v (u.val * g) = WR v g * WR' v g) →
    (∀ w (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ) g,
      WC w (u.val * g) * WC' w (u.val * g) = WC w g * WC' w g) →
    (∀ (v : S) (u : Langlands.GeneralLinear.upperUnipotent (r + 1) (FiniteCompletion F v.1)) g,
      WS v (u.val * g) * WS' v (u.val * g) = WS v g * WS' v g) →
    (∀ g ∈ unipotentIntegralOutside F (r + 1) S,
      W g * W' g = κ *
        ((∏ v, WR v (realComponent F (r + 1) v g) * WR' v (realComponent F (r + 1) v g)) *
        (∏ w, WC w (complexComponent F (r + 1) w g) * WC' w (complexComponent F (r + 1) w g)) *
        ∏ v : S, WS v (finiteComponent F (r + 1) v.1 g) *
          WS' v (finiteComponent F (r + 1) v.1 g))) →
    (Φ = (integralOutside F (r + 1) S).indicator fun y =>
      (∏ v, ΦR v (realRowCoordinates F (r + 1) v y)) *
      (∏ w, ΦC w (complexRowCoordinates F (r + 1) w y)) *
      ∏ v : S, ΦS v (localCoordinates F (r + 1) v.1 y)) →
    ∀ (s : ℂ) (q : WhittakerQuotient F (r + 1)),
      q ∈ unipotentIntegralClasses F (r + 1) S →
      equalWhittakerIntegrand F W W' Φ s q = κ *
        ((∏ v, ArchimedeanLocal.realEqualIntegrand (WR v) (WR' v) (ΦR v) s
          (realQuotientProjection F r v q)) *
        (∏ w, ArchimedeanLocal.complexEqualIntegrand (WC w) (WC' w) (ΦC w) s
          (complexQuotientProjection F r w q)) *
        ∏ v : S, ArchimedeanLocal.equalIntegrand
          (RankinSelberg.normalizedAbsoluteValue
            (Langlands.Global.CompletionPadic.padicField v.1).canonicalTopologicalData)
          (WS v) (WS' v) (ΦS v) s (finiteQuotientProjection F r v.1 q))

/-- Product bookkeeping, retaining the genuine Whittaker product as a premise. -/
theorem pairedWhittakerIntegrandProduct : PairedWhittakerIntegrandProductStatement.{u} := by
  intro F _ _ r S κ W W' Φ WR WR' WC WC' WS WS' ΦR ΦC ΦS hR hC hS hW hΦ s q hq
  have hg : q.out ∈ unipotentIntegralOutside F (r + 1) S := hq
  have hrow := lastRow_mem_integralOutside F r S q.out hg
  have heR (v : {v : InfinitePlace F // v.IsReal}) :=
    equalIntegrand_mk_of_pair_invariant ArchimedeanLocal.realNormalizedAbs r
      (WR v) (WR' v) (hR v) (ΦR v) s (realComponent F (r + 1) v q.out)
  have heC (w : {v : InfinitePlace F // v.IsComplex}) :=
    equalIntegrand_mk_of_pair_invariant ArchimedeanLocal.complexNormalizedAbs r
      (WC w) (WC' w) (hC w) (ΦC w) s (complexComponent F (r + 1) w q.out)
  have heS (v : S) :=
    equalIntegrand_mk_of_pair_invariant
      (RankinSelberg.normalizedAbsoluteValue
        (Langlands.Global.CompletionPadic.padicField v.1).canonicalTopologicalData) r
      (WS v) (WS' v) (hS v) (ΦS v) s (finiteComponent F (r + 1) v.1 q.out)
  dsimp only [equalWhittakerIntegrand]
  rw [hW q.out hg, hΦ, Set.indicator_of_mem hrow,
    DeterminantProducts.detPower_product F (r + 1) S q.out hg s]
  simp only [realRowCoordinates_lastRow, complexRowCoordinates_lastRow,
    localCoordinates_lastRow, ArchimedeanLocal.realEqualIntegrand,
    ArchimedeanLocal.complexEqualIntegrand, realQuotientProjection,
    complexQuotientProjection, finiteQuotientProjection]
  simp only [heR, heC, heS, Finset.prod_mul_distrib]
  ring

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel K.Carrier
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := borel _
local instance (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r K.Carrier) := ⟨rfl⟩

variable {ψ : Correspondence.NontrivialAdditiveCharacter K}
  {ν : Correspondence.LocalAdditiveHaarMeasure K} {r : ℕ}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) W}

/-- The finite ordinary local factor integrates to the recorded test-data integral. -/
theorem padic_testData_integral (D : EqualLocalTestData K ψ ν π σ) (s : ℂ) :
    padicQuotientIntegral K (equalPadicQuotientMeasure K r)
      (ArchimedeanLocal.equalIntegrand
        (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData)
        D.f.val.val D.f'.val.val D.Φ s) = D.integral s :=
  equalIntegral_eq_rankinSelberg ψ
    (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData) r
    (unipotentQuotientHaar K.Carrier r) D.f.val D.f'.val D.Φ s

/-- The finite dual local factor integrates to the recorded dual integral. -/
theorem padic_testData_dualIntegral (D : EqualLocalTestData K ψ ν π σ) (s : ℂ) :
    padicQuotientIntegral K (equalPadicQuotientMeasure K r)
      (ArchimedeanLocal.equalIntegrand
        (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData)
        (ArchimedeanLocal.dualFunction (r + 1) D.f.val.val)
        (ArchimedeanLocal.dualFunction (r + 1) D.f'.val.val) D.Φhat s) = D.dualIntegral s :=
  equalIntegral_eq_rankinSelberg (ψ.scale (-1))
    (RankinSelberg.normalizedAbsoluteValue K.canonicalTopologicalData) r
    (unipotentQuotientHaar K.Carrier r)
    (firstDualFunction ψ r D.f.val) (secondDualFunction ψ r D.f'.val) D.Φhat s

end Padic

end Langlands.Global.RankinSelbergGlobal.EqualIntegrandProducts
