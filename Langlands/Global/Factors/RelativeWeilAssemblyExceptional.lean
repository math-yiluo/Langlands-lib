import Langlands.Global.Factors.RelativeWeilAssemblyGlobal
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Exceptional places in the assembly of the relative Weil functional equation

Additive conductors vanish outside a finite set, finite epsilon factors are `1` at unramified
places of conductor zero, and the Hecke Euler factors are nonzero meromorphic and nonzero on a
right half-plane.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

open Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField
open Langlands.Global Langlands.Global.HeckeFunctionalEquation Langlands.Global.AdelicFunctoriality

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- An unramified epsilon factor equal to `1` at `s = 0` and at `s = 1` has additive
conductor zero. -/
theorem additiveConductor_eq_zero_of_epsilon_eq_one
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (μ : LocalFactor.PadicAbelian.BorelMeasure T) (ha : T.multiplicativeConductor χ = 0)
    (h0 : LocalFactor.PadicAbelian.epsilon T χ ψ μ 0 = 1)
    (h1 : LocalFactor.PadicAbelian.epsilon T χ ψ μ 1 = 1) :
    T.additiveConductor ψ = 0 := by
  simp only [LocalFactor.PadicAbelian.epsilon, LocalFactor.PadicAbelian.epsilonAt, ha,
    ite_true] at h0 h1
  set n := T.additiveConductor ψ
  set L : ℝ := Real.log (T.residueCardinality : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast T.residueCardinality_gt_one)
  have hE : Complex.exp ((n : ℂ) * (1 - 0) * (L : ℂ)) = 1 := by
    simp only [sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h1
    linear_combination h0 - Complex.exp ((n : ℂ) * (1 - 0) * (L : ℂ)) * h1
  have hE' : Real.exp ((n : ℝ) * L) = 1 := by
    have : ((Real.exp ((n : ℝ) * L) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_exp]
      simpa using hE
    exact_mod_cast this
  rw [Real.exp_eq_one_iff, mul_eq_zero] at hE'
  rcases hE' with h | h
  · exact_mod_cast h
  · exact absurd h hL.ne'

end Local

section Hecke

variable {K : Type u} [Field K] [NumberField K]

theorem isUnramifiedAt_one (v : FinitePlace K) : (1 : HeckeCharacter K).IsUnramifiedAt v :=
  fun _ _ => rfl

theorem isUnramifiedAt_mul {χ χ' : HeckeCharacter K} {v : FinitePlace K}
    (h : χ.IsUnramifiedAt v) (h' : χ'.IsUnramifiedAt v) : (χ * χ').IsUnramifiedAt v := by
  intro a ha
  change χ.finiteComponent v a * χ'.finiteComponent v a = 1
  rw [h a ha, h' a ha, one_mul]

/-- Two finite additive components of the same adelic character at the same place are equal. -/
theorem eq_of_isFiniteAdditiveComponent
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)} {v : FinitePlace K}
    {ψ₁ ψ₂ : @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology}
    (h₁ : IsFiniteAdditiveComponent ψ v ψ₁) (h₂ : IsFiniteAdditiveComponent ψ v ψ₂) :
    ψ₁ = ψ₂ := by
  have h : ψ₁.toAddChar = ψ₂.toAddChar :=
    DFunLike.ext _ _ fun x => (h₁ x).trans (h₂ x).symm
  cases ψ₁
  cases ψ₂
  cases h
  rfl

/-- A finite epsilon factor of an unramified character that is `1` everywhere has additive
conductor zero. -/
theorem additiveConductor_eq_zero_of_finiteEpsilon (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (v : FinitePlace K) (hχ : χ.IsUnramifiedAt v) (h : ∀ s, finiteEpsilon χ ψf μ v s = 1) :
    (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0 := by
  have h0 := h 0
  have h1 := h 1
  unfold finiteEpsilon at h0 h1
  exact additiveConductor_eq_zero_of_epsilon_eq_one _ (χ.finiteComponent v) (ψf v) _
    (multiplicativeConductor_eq_zero_of_isUnramifiedAt χ v hχ) h0 h1

/-- The finite epsilon factor of a character unramified at `v` is `1` when the additive
conductor at `v` is zero. -/
theorem finiteEpsilon_eq_one (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (v : FinitePlace K) (hχ : χ.IsUnramifiedAt v)
    (hψ : (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0) (s : ℂ) :
    finiteEpsilon χ ψf μ v s = 1 :=
  epsilon_eq_one_of_conductors_eq_zero (CompletionPadic.topologicalData v)
    (χ.finiteComponent v) (ψf v) (μ v) (multiplicativeConductor_eq_zero_of_isUnramifiedAt χ v hχ)
    hψ s

/-- From the Hecke functional equation of the trivial character: the additive conductors of a
family of finite components of `ψ` vanish outside a finite set. -/
theorem exists_finset_additiveConductor_eq_zero
    (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ1 : ∃ x : Adeles K, ψ x ≠ 1) (hψ2 : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S,
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0 := by
  let μ := fun v => Classical.choice (nonempty_selfDualHaar v (ψf v))
  let D : HeckeArchData (1 : HeckeCharacter K) ψ :=
    Classical.choice (nonempty_heckeArchData hH 1 ψ hψ1 hψ2)
  obtain ⟨S, hS, -⟩ := hasGlobalEquation_of_heckeArchData hH 1 ψ hψ1 hψ2 ψf hψf μ D
  exact ⟨S, fun v hv =>
    additiveConductor_eq_zero_of_finiteEpsilon 1 ψf μ v (isUnramifiedAt_one v) (hS v hv)⟩

/-- The finite places at which a family of finite additive characters has nonzero additive
conductor. -/
def nonzeroConductorPlaces
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology) : Set (FinitePlace K) :=
  {v | (CompletionPadic.topologicalData v).additiveConductor (ψf v) ≠ 0}

/-- The places of nonzero additive conductor of a family of finite components of `ψ` form a
finite set. -/
theorem finite_nonzeroConductorPlaces
    (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (hψ1 : ∃ x : Adeles K, ψ x ≠ 1) (hψ2 : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) :
    (nonzeroConductorPlaces ψf).Finite := by
  obtain ⟨S, hS⟩ := exists_finset_additiveConductor_eq_zero hH ψ hψ1 hψ2 ψf hψf
  exact S.finite_toSet.subset fun v hv => by_contra fun h => hv (hS v h)

/-- The Hecke L-factor as `(1 - a)⁻¹`. -/
theorem heckeL_eq (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) :
    heckeL χ v s = (1 - HeckeEulerProduct.coeff χ v s)⁻¹ :=
  HeckeEulerProduct.lFactor_eq χ v s

/-- The Hecke L-factors of `χ` are nonzero on a right half-plane, uniformly in the place. -/
theorem exists_heckeL_ne_zero (χ : HeckeCharacter K) :
    ∃ σ₀ : ℝ, ∀ (v : FinitePlace K) (s : ℂ), σ₀ < s.re → heckeL χ v s ≠ 0 := by
  obtain ⟨β, hβ⟩ := HeckeEulerProduct.exists_norm_finiteComponent_uniformizer χ
  refine ⟨-β, fun v s hs => ?_⟩
  have hlt : ‖HeckeEulerProduct.coeff χ v s‖ < 1 := by
    refine (HeckeEulerProduct.norm_coeff_le χ hβ v s).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith))
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  rw [heckeL_eq]
  refine inv_ne_zero fun h => ?_
  have h1 : HeckeEulerProduct.coeff χ v s = 1 := by linear_combination -h
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

theorem differentiable_coeff (χ : HeckeCharacter K) (v : FinitePlace K) :
    Differentiable ℂ (HeckeEulerProduct.coeff χ v) := by
  unfold HeckeEulerProduct.coeff
  split_ifs
  · unfold LocalFactor.PadicAbelian.spectralVariable
    fun_prop
  · exact differentiable_const 0

/-- The Hecke L-factors have nonzero germ everywhere. -/
theorem nonzeroMeromorphic_heckeL (χ : HeckeCharacter K) (v : FinitePlace K) :
    NonzeroMeromorphic (heckeL χ v) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_heckeL_ne_zero χ
  refine nonzeroMeromorphic_of_ne_zero_halfPlane (fun z => ?_) σ₀ fun s hs => hσ₀ v s hs
  have hf : heckeL χ v = fun s => (1 - HeckeEulerProduct.coeff χ v s)⁻¹ :=
    funext (heckeL_eq χ v)
  rw [hf]
  exact (((differentiable_const 1).sub (differentiable_coeff χ v)).analyticAt z).meromorphicAt.inv

end Hecke

/-- An epsilon monomial `c · q^{-ms}` with `q > 0` has nonzero germ everywhere. -/
theorem nonzeroMeromorphic_epsilonMonomial (q : ℕ) (hq : 0 < q) (c : ℂˣ) (m : ℤ) :
    NonzeroMeromorphic (RankinSelberg.epsilonMonomial q c m) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd : Differentiable ℂ (RankinSelberg.epsilonMonomial q c m) := fun s => by
    unfold RankinSelberg.epsilonMonomial
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl hq0)).zpow
        (Or.inl (RankinSelberg.spectralPoint_ne_zero_of_pos hq s)))
  exact nonzeroMeromorphic_of_ne_zero_halfPlane (fun z => (hd.analyticAt z).meromorphicAt) 0
    fun s _ => RankinSelberg.epsilonMonomial_ne_zero q (by exact_mod_cast hq) c m s

/-- Functions that agree wherever a nonzero meromorphic function is nonzero have equal germs
on every punctured neighbourhood. -/
theorem meromorphicEq_of_eq_of_ne_zero {f g G : ℂ → ℂ} (hG : NonzeroMeromorphic G)
    (h : ∀ s, G s ≠ 0 → f s = g s) : MeromorphicEq f g := fun z => by
  filter_upwards [hG.eventually_ne_zero z] with s hs using h s hs

end Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
