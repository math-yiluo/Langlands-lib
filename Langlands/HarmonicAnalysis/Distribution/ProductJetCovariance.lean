import Langlands.HarmonicAnalysis.Distribution.ProductJetDistribution
import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform

/-! # Leading transverse coefficient under a local change of coordinates -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens W}

/-- A distribution has transverse order at most `i` if it annihilates the tests
whose transverse derivatives through order `i` vanish on the zero section. -/
def HasTransverseJetOrder (T : 𝓓'(productTestDomain U V, F)) (i : ℕ) : Prop :=
  ∀ f : 𝓓(productTestDomain U V, ℝ),
    (∀ k ≤ i, transverseProductJetCLM k f = 0) → T f = 0

/-- The restriction of a distribution supported on the zero section to an open
product inside a fixed compact subset has bounded transverse order. -/
theorem hasTransverseJetOrder_comp_monoCLM [FiniteDimensional ℝ W]
    (T : 𝓓'(productTestDomain U V, F))
    (hT : Distribution.IsVanishingOn T {z : E × W | z.2 ≠ 0})
    {U₀ : Opens E} {V₀ : Opens W} {K : Compacts (E × W)}
    (hK : (K : Set (E × W)) ⊆ productTestDomain U V)
    (hK₀ : (productTestDomain U₀ V₀ : Set (E × W)) ⊆ K) :
    HasTransverseJetOrder
      (T.comp (TestFunction.monoCLM ℝ (Ω₁ := productTestDomain U₀ V₀) (n₁ := ⊤)))
      (smoothDistributionCompactOrder T hK) := by
  intro f hflat
  let fc : 𝓓_{K}(E × W, ℝ) := ContDiffMapSupportedIn.of_support_subset f.contDiff
    ((subset_tsupport (⇑f)).trans (f.tsupport_subset.trans hK₀))
  have hle : productTestDomain U₀ V₀ ≤ productTestDomain U V := hK₀.trans hK
  have hfc : (TestFunction.monoCLM ℝ f : 𝓓(productTestDomain U V, ℝ)) =
      TestFunction.ofSupportedIn hK fc := by
    ext z
    have h : (⇑(TestFunction.monoCLM ℝ f : 𝓓(productTestDomain U V, ℝ))) = ⇑f := by
      simp [hle]
    exact congrFun h z
  change T (TestFunction.monoCLM ℝ f) = 0
  rw [hfc]
  apply distribution_eq_zero_of_transverseProductJet T hT hK fc
  intro x i hi v
  change iteratedFDeriv ℝ i f (x, 0) (fun k => (0, v k)) = 0
  rw [← transverseProductJetCLM_apply, hflat i hi]
  rfl

/-- When lower transverse derivatives vanish, a distribution of transverse order
at most `i` evaluates only the order-`i` coefficient. -/
theorem eval_eq_transverseProductJetCoefficient_of_lower_eq_zero
    (T : 𝓓'(productTestDomain U V, F)) (i : ℕ) (hord : HasTransverseJetOrder T i)
    (χ : 𝓓(V, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1)
    (f : 𝓓(productTestDomain U V, ℝ)) (hflat : ∀ k < i, transverseProductJetCLM k f = 0) :
    T f = transverseProductJetCoefficient T χ i (transverseProductJetCLM i f) := by
  let a := transverseProductJetCLM i f
  have hz := hord (f - productJetExtensionCLM χ i a) (by
    intro k hk
    rw [map_sub]
    by_cases hki : k = i
    · subst k
      rw [transverseProductJetCLM_productJetExtensionCLM_self χ hχ i a
        (transverseProductJetCLM_comp_perm i f), sub_self]
    · rw [transverseProductJetCLM_productJetExtensionCLM_of_ne χ hχ (Ne.symm hki) a,
        hflat k (hk.lt_of_ne hki), sub_zero])
  change T f = T (productJetExtensionCLM χ i a)
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem hasTransverseJetOrder_of_coefficient_eq_zero
    (T : 𝓓'(productTestDomain U V, F)) (i : ℕ) (hord : HasTransverseJetOrder T (i + 1))
    (χ : 𝓓(V, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1)
    (hc : transverseProductJetCoefficient T χ (i + 1) = 0) :
    HasTransverseJetOrder T i := by
  intro f hflat
  rw [eval_eq_transverseProductJetCoefficient_of_lower_eq_zero T (i + 1) hord χ hχ f
    (fun k hk => hflat k (Nat.le_of_lt_succ hk)), hc]
  rfl

theorem distribution_eq_zero_of_coefficient_zero_at_order_zero
    (T : 𝓓'(productTestDomain U V, F)) (hord : HasTransverseJetOrder T 0)
    (χ : 𝓓(V, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1)
    (hc : transverseProductJetCoefficient T χ 0 = 0) :
    T = 0 := by
  ext f
  rw [eval_eq_transverseProductJetCoefficient_of_lower_eq_zero T 0 hord χ hχ f
    (fun k hk => (Nat.not_lt_zero k hk).elim), hc]
  rfl

section Pullback

variable {E' W' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  {U' : Opens E'} {V' : Opens W'}
  (P : 𝓓(productTestDomain U' V', ℝ) →L[ℝ] 𝓓(productTestDomain U V, ℝ))
  (H : E × W → E' × W') (b : E → E')
  (hH : ∀ x ∈ U, ContDiffAt ℝ ∞ H (x, 0))
  (hH0 : ∀ x ∈ U, H (x, 0) = (b x, 0))
  (hP : ∀ (f : 𝓓(productTestDomain U' V', ℝ)) (x : E), x ∈ U →
    (P f : E × W → ℝ) =ᶠ[𝓝 (x, 0)] (⇑f ∘ H))

include hH hH0 hP in
theorem transverseProductJetCLM_pullback_apply (i : ℕ)
    (f : 𝓓(productTestDomain U' V', ℝ))
    (hflat : ∀ k < i, transverseProductJetCLM k f = 0)
    {x : E} (hx : x ∈ U) (v : Fin i → W) :
    transverseProductJetCLM i (P f) x v =
      transverseProductJetCLM i f (b x) (fun k => productNormalDerivative H x (v k)) := by
  rw [transverseProductJetCLM_apply, ((hP f x hx).iteratedFDeriv ℝ i).eq_of_nhds]
  exact transverseProductJet_comp_of_lower_eq_zero f (hH x hx) (hH0 x hx) i hflat v

include hH hH0 hP in
theorem transverseProductJetCLM_pullback_eq_zero (i : ℕ)
    (f : 𝓓(productTestDomain U' V', ℝ))
    (hflat : ∀ k ≤ i, transverseProductJetCLM k f = 0) :
    transverseProductJetCLM i (P f) = 0 := by
  ext x v
  by_cases hx : x ∈ U
  · rw [transverseProductJetCLM_pullback_apply P H b hH hH0 hP i f
      (fun k hk => hflat k hk.le) hx, hflat i le_rfl]
    rfl
  · have h := (transverseProductJetCLM i (P f)).zero_on_compl hx
    exact congrArg (fun a : W [×i]→L[ℝ] ℝ => a v) h

/-- The induced continuous pullback on order-`i` test coefficients. The output
coefficients are symmetric because they are extracted as derivatives. -/
def transverseProductJetPullbackCLM (χ' : 𝓓(V', ℝ)) (i : ℕ) :
    𝓓(U', W' [×i]→L[ℝ] ℝ) →L[ℝ] 𝓓(U, W [×i]→L[ℝ] ℝ) :=
  (transverseProductJetCLM i).comp (P.comp (productJetExtensionCLM χ' i))

include hH hH0 hP in
theorem transverseProductJetPullbackCLM_apply (χ' : 𝓓(V', ℝ))
    (hχ' : (χ' : W' → ℝ) =ᶠ[𝓝 0] 1) (i : ℕ)
    (a : 𝓓(U', W' [×i]→L[ℝ] ℝ))
    (ha : ∀ x v (σ : Equiv.Perm (Fin i)), a x (v ∘ σ) = a x v)
    {x : E} (hx : x ∈ U) (v : Fin i → W) :
    transverseProductJetPullbackCLM P χ' i a x v =
      a (b x) (fun k => productNormalDerivative H x (v k)) := by
  change transverseProductJetCLM i (P (productJetExtensionCLM χ' i a)) x v = _
  rw [transverseProductJetCLM_pullback_apply P H b hH hH0 hP i
    (productJetExtensionCLM χ' i a)
    (fun k hk => transverseProductJetCLM_productJetExtensionCLM_of_ne χ' hχ' hk.ne' a) hx,
    transverseProductJetCLM_productJetExtensionCLM_self χ' hχ' i a ha]

include hH hH0 hP in
/-- The leading coefficient of a transported distribution is the original leading
coefficient composed with the pullback on multilinear-valued tests. -/
theorem transverseProductJetCoefficient_comp
    (T : 𝓓'(productTestDomain U V, F)) (i : ℕ) (hord : HasTransverseJetOrder T i)
    (χ : 𝓓(V, ℝ)) (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1)
    (χ' : 𝓓(V', ℝ)) (hχ' : (χ' : W' → ℝ) =ᶠ[𝓝 0] 1) :
    transverseProductJetCoefficient (T.comp P) χ' i =
      (transverseProductJetCoefficient T χ i).comp (transverseProductJetPullbackCLM P χ' i) := by
  ext a
  change T (P (productJetExtensionCLM χ' i a)) =
    transverseProductJetCoefficient T χ i
      (transverseProductJetCLM i (P (productJetExtensionCLM χ' i a)))
  apply eval_eq_transverseProductJetCoefficient_of_lower_eq_zero T i hord χ hχ
  intro k hk
  apply transverseProductJetCLM_pullback_eq_zero P H b hH hH0 hP
  intro l hl
  exact transverseProductJetCLM_productJetExtensionCLM_of_ne χ' hχ' (hl.trans_lt hk).ne' a

end Pullback

end Langlands.HarmonicAnalysis
