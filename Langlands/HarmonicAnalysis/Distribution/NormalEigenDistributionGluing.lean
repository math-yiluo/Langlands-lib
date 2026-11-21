import Langlands.HarmonicAnalysis.Distribution.NormalEigenDistributionExtension

/-! # Holomorphic gluing of compact-support eigen-distribution extensions -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Ω : Opens X}

/-- A family has one bound of finite derivative order on each fixed compact test support. -/
def HasUniformCompactTestOrder {Ω : Opens X} (T : ℂ → 𝓓'(Ω, ℂ)) (S : Set ℂ) : Prop :=
  ∀ (K : Compacts X) (hK : (K : Set X) ⊆ Ω), ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z ∈ S, ∀ f, ‖T z (TestFunction.ofSupportedIn hK f)‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℝ X ℝ ⊤ K d f

/-- Holomorphic functions on a preconnected open set agree when their values agree
on a nonempty open subset. -/
theorem eqOn_of_holomorphic_eqOn_seed {S S₀ : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hS₀ : IsOpen S₀) (hsub : S₀ ⊆ S) (hne : S₀.Nonempty) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f S) (hg : DifferentiableOn ℂ g S) (he : EqOn f g S₀) : EqOn f g S := by
  obtain ⟨z, hz⟩ := hne
  have hnear : ∀ᶠ q in 𝓝 z, q ∈ S₀ := hS₀.mem_nhds hz
  exact (hf.analyticOnNhd hS).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hS) hconn
    (hsub hz) (hnear.mono he)

/-- Compact-support forms which are holomorphic in the parameter and agree with a
common distribution on an open seed domain define a holomorphic distribution family. -/
theorem exists_distributionFamily_of_compactForms {S S₀ : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hS₀ : IsOpen S₀) (hsub : S₀ ⊆ S) (hne : S₀.Nonempty)
    (T₀ : ℂ → 𝓓'(Ω, ℂ))
    (L : ∀ (K : Compacts X), (K : Set X) ⊆ Ω → ℂ → 𝓓_{K}(X, ℝ) →L[ℝ] ℂ)
    (hHol : ∀ K hK f, DifferentiableOn ℂ (fun z => L K hK z f) S)
    (hSeed : ∀ z ∈ S₀, ∀ K hK f, L K hK z f = T₀ z (TestFunction.ofSupportedIn hK f)) :
    ∃ T : ℂ → 𝓓'(Ω, ℂ),
      (∀ f, DifferentiableOn ℂ (fun z => T z f) S) ∧
      (∀ z ∈ S, ∀ K hK f, T z (TestFunction.ofSupportedIn hK f) = L K hK z f) ∧ EqOn T T₀ S₀ := by
  classical
  let Kf (f : 𝓓(Ω, ℝ)) : Compacts X := ⟨tsupport f, f.hasCompactSupport⟩
  let hKf (f : 𝓓(Ω, ℝ)) : (Kf f : Set X) ⊆ Ω := f.tsupport_subset
  let fK (f : 𝓓(Ω, ℝ)) : 𝓓_{Kf f}(X, ℝ) := ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure
  have hfK (f : 𝓓(Ω, ℝ)) : TestFunction.ofSupportedIn (hKf f) (fK f) = f := rfl
  let ev (z : ℂ) (f : 𝓓(Ω, ℝ)) : ℂ := if z ∈ S then L (Kf f) (hKf f) z (fK f) else 0
  let form (K : Compacts X) (hK : (K : Set X) ⊆ Ω) (z : ℂ) : 𝓓_{K}(X, ℝ) →L[ℝ] ℂ :=
    if z ∈ S then L K hK z else 0
  have he (K : Compacts X) (hK : (K : Set X) ⊆ Ω) (z : ℂ) (f : 𝓓_{K}(X, ℝ)) :
      ev z (TestFunction.ofSupportedIn hK f) = form K hK z f := by
    by_cases hz : z ∈ S
    · simp only [ev, form, ite_eq_left hz]
      refine eqOn_of_holomorphic_eqOn_seed hS hconn hS₀ hsub hne (hHol _ _ _) (hHol K hK f) ?_ hz
      intro q hq
      change L _ _ q _ = L K hK q f
      rw [hSeed q hq, hSeed q hq, hfK]
    · simp only [ev, form, ite_eq_right hz, zero_apply]
  let T (z : ℂ) : 𝓓'(Ω, ℂ) := TestFunction.limitCLM ℝ (ev z) (fun K hK => form K hK z) fun K hK => he K hK z
  refine ⟨T, ?_, ?_, ?_⟩
  · intro f
    refine (hHol (Kf f) (hKf f) (fK f)).congr fun z hz => ?_
    change ev z f = L (Kf f) (hKf f) z (fK f)
    exact ite_eq_left hz
  · intro z hz K hK f
    change ev z _ = _
    rw [he, show form K hK z = L K hK z from ite_eq_left hz]
  · intro z hz
    apply DFunLike.ext
    intro f
    change ev z f = _
    simp only [ev, ite_eq_left (hsub hz), hSeed z hz, hfK]

variable {E : Type u} {N : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

local notation "X₀" => E × N
local notation "pK(" K "|" k ")" => ContDiffMapSupportedIn.supSeminorm ℝ X₀ ℝ ⊤ K k

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ N] in
private theorem supSeminorm_mono_order (K : Compacts X₀) {i j : ℕ} (hij : i ≤ j) :
    pK(K | i) ≤ pK(K | j) :=
  Finset.sup_mono fun _ hk => Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans hij)

/-- Punctured holomorphic distributions with a common weighted bound on each compact
extend across the zero section under a vanishing nilpotently linearized field and
nonzero infinitesimal covariance. The full-domain seed supplies compatibility. -/
theorem exists_normalEigenDistributionExtension {Ω : Opens X₀} {W : X₀ → X₀} {b : X₀ → ℝ}
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hZero : ∀ x : E, (x, (0 : N)) ∈ Ω → W (x, 0) = 0 ∧ b (x, 0) = 0)
    (hNil : ∀ x : E, (x, (0 : N)) ∈ Ω → IsNilpotent (fderiv ℝ W (x, 0)).toLinearMap)
    {S S₀ : Set ℂ} (hS : IsOpen S) (hconn : IsPreconnected S) (hS₀ : IsOpen S₀)
    (hsub : S₀ ⊆ S) (hne : S₀.Nonempty)
    (T : ℂ → 𝓓'(normalPuncturedDomain Ω, ℂ)) (T₀ : ℂ → 𝓓'(Ω, ℂ))
    (hT : ∀ (K : Compacts X₀), (K : Set X₀) ⊆ Ω → ∃ d m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z ∈ S, HasWeightedNormalBound (T z) K d m A)
    (hHol : ∀ g : 𝓓(normalPuncturedDomain Ω, ℝ), DifferentiableOn ℂ (fun z => T z g) S)
    (eigen : ℂ) (heigen : eigen ≠ 0)
    (hEig : ∀ z ∈ S, ∀ g, T z (shiftedVectorFieldDerivativeTest
      (hW.mono (inter_subset_left : (normalPuncturedDomain Ω : Set X₀) ⊆ Ω))
      (hb.mono inter_subset_left) g) = eigen * T z g)
    (hRestr : ∀ z ∈ S₀, ∀ g, T z g = T₀ z (TestFunction.monoCLM ℝ g))
    (hEig₀ : ∀ z ∈ S₀, ∀ g, T₀ z (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T₀ z g)
    (hSeedOrder : ∀ z ∈ S₀, ∀ (K : Compacts X₀) (hK : (K : Set X₀) ⊆ Ω),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖T₀ z (TestFunction.ofSupportedIn hK f)‖ ≤ C * pK(K | 0) f) :
    ∃ T' : ℂ → 𝓓'(Ω, ℂ), HasUniformCompactTestOrder T' S ∧
      (∀ f, DifferentiableOn ℂ (fun z => T' z f) S) ∧
      (∀ z ∈ S, ∀ g, T' z (TestFunction.monoCLM ℝ g) = T z g) ∧ EqOn T' T₀ S₀ ∧
      ∀ z ∈ S, ∀ g, T' z (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T' z g := by
  classical
  have hForms (K : Compacts X₀) (hK : (K : Set X₀) ⊆ Ω) :
      ∃ L : ℂ → 𝓓_{K}(X₀, ℝ) →L[ℝ] ℂ,
        (∀ f, DifferentiableOn ℂ (fun z => L z f) S) ∧
        (∃ order : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f z, z ∈ S → ‖L z f‖ ≤ C * pK(K | order) f) ∧
        (∀ z ∈ S, ∀ (f : 𝓓_{K}(X₀, ℝ)) (hoff : tsupport f ⊆ normalPuncturedDomain Ω),
          L z f = T z ⟨f, f.contDiff, f.hasCompactSupport, hoff⟩) ∧
        ∀ z ∈ S₀, ∀ f, L z f = T₀ z (TestFunction.ofSupportedIn hK f) := by
    obtain ⟨d, m, A, hA, hTK⟩ := hT K hK
    obtain ⟨_, order, C, hC, L, hLHol, hLBound, _, hLOff, hLSeed⟩ :=
      exists_fixedSupportNormalEigenExtension hW hb hK hZero hNil hS T hA hTK hHol eigen heigen hEig
    refine ⟨L, hLHol, ⟨order, C, hC, hLBound⟩, hLOff, fun z hz => ?_⟩
    obtain ⟨C₀, hC₀, hBound₀⟩ := hSeedOrder z hz K hK
    refine hLSeed z (hsub hz) (T₀ z) (hRestr z hz) (hEig₀ z hz) C₀ hC₀ fun f => ?_
    exact (hBound₀ f).trans (mul_le_mul_of_nonneg_left (supSeminorm_mono_order K (Nat.zero_le _) f) hC₀)
  choose L hLHol hLBound hLOff hLSeed using hForms
  obtain ⟨T', hT'Hol, hCompare, hSeed⟩ := exists_distributionFamily_of_compactForms
    hS hconn hS₀ hsub hne T₀ L hLHol fun z hz K hK => hLSeed K hK z hz
  refine ⟨T', ?_, hT'Hol, ?_, hSeed, ?_⟩
  · intro K hK
    obtain ⟨order, C, hC, hBound⟩ := hLBound K hK
    refine ⟨order, C, hC, fun z hz f => ?_⟩
    rw [hCompare z hz K hK f]
    exact hBound f z hz
  · intro z hz g
    let K : Compacts X₀ := ⟨tsupport g, g.hasCompactSupport⟩
    let f : 𝓓_{K}(X₀, ℝ) := ContDiffMapSupportedIn.of_support_subset g.contDiff subset_closure
    have hm : normalPuncturedDomain Ω ≤ Ω := inter_subset_left
    have hK : (K : Set X₀) ⊆ Ω := g.tsupport_subset.trans hm
    have he : (TestFunction.monoCLM ℝ g : 𝓓(Ω, ℝ)) = TestFunction.ofSupportedIn hK f := by
      have hcoe : ((TestFunction.monoCLM ℝ g : 𝓓(Ω, ℝ)) : X₀ → ℝ) = g := by simp [hm]
      ext x
      exact congrFun hcoe x
    rw [he, hCompare z hz K hK f]
    exact hLOff K hK z hz f g.tsupport_subset
  · intro z hz g
    refine eqOn_of_holomorphic_eqOn_seed hS hconn hS₀ hsub hne (hT'Hol _)
      ((hT'Hol g).const_mul eigen) ?_ hz
    intro q hq
    change T' q (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T' q g
    rw [hSeed hq]
    exact hEig₀ q hq g

/-- A holomorphic eigen-distribution family extends from a punctured domain
when its weighted bounds and its full-domain order-zero seed are available. -/
def NormalEigenDistributionGluingStatement : Prop :=
  ∀ (E : Type u) (N : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ω : Opens (E × N)) (W : E × N → E × N) (b : E × N → ℝ)
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω),
    (∀ x : E, (x, (0 : N)) ∈ Ω → W (x, 0) = 0 ∧ b (x, 0) = 0) →
    (∀ x : E, (x, (0 : N)) ∈ Ω → IsNilpotent (fderiv ℝ W (x, 0)).toLinearMap) →
    ∀ (S S₀ : Set ℂ), IsOpen S → IsPreconnected S → IsOpen S₀ → S₀ ⊆ S → S₀.Nonempty →
    ∀ (T : ℂ → 𝓓'(normalPuncturedDomain Ω, ℂ)) (T₀ : ℂ → 𝓓'(Ω, ℂ)),
      (∀ (K : Compacts (E × N)), (K : Set (E × N)) ⊆ Ω → ∃ d m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ z ∈ S, HasWeightedNormalBound (T z) K d m A) →
      (∀ g : 𝓓(normalPuncturedDomain Ω, ℝ), DifferentiableOn ℂ (fun z => T z g) S) →
      ∀ (eigen : ℂ), eigen ≠ 0 →
      (∀ z ∈ S, ∀ g, T z (shiftedVectorFieldDerivativeTest
        (hW.mono (inter_subset_left : (normalPuncturedDomain Ω : Set (E × N)) ⊆ Ω))
        (hb.mono inter_subset_left) g) = eigen * T z g) →
      (∀ z ∈ S₀, ∀ g, T z g = T₀ z (TestFunction.monoCLM ℝ g)) →
      (∀ z ∈ S₀, ∀ g, T₀ z (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T₀ z g) →
      (∀ z ∈ S₀, ∀ (K : Compacts (E × N)) (hK : (K : Set (E × N)) ⊆ Ω),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖T₀ z (TestFunction.ofSupportedIn hK f)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K 0 f) →
      ∃ T' : ℂ → 𝓓'(Ω, ℂ), HasUniformCompactTestOrder T' S ∧
        (∀ f, DifferentiableOn ℂ (fun z => T' z f) S) ∧
        (∀ z ∈ S, ∀ g, T' z (TestFunction.monoCLM ℝ g) = T z g) ∧ EqOn T' T₀ S₀ ∧
        ∀ z ∈ S, ∀ g, T' z (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T' z g

theorem normalEigenDistributionGluing : NormalEigenDistributionGluingStatement.{u, v} := by
  intro E N _ _ _ _ _ _ Ω W b hW hb hZero hNil S S₀ hS hconn hS₀ hsub hne T T₀ hT hHol eigen heigen
    hEig hRestr hEig₀ hSeedOrder
  exact exists_normalEigenDistributionExtension hW hb hZero hNil hS hconn hS₀ hsub hne T T₀ hT hHol
    eigen heigen hEig hRestr hEig₀ hSeedOrder

end Langlands.HarmonicAnalysis
