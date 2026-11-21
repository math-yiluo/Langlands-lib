import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Global.EisensteinCommonNormalization

/-! # Normalization from the original local continuation witnesses -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace Langlands.Analysis.Meromorphic

variable {E V Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [AddCommGroup Z] [Module ℂ Z]

/-- Extend a local numerator and denominator to the ambient parameter space,
and use the open dense subset where the denominator does not vanish. -/
theorem IsMeromorphicOn.exists_flat_numerator {B : TopologicalSpace.Opens E}
    {v : B → V} {D : Set B} (hv : IsMeromorphicOn 𝓘(ℂ, E) v D)
    (eval : V →ₗ[ℂ] Z) (f : E → Z)
    (hf : ∀ s ∈ D, eval (v s) = f s.val) (z : B) :
    ∃ (W U : Set E) (a : E → ℂ) (H : E → V),
      IsOpen W ∧ z.val ∈ W ∧ IsOpen U ∧ W ⊆ closure U ∧
      DifferentiableOn ℂ a W ∧
      (∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (H t)) W) ∧
      ∀ t ∈ U, t ∈ Subtype.val '' D ∧ a t ≠ 0 ∧ eval (H t) = a t • f t := by
  classical
  obtain ⟨hDo, hDd, _, hlocal⟩ := hv
  obtain ⟨W₀, hWo₀, hWc₀, hzW, a₀, H₀, ha₀, ⟨s, hsW, hsa⟩, hH₀, hEq⟩ := hlocal z
  let W := Subtype.val '' W₀
  let D' := Subtype.val '' D
  let a := extendOpens a₀
  let H := extendOpens H₀
  let V₀ := W ∩ a ⁻¹' ({0}ᶜ : Set ℂ)
  let U := V₀ ∩ D'
  have hWo : IsOpen W := B.isOpen.isOpenMap_subtype_val W₀ hWo₀
  have hDo' : IsOpen D' := B.isOpen.isOpenMap_subtype_val D hDo
  have hclD : W ⊆ closure D' := by
    rintro _ ⟨x, _, rfl⟩
    have hx : x ∈ closure D := hDd x
    exact image_closure_subset_closure_image continuous_subtype_val ⟨x, hx, rfl⟩
  have hWc : IsPreconnected W := hWc₀.isPreconnected.image _ continuous_subtype_val.continuousOn
  have ha : DifferentiableOn ℂ a W := differentiableOn_extendOpens hWo₀ ha₀
  have hne : ∃ x ∈ W, a x ≠ 0 := ⟨s.val, ⟨s, hsW, rfl⟩, by
    change extendOpens a₀ s.val ≠ 0
    rwa [extendOpens_coe]⟩
  have hVo : IsOpen V₀ := ha.continuousOn.isOpen_inter_preimage hWo isClosed_singleton.isOpen_compl
  refine ⟨W, U, a, H, hWo, ⟨z, hzW, rfl⟩, hVo.inter hDo', ?_, ha, ?_, ?_⟩
  · intro x hx
    apply mem_closure_iff.mpr
    intro O hOo hxO
    obtain ⟨y, ⟨hyO, hyW⟩, hya⟩ := exists_ne_zero_of_differentiableOn hWo hWc ha hne
      (hOo.inter hWo) inter_subset_right ⟨x, hxO, hx⟩
    have hyV : y ∈ V₀ := ⟨hyW, hya⟩
    obtain ⟨t, ⟨htO, htV⟩, htD⟩ := mem_closure_iff.mp (hclD hyW) (O ∩ V₀)
      (hOo.inter hVo) ⟨hyO, hyV⟩
    exact ⟨t, htO, htV, htD⟩
  · intro test
    have htest : (fun t => test (H t)) = extendOpens (fun s => test (H₀ s)) := by
      funext t
      by_cases ht : t ∈ B <;> simp [H, extendOpens, ht]
    rw [htest]
    exact differentiableOn_extendOpens hWo₀ (hH₀ test)
  · rintro t ⟨⟨⟨x, hxW, rfl⟩, hxa⟩, hxD⟩
    refine ⟨hxD, hxa, ?_⟩
    obtain ⟨y, hyD, hxy⟩ := hxD
    have hxy' : y = x := Subtype.val_injective hxy
    subst y
    change eval (extendOpens H₀ x.val) = extendOpens a₀ x.val • f x.val
    rw [extendOpens_coe, extendOpens_coe, ← hEq x ⟨hyD, hxW⟩, map_smul, hf x hyD]

end Langlands.Analysis.Meromorphic

namespace Langlands.Global.EisensteinJet

open Langlands.Analysis.Meromorphic Langlands.Automorphic.GroupSchemeFunctions
  UniformGrowthFrechetSpace

/-- Extend a family of continued basis vectors linearly in its coordinates. -/
def continuedLinearCombination {E Z : Type*} [AddCommGroup Z] [Module ℂ Z] {n : ℕ}
    (f : Fin n → E → Z) (t : E) : (Fin n → ℂ) →ₗ[ℂ] Z :=
  commonNumerator (fun _ => 1) (fun j => f j t)

@[simp]
theorem continuedLinearCombination_apply {E Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    {n : ℕ} (f : Fin n → E → Z) (t : E) (c : Fin n → ℂ) :
    continuedLinearCombination f t c = ∑ j, c j • f j t := by
  simp [continuedLinearCombination]

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

/-- The local Fréchet-valued continuation witnesses of finitely many sections
provide a common normalization on a ball around the specialization point. -/
theorem exists_common_normalization_of_meromorphic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (z : E) (B : Fin n → TopologicalSpace.Opens E) (hz : ∀ j, z ∈ B j)
    (R : Fin n → ℝ) (L : Fin n → Subgroup (FiniteAdelicGroupPoints F G))
    (hL : ∀ j, IsOpen (L j : Set (FiniteAdelicGroupPoints F G)))
    (v : ∀ j, B j → Growth[R j, L j]) (D : ∀ j, Set (B j))
    (hv : ∀ j, IsMeromorphicOn 𝓘(ℂ, E) (v j) (D j))
    (f : Fin n → E → AdelicGroupPoints F G → ℂ)
    (hf : ∀ j (t : B j), t ∈ D j →
      toFun F G rho hsmooth hcalc hN hrho (R j) (L j) (v j t) = f j t.val) :
    ∃ r > 0, ∃ (S : ℝ) (M : Subgroup (FiniteAdelicGroupPoints F G)),
      IsOpen (M : Set (FiniteAdelicGroupPoints F G)) ∧
      ∃ (A : E → ℂ) (J : E → (Fin n → ℂ) →ₗ[ℂ] Growth[S, M]) (V : Set E),
        DifferentiableOn ℂ A (Metric.ball z r) ∧
        (∀ c (test : Growth[S, M] →L[ℂ] ℂ),
          DifferentiableOn ℂ (fun t => test (J t c)) (Metric.ball z r)) ∧
        IsOpen V ∧ V ⊆ Metric.ball z r ∧ Metric.ball z r ⊆ closure V ∧
        (∀ t ∈ V, (∀ j, t ∈ Subtype.val '' D j) ∧ A t ≠ 0 ∧
          ∀ c, toFun F G rho hsmooth hcalc hN hrho S M (J t c) =
            A t • continuedLinearCombination f t c) := by
  let eval (j : Fin n) : Growth[R j, L j] →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) :=
    ⟨⟨toFun F G rho hsmooth hcalc hN hrho (R j) (L j), fun _ _ => rfl⟩, fun _ _ => rfl⟩
  choose W U a H hWo hzW hUo hclU ha hH hEq using fun j =>
    (hv j).exists_flat_numerator (eval j) (f j) (hf j) ⟨z, hz j⟩
  obtain ⟨r, hr, S, M, hMo, A, J, V, hA, hJ, hVo, hVball, hclV, hV⟩ :=
    exists_common_normalization F G rho hsmooth hcalc hN hrho z W U hWo hzW hUo hclU
      a ha (fun j t ht => (hEq j t ht).2.1) R L hL f H hH
      (fun j t ht => (hEq j t ht.2).2.2)
  refine ⟨r, hr, S, M, hMo, A, J, V, hA, hJ, hVo, hVball, hclV, fun t ht => ?_⟩
  obtain ⟨hUt, hAt, hJt⟩ := hV t ht
  exact ⟨fun j => (hEq j t (hUt j)).1, hAt, by simpa only [continuedLinearCombination_apply] using hJt⟩

end Langlands.Global.EisensteinJet
