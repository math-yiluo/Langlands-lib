import Langlands.Representation.Archimedean.RealStandardTwoBlockOperators
import Langlands.Representation.Archimedean.RealStandardCompactHermitianForm
import Langlands.Representation.Archimedean.RealStandardCompactBlockProduct
import Langlands.Representation.Archimedean.RealGKPositiveFormComparison
import Langlands.Representation.Archimedean.RealGKNonnegativeForm
import Mathlib.MeasureTheory.Integral.Pi

/-! # Infinitesimal unitarity descends to Hermitian standard factors -/

noncomputable section

open MeasureTheory
open scoped TensorProduct ComplexConjugate Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.InvariantSesquilinear
open RealPrincipalSeriesDuality RealLeviChart RealLeviBlockHaar RealLeviSlices
open RealLeviParabolicIntegration InductionStages RealTemperedForm

attribute [local instance] measurableSpaceK secondCountableTopology_O

local instance borelSpaceK_unitarityDescent (n : ℕ) :
    BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ
private abbrev K (n : ℕ) := unitaryCompact ℝ n

private theorem exists_compact_product_of_flat_eq (dss : Fin 2 → List RealBlock)
    {D : List RealBlock} (hD : flat dss = D)
    (u : KFin (sz dss 0) (dss 0)) (v : KFin (sz dss 1) (dss 1)) :
    ∃ F : KFin (∑ i, sz dss i) D, IsTwoBlockCompactProduct (sz dss) F.val u.val v.val := by
  subst D
  let f : ∀ i : Fin 2, KFin (sz dss i) (dss i) :=
    Fin.cons u (Fin.cons v fun i => i.elim0)
  obtain ⟨F, hF⟩ := realStandardCompactBlockProduct dss f
  exact ⟨F, fun κ => (hF κ).trans (Fin.prod_univ_two _)⟩

private theorem localize_of_flat_eq (dss : Fin 2 → List RealBlock)
    {D es fs : List RealBlock} (hD : flat dss = D) :
    let N := ∑ i, sz dss i
    let cl := cls (sz dss)
    ∀ (S : KFin N D →ₗ[ℂ] KFin N es) (E : KFin N D →ₗ[ℂ] KFin N fs),
      CommutesWithBlockMultipliers cl S → CommutesWithBlockMultipliers cl E →
      ∀ a : ℂ, (∀ f : KFin N D,
        let w := ∫ k : K N, a * ((S f).val k * conj ((E f).val k)) ∂haarK N
        0 ≤ w.re ∧ w.im = 0) →
      ∀ f : KFin N D,
        let w := ∫ k : Kc cl, a * ((S f).val k * conj ((E f).val k)) ∂μc cl
        0 ≤ w.re ∧ w.im = 0 := by
  subst D
  exact realStandardBlockLocalization dss

private theorem integral_block_product (s : Fin 2 → ℕ)
    (f : G (∑ i, s i) → ℂ) (hf : Continuous f) (a : ℂ)
    (u : K (s 0) → ℂ) (v : K (s 1) → ℂ)
    (h : ∀ κ : ∀ i, K (s i), f (bd κ) = a * (u (κ 0) * v (κ 1))) :
    (∫ k : Kc (cls s), f k.val ∂μc (cls s)) =
      a * ((∫ l, u l ∂haarK (s 0)) * ∫ r, v r ∂haarK (s 1)) := by
  have hPi := integral_pi_mul_eq (sz := s) hf 1
  change (∫ κ, f (bd κ * 1) ∂Measure.pi (fun i => haarK (s i))) =
    (∫ k : Kc (cls s), f (k.val * 1) ∂μc (cls s)) at hPi
  simp only [mul_one] at hPi
  rw [← hPi, integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul]
  let w : ∀ i : Fin 2, K (s i) → ℂ := Fin.cons u (Fin.cons v fun i => i.elim0)
  have hProduct := integral_fintype_prod_eq_prod w (μ := fun i => haarK (s i))
  simp only [Fin.prod_univ_two] at hProduct
  exact congrArg (a * ·) hProduct

private theorem unitarizable_of_scaled_diagonal {n : ℕ} {ds : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (B : KFin n ds →ₗ⋆[ℂ] KFin n ds →ₗ[ℂ] ℂ) (hB : B ≠ 0)
    (hK : ∀ k u v, B (realStandardRep n ds k u) (realStandardRep n ds k v) = B u v)
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) u v,
      B (realStandardLie n ds (1 ⊗ₜ X) u) v + B u (realStandardLie n ds (1 ⊗ₜ X) v) = 0)
    (a : ℂ) (ha : a ≠ 0)
    (hPos : ∀ v, 0 ≤ (a * B v v).re ∧ (a * B v v).im = 0) :
    IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) := by
  apply realGKNonnegativeForm (realStandardRep n ds) (realStandardLie n ds) hirr (a • B)
  · exact smul_ne_zero ha hB
  · intro k u v
    change a * B (realStandardRep n ds k u) (realStandardRep n ds k v) = a * B u v
    rw [hK]
  · intro X u v
    change a * B (realStandardLie n ds (1 ⊗ₜ X) u) v +
      a * B u (realStandardLie n ds (1 ⊗ₜ X) v) = 0
    rw [← mul_add, hL, mul_zero]
  · exact fun v => (hPos v).2
  · exact fun v => (hPos v).1

/-- A consecutive two-factor splitting of an irreducible infinitesimally
unitary real standard module inherits unitarity on both factors, provided
the factors are irreducible and each is equivalent to its Hermitian dual. -/
def RealStandardUnitarityDescentStatement : Prop :=
  ∀ (A B : List RealBlock) (n : ℕ), realRank A + realRank B = n →
    let a := realRank A
    let b := realRank B
    let A' := A.map realHermitianDualBlock
    let B' := B.map realHermitianDualBlock
    ∀ (E₀ : KFin a A ≃ₗ[ℂ] KFin a A') (E₁ : KFin b B ≃ₗ[ℂ] KFin b B'),
      IsRealStandardIntertwiner a (realStandardRep a A') (realStandardLie a A') A E₀.toLinearMap →
      IsRealStandardIntertwiner b (realStandardRep b B') (realStandardLie b B') B E₁.toLinearMap →
      IsIrreducibleGKModule (realStandardRep a A) (realStandardLie a A) →
      IsIrreducibleGKModule (realStandardRep b B) (realStandardLie b B) →
      IsIrreducibleGKModule (realStandardRep n (A ++ B)) (realStandardLie n (A ++ B)) →
      IsRealUnitarizableGKModule n (realStandardRep n (A ++ B)) (realStandardLie n (A ++ B)) →
      IsRealUnitarizableGKModule a (realStandardRep a A) (realStandardLie a A) ∧
      IsRealUnitarizableGKModule b (realStandardRep b B) (realStandardLie b B)

theorem realStandardUnitarityDescent : RealStandardUnitarityDescentStatement := by
  intro A B n hn a b A' B' E₀ E₁ hE₀ hE₁ hI₀ hI₁ hI hU
  let dss : Fin 2 → List RealBlock := ![A, B]
  let s := sz dss
  let N := ∑ i, s i
  let D := A ++ B
  let cl := cls s
  have hN : N = n := (Fin.sum_univ_two s).trans hn
  rw [← hN] at hI hU
  have hD : flat dss = D := by
    rw [flat_succ, flat_succ]
    change A ++ (B ++ []) = A ++ B
    rw [List.append_nil]
  have hRank : realRank D = N := hD ▸ realRank_flat dss
  have hEA : realRank A' = s 0 := realRank_map_hermitianDual A
  have hEB : realRank B' = s 1 := realRank_map_hermitianDual B
  obtain ⟨L⟩ := SplitFourierReplacement.nonempty_characterReplacement (rfl : realRank A = s 0)
  obtain ⟨R⟩ := SplitFourierReplacement.nonempty_characterReplacement (rfl : realRank B = s 1)
  let liftSpec (es : List RealBlock) : Prop :=
    ∃ S : SplitFourierReplacement N es D,
      CommutesWithBlockMultipliers cl S.reverse ∧
      ActsOnTwoCompactFactors s S.reverse L.reverse R.reverse
  have hLift : liftSpec (D.flatMap repl) := by
    change liftSpec ((A ++ B).flatMap repl)
    rw [List.flatMap_append]
    exact realTwoBlockFourierReplacement s (realRank_flatMap_repl A) rfl
      (realRank_flatMap_repl B) rfl L R
  obtain ⟨S, hSWeight, hSProd⟩ := hLift
  let equivSpec (es : List RealBlock) : Prop :=
    ∃ E : KFin N D ≃ₗ[ℂ] KFin N es,
      IsRealStandardIntertwiner N (realStandardRep N es) (realStandardLie N es) D E.toLinearMap ∧
      CommutesWithBlockMultipliers cl E.toLinearMap ∧
      ActsOnTwoCompactFactors s E.toLinearMap E₀.toLinearMap E₁.toLinearMap
  have hEquiv : equivSpec (D.map realHermitianDualBlock) := by
    change equivSpec ((A ++ B).map realHermitianDualBlock)
    rw [List.map_append]
    exact realTwoBlockEquiv s rfl hEA rfl hEB E₀ E₁ hE₀ hE₁
  obtain ⟨E, hE, hEWeight, hEProd⟩ := hEquiv
  obtain ⟨F₀, hF₀, hF₀ne, hF₀K, hF₀L⟩ := realStandardCompactHermitianForm rfl L E₀ hE₀
  obtain ⟨F₁, hF₁, hF₁ne, hF₁K, hF₁L⟩ := realStandardCompactHermitianForm rfl R E₁ hE₁
  obtain ⟨F, hF, hFne, hFK, hFL⟩ := realStandardCompactHermitianForm hRank S E hE
  obtain ⟨p, hp⟩ := hU
  obtain ⟨c, hc⟩ := realGKPositiveFormComparison (realStandardRep N D) (realStandardLie N D)
    (isRealGKModule_realStandardModule N D) (realStandardDensityHyp hI) p F hp hFK hFL
  have hcne : c ≠ 0 := by
    intro hz
    apply hFne
    ext v w
    rw [hc, hz, zero_mul]
    rfl
  let a₀ := c⁻¹
  have ha₀ : a₀ ≠ 0 := inv_ne_zero hcne
  have hPos (f : KFin N D) :
      let w := ∫ k : K N, a₀ * ((S.reverse f).val k * conj ((E f).val k)) ∂haarK N
      0 ≤ w.re ∧ w.im = 0 := by
    dsimp only
    have he :
        (∫ k : K N, a₀ * ((S.reverse f).val k * conj ((E f).val k)) ∂haarK N) = p.inner f f := by
      rw [integral_const_mul, ← hF f f, hc, ← mul_assoc]
      rw [show a₀ * c = 1 from inv_mul_cancel₀ hcne, one_mul]
    rw [he]
    exact ⟨p.re_inner_nonneg f, (Complex.conj_eq_iff_im).mp (p.conj_inner_symm f f)⟩
  have hBoth (u : KFin a A) (v : KFin b B) :
      0 ≤ (a₀ * (F₀ u u * F₁ v v)).re ∧ (a₀ * (F₀ u u * F₁ v v)).im = 0 := by
    obtain ⟨f, hf⟩ := exists_compact_product_of_flat_eq dss hD u v
    let ψ : G N → ℂ := fun k => a₀ * ((S.reverse f).val k * conj ((E f).val k))
    have hψ : Continuous ψ := continuous_const.mul
      ((continuous_of_mem_kFiniteFunctions (S.reverse f).2).mul
        (Complex.continuous_conj.comp (continuous_of_mem_kFiniteFunctions (E f).2)))
    let g₀ : K (s 0) → ℂ := fun k => (L.reverse u).val k.val * conj ((E₀ u).val k.val)
    let g₁ : K (s 1) → ℂ := fun k => (R.reverse v).val k.val * conj ((E₁ v).val k.val)
    have hProd (κ : ∀ i, K (s i)) : ψ (bd κ) = a₀ * (g₀ (κ 0) * g₁ (κ 1)) := by
      calc
        ψ (bd κ) = a₀ * (((L.reverse u).val (κ 0).val * (R.reverse v).val (κ 1).val) *
            conj ((E₀ u).val (κ 0).val * (E₁ v).val (κ 1).val)) :=
          congrArg₂ (fun x y : ℂ => a₀ * (x * conj y)) (hSProd f u v hf κ) (hEProd f u v hf κ)
        _ = _ := by
          dsimp only [g₀, g₁]
          rw [map_mul]
          ring
    have he := integral_block_product s ψ hψ a₀ g₀ g₁ hProd
    have hi₀ : (∫ k, g₀ k ∂haarK (s 0)) = F₀ u u := (hF₀ u u).symm
    have hi₁ : (∫ k, g₁ k ∂haarK (s 1)) = F₁ v v := (hF₁ v v).symm
    rw [hi₀, hi₁] at he
    have hl := localize_of_flat_eq dss hD S.reverse E.toLinearMap hSWeight hEWeight a₀ hPos f
    change 0 ≤ (∫ k : Kc cl, ψ k.val ∂μc cl).re ∧
      (∫ k : Kc cl, ψ k.val ∂μc cl).im = 0 at hl
    rwa [he] at hl
  obtain ⟨u₀, hu₀⟩ := exists_diagonal_ne_zero F₀ hF₀ne
  obtain ⟨v₀, hv₀⟩ := exists_diagonal_ne_zero F₁ hF₁ne
  refine ⟨unitarizable_of_scaled_diagonal hI₀ F₀ hF₀ne hF₀K hF₀L (a₀ * F₁ v₀ v₀)
      (mul_ne_zero ha₀ hv₀) ?_,
    unitarizable_of_scaled_diagonal hI₁ F₁ hF₁ne hF₁K hF₁L (a₀ * F₀ u₀ u₀)
      (mul_ne_zero ha₀ hu₀) ?_⟩
  · intro u
    have he : (a₀ * F₁ v₀ v₀) * F₀ u u = a₀ * (F₀ u u * F₁ v₀ v₀) := by ring
    rw [he]
    exact hBoth u v₀
  · intro v
    rw [mul_assoc]
    exact hBoth u₀ v

end Langlands.Archimedean
