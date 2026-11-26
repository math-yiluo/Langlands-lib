import Langlands.Global.AdelicIntertwiningAutomorphyStatement
import Langlands.Global.AdelicEisensteinGlobalMajorant
import Langlands.Global.AdelicEisensteinUnfoldingGlobalMajorant
import Langlands.GroupScheme.MatrixRepresentationRationalPoints

/-! # Moderate growth of regular adelic intertwining integrals

A proof of `Langlands.Global.IntertwiningModerateGrowthStatement`: the global polynomial
majorant of the Eisenstein terms (`eisensteinGlobalMajorant`) unfolds to an integrable majorant
on the rational intertwining quotient that keeps a power of the adelic height of the external
argument (`exists_integrable_unfolding_majorant`). Integrating it and multiplying by the
polynomial bound of the target height power gives moderate growth. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RepresentationGrowth

/-- A closed matrix embedding of size zero forces the adelic points to form a trivial group. -/
theorem subsingleton_adelicGroupPoints_of_closed_zeroMatrix {F : Type u} [Field F]
    [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    Subsingleton (AdelicGroupPoints F G) := by
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : Mono rho.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => rho.pointMatrix_injective _ (Subsingleton.elim _ _)⟩

/-- **Moderate growth of intertwining integrals** (Mœglin–Waldspurger II.1.6 (i)). For the data
of `IntertwiningModerateGrowthStatement` with a matrix embedding of positive size, the threshold of
the global Eisenstein majorant works: for every parameter beyond it, `M(w, λ)φ` has moderate
growth for the adelic norm of `rho`. For size zero the adelic points are trivial and the proof
takes the threshold `0`. -/
theorem intertwiningModerateGrowth : IntertwiningModerateGrowthStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hπ hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have := subsingleton_adelicGroupPoints_of_closed_zeroMatrix rho hrho
    refine ⟨0, fun lam _ => ?_⟩
    refine ⟨‖hK.intertwiningOperator hK' iU l iV c π' w φ lam 1‖ + 1, by positivity, 0,
      fun g => ?_⟩
    rw [Subsingleton.elim g 1, Real.rpow_zero, mul_one]
    exact le_add_of_nonneg_right zero_le_one
  have hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ := hφ.1
  obtain ⟨R, hR⟩ := eisensteinGlobalMajorant F G P M U A p iU l a r hA hT hG hU hK rho hN hrho
    φ hinv hφ.2.2.2.2
  refine ⟨R, fun lam hlam => ?_⟩
  obtain ⟨b, e, hb, hb0, he, hbound⟩ := hR lam hlam
  have hcls : ∀ δ δ' : AdelicSubgroupPoints.rationalSubgroup F G
      (SubgroupFunctor.range (iV ≫ q)),
      intertwiningRationalCoset F p w δ = intertwiningRationalCoset F p w δ' →
      (δ' : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) *
        (δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))⁻¹ ∈
        intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w) := by
    intro δ δ' h
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hrel
    obtain ⟨z, -, hz⟩ := hrel
    exact mul_inv_mem_intertwiningRationalSubgroup r w hG hU hq hV hmul hw δ.2 δ'.2 ⟨z, hz⟩
  obtain ⟨B, hBint, hB0, hBbound⟩ := exists_integrable_unfolding_majorant hK (iV ≫ q) w rho hN
    hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
    (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w))
    (isDiscrete_intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w))
    hcls r.isCompatible.levi hU φ hinv lam b hb hb0 e he hbound
  let ν := intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)
  have hBμ : Integrable B ν := hBint
  let H := adelicHeight F G rho
  have hH (g : AdelicGroupPoints F G) : 1 ≤ H g := one_le_adelicHeight F G rho hN g
  have hI (g : AdelicGroupPoints F G) :
      ‖hK.intertwiningIntegral iU (iV ≫ q) w φ lam g‖ ≤ (∫ x, B x ∂ν) * H g ^ e := by
    calc ‖hK.intertwiningIntegral iU (iV ≫ q) w φ lam g‖
        ≤ ∫ x, B x * H g ^ e ∂ν :=
          norm_integral_le_of_norm_le (hBμ.mul_const _)
            (Filter.Eventually.of_forall fun x => hBbound x g)
      _ = (∫ x, B x ∂ν) * H g ^ e := integral_mul_const _ _
  obtain ⟨C, e', hC, he', hheight⟩ :=
    hK'.exists_norm_heightPower_le_adelicHeight rho hN hrho (-weylParameter l c π' lam)
  have hint0 : 0 ≤ ∫ x, B x ∂ν := integral_nonneg hB0
  let s : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hs : 0 < s := pow_pos (Nat.cast_pos.mpr hN) _
  let K₀ : ℝ := C * (∫ x, B x ∂ν)
  have hK₀ : 0 ≤ K₀ := mul_nonneg hC.le hint0
  refine ⟨K₀ * s ^ (e' + e) + 1, by positivity, e' + e, fun g => ?_⟩
  have hsN : 0 < adelicSourceNorm F G rho g := adelicSourceNorm_pos F G rho hN g
  have hHs : H g = s * adelicSourceNorm F G rho g := adelicHeight_eq_scalar_mul_sourceNorm F G rho g
  have hHpos : 0 < H g := zero_lt_one.trans_le (hH g)
  have hmain : ‖hK.intertwiningOperator hK' iU l iV c π' w φ lam g‖ ≤ K₀ * H g ^ (e' + e) := by
    unfold IsIwasawaCompact.intertwiningOperator
    rw [norm_mul, Real.rpow_add hHpos]
    calc ‖hK'.heightPower (-weylParameter l c π' lam) g‖ *
          ‖hK.intertwiningIntegral iU (iV ≫ q) w φ lam g‖
        ≤ (C * H g ^ e') * ((∫ x, B x ∂ν) * H g ^ e) :=
          mul_le_mul (hheight g) (hI g) (norm_nonneg _)
            (mul_nonneg hC.le (Real.rpow_nonneg hHpos.le _))
      _ = K₀ * (H g ^ e' * H g ^ e) := by ring
  calc ‖hK.intertwiningOperator hK' iU l iV c π' w φ lam g‖
      ≤ K₀ * H g ^ (e' + e) := hmain
    _ = K₀ * s ^ (e' + e) * adelicSourceNorm F G rho g ^ (e' + e) := by
      rw [hHs, Real.mul_rpow hs.le hsN.le]
      ring
    _ ≤ (K₀ * s ^ (e' + e) + 1) * adelicSourceNorm F G rho g ^ (e' + e) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg hsN.le _)

end Langlands.Global
