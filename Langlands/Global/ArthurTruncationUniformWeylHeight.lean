import Langlands.Global.ArthurWeylHeightOrbit

/-! # The uniform fundamental-weight bound for Weyl height displacement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints ArthurParabolicSpaces

/-- The Weyl height comparison with one uniform additive error for the specified
lift, weight and compact Iwasawa subgroup. -/
theorem exists_weylHeight_lowerBound
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
    [Mono i.hom.hom.left] {ν : cocharacterLattice T}
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) (β : SimpleRoot i ν)
    (weight : Vstar T) (hweight : D.IsRealFundamentalWeight ν β weight)
    (n : normalizerPoints i) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν ∅)))
        (x : AdelicGroupPoints F G),
        pair T weight (height hi hK hρ x) ≤
          pair T (relativeWeylFullRealAction i (QuotientGroup.mk n) weight)
            (height hi hK hρ (innerAdelicPoint F G n.val * (v : AdelicGroupPoints F G) * x)) + B := by
  obtain ⟨d, j, ρ, hp, c, ζ, hc, hline⟩ := exists_minimalParabolic_line_weight hG hi hν D β weight hweight
  let p₀ := Standard.parabolicHom i ν ∅
  let j₀ := torusToParabolic F i ν ∅
  let χ₁ := (ρ.restrict p₀).coordinateLineRationalCharacter j hp
  let w : relativeWeylGroup i := QuotientGroup.mk n
  let W := relativeWeylFullRealAction i w
  let χ := rationalCharacterRestrictReal i ζ
  obtain ⟨χ₂, B, hB, hχ₂, hbound⟩ := exists_weylLineHeight_bound hG hi hν hK ρ j hp n
  have heq₁ : ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ χ₁ : Vstar T) = c • weight + χ := hline
  have heq₂ : ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ χ₂ : Vstar T) = c • W weight + χ := by
    have he := congrArg W heq₁
    change relativeWeylFullRealAction i w ((1 : ℝ) ⊗ₜ[ℤ] torusCharacterRestrict j₀ χ₁) =
      W (c • weight + χ) at he
    rw [relativeWeylFullRealAction_tmul, relativeWeylLatticeAction_mk, ← hχ₂, map_add, map_smul,
      show W χ = χ from relativeWeylFullRealAction_restrictionRange i w ζ] at he
    exact he
  refine ⟨B / c, div_nonneg hB hc.le, fun v x => ?_⟩
  let H := height hi hK hρ
  let y := innerAdelicPoint F G n.val * (v : AdelicGroupPoints F G) * x
  have hb : hK.height x χ₁ ≤ hK.height y χ₂ + B := hbound v x
  rw [← height_pair_character hi hK hρ χ₁ x, ← height_pair_character hi hK hρ χ₂ y, heq₁, heq₂] at hb
  have hζ : pair T χ (H y) = pair T χ (H x) :=
    ambientCharacter_pair_height_innerAdelicPoint_mul hG hi hν hK hρ ζ n v x
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
  change c * pair T weight (H x) + pair T χ (H x) ≤
    c * pair T (W weight) (H y) + pair T χ (H y) + B at hb
  rw [hζ] at hb
  have hdiff : (pair T weight (H x) - pair T (W weight) (H y)) * c ≤ B := by
    rw [sub_mul]
    linarith only [show pair T weight (H x) * c + pair T χ (H x) ≤
        pair T (W weight) (H y) * c + pair T χ (H x) + B by
      simpa only [mul_comm c] using hb]
  change pair T weight (H x) ≤ pair T (W weight) (H y) + B / c
  linarith only [(le_div_iff₀ hc).mpr hdiff]

end Langlands.Global.ArthurTruncation.Idempotence
