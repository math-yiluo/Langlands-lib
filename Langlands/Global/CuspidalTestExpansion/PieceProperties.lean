import Langlands.Global.CuspidalTestExpansion.StabilizerInvariance
import Langlands.Global.CuspidalTestExpansion.IntertwiningInvariance
import Langlands.Global.AdelicBruhatIntertwiningIdentification
import Langlands.Global.AdelicEisensteinStabilizerContinuity
import Langlands.Global.AdelicEisensteinUnfoldingGlobalMajorant
import Langlands.Global.AdelicStandardBruhatPiece
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Continuity, bounds and invariance of the intertwining integral of a Bruhat piece -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  RepresentationGrowth EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

variable {I J I₁ J₁ : StandardIndex F G fam.i fam.ν} {n : normalizerPoints fam.i}

instance instClosedSourcePiece (pc : StandardBruhatPiece fam I J I₁ J₁ n) :
    IsClosedImmersion (pc.source.inclusion ≫ fam.p I).hom.hom.left := by
  rw [pc.source.inclusion_comp]
  exact (fam.isCompatible I₁).parabolic.isClosedSubgroup

instance instClosedSourceRadicalPiece (pc : StandardBruhatPiece fam I J I₁ J₁ n) :
    IsClosedImmersion (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I).hom.hom.left := by
  rw [pc.source.inclusion_comp]
  exact fam.closedU I₁

instance instClosedTargetRadicalPiece (pc : StandardBruhatPiece fam I J I₁ J₁ n) :
    IsClosedImmersion (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J).hom.hom.left := by
  rw [pc.target.inclusion_comp]
  exact fam.closedU J₁

/-- The twist `φ_λ` of a function on `U_I(𝔸)M_I(F) \ G(𝔸)` is left invariant under `U_I(𝔸)` and
`P_I(F)`. -/
theorem parameterTwist_isLeftInvariant [IsClosedImmersion (fam.p I).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p I) K)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) (fam.iU I))
        (hK.parameterTwist φ lam) ∧
      IsLeftInvariantUnder F G (rationalImage F (fam.p I)) (hK.parameterTwist φ lam) := by
  constructor
  · rintro _ ⟨y, rfl⟩ x
    have hu : map F (fam.U I) G (fam.iU I ≫ fam.p I) y ∈
        parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I) :=
      Subgroup.mem_sup_left ⟨y, rfl⟩
    change φ (map F (fam.U I) G (fam.iU I ≫ fam.p I) y * x) *
        hK.heightPower lam (map F (fam.U I) G (fam.iU I ≫ fam.p I) y * x) =
      φ x * hK.heightPower lam x
    rw [hφ _ hu x, hK.heightPower_unipotent_mul (fam.isUnipotentRadical I).1.isUnipotent]
  · rintro _ ⟨y, rfl⟩ x
    have hz : map F (fam.P I) G (fam.p I) (rational F (fam.P I) y) ∈
        parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I) :=
      rationalImage_le_parabolicQuotientSubgroup (fam.p I) (fam.iU I) (fam.l I)
        (fam.isCompatible I).levi (fam.isUnipotentRadical I) ⟨y, rfl⟩
    change φ (map F (fam.P I) G (fam.p I) (rational F (fam.P I) y) * x) *
        hK.heightPower lam (map F (fam.P I) G (fam.p I) (rational F (fam.P I) y) * x) =
      φ x * hK.heightPower lam x
    rw [hφ _ hz x, hK.heightPower_rational_mul]

set_option maxHeartbeats 4000000 in
/-- Assume `GeometricLemmaUnfoldingStatement` and `0 < N`, and let `φ` be continuous and left
invariant under `U_I(𝔸) M_I(F)`, with a summable nonnegative majorant
`‖φ_λ(γ_c g)‖ ≤ b c · H(g)^d` (`d ≥ 0`) of the Eisenstein terms over `P_I(F) \ G(F)`. Then the
intertwining integral of a Bruhat piece converges at every argument, equals the unfolded
stabilizer integral, is continuous, has a polynomial bound `C · H(y)^d` in the matrix height,
and is left invariant under the rational points of the target parabolic `P_{J₁}` of the
piece. -/
theorem pieceIntegral_properties (hGLU : GeometricLemmaUnfoldingStatement.{u})
    [IsClosedImmersion (fam.p I).hom.hom.left]
    (pc : StandardBruhatPiece fam I J I₁ J₁ n) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p I) K) (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) φ)
    (lam : ComplexCharacterParameter F (fam.P I))
    (b : ParabolicRationalCosets F (fam.p I) → ℝ) (d : ℝ) (hb : Summable b)
    (hb0 : ∀ x, 0 ≤ b x) (hd : 0 ≤ d)
    (hbound : ∀ g x, ‖hK.eisensteinTerm φ lam g x‖ ≤ b x * adelicHeight F G rho g ^ d) :
    let Pint : AdelicGroupPoints F G → ℂ := fun y =>
      hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) y
    (∀ y, Integrable (hK₁.intertwiningIntegrand (fam.iU I₁)
        (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) y)
      (intertwiningMeasure F (pc.source.inclusion ≫ fam.p I) (fam.iU I₁)
        (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) (innerAdelicPoint F G n.val))) ∧
    (∀ y, Pint y = stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) (innerAdelicPoint F G n.val)
      (hK.parameterTwist φ lam) y) ∧
    Continuous Pint ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖Pint y‖ ≤ C * adelicHeight F G rho y ^ d) ∧
    IsLeftInvariantUnder F G (rationalImage F (pc.target.inclusion ≫ fam.p J)) Pint := by
  intro Pint
  have hVr := (fam.isUnipotentRadical J).1
  have : IsAffineHom (fam.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (fam.iU J ≫ fam.p J)
      hVr.smooth hVr.connectedSpace hVr.isUnipotent
  set Φ := hK.parameterTwist φ lam with hΦdef
  obtain ⟨hΦU, hΦP⟩ := fam.parameterTwist_isLeftInvariant hK hφ lam
  have hΦc : Continuous Φ := hK.continuous_parameterTwist hφc lam
  set wA := innerAdelicPoint F G n.val with hwA
  obtain ⟨B, hBint, hB0, hBbd⟩ := eisensteinUnfoldingGlobalMajorant hK (fam.iU J ≫ fam.p J) n.val
    rho (iU := fam.iU I) (l := fam.l I) hN hVr.smooth hVr.connectedSpace hVr.isUnipotent
    (fam.isCompatible I).levi (fam.isUnipotentRadical I) φ hφ lam b d hb hb0 hd hbound
  have hSbd : ∀ v g, ‖eisensteinStabilizerIntegrand (fam.p I) (fam.p J) (fam.iU J) wA Φ g v‖ ≤
      B v * adelicHeight F G rho g ^ d := fun v g => hBbd v g
  obtain ⟨hSint, hScont⟩ := eisensteinStabilizerContinuity (fam.p I) (fam.p J) (fam.iU J) wA rho
    hN Φ hΦc hΦP B d hBint hB0 hd hSbd
  have hident (y : AdelicGroupPoints F G) := bruhatIntertwiningIdentification (fam.p I) (fam.iU I)
    (fam.p J) (fam.iU J) n.val pc.source.inclusion (fam.iU I₁) pc.target.inclusion (fam.iU J₁) hK hK₁
    hGLU fam.connectedReductive (fam.isCompatible I).parabolic (fam.isUnipotentRadical I)
    (fam.isCompatible J).parabolic (fam.isUnipotentRadical J)
    (by rw [pc.source.inclusion_comp]; exact (fam.isCompatible I₁).parabolic)
    (fam.isUnipotentRadical I₁)
    (by rw [pc.target.inclusion_comp]; exact (fam.isCompatible J₁).parabolic)
    (fam.isUnipotentRadical J₁) pc.geometry φ lam hΦc.measurable hΦU hΦP y (hSint y)
  have hPint : ∀ y, Pint y = stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) wA Φ y :=
    fun y => (hident y).2.1
  refine ⟨fun y => (hident y).1, hPint, ?_, ?_, ?_⟩
  · have : Pint = stabilizerIntegral (fam.p I) (fam.p J) (fam.iU J) wA Φ := funext hPint
    rw [this]
    exact hScont
  · refine ⟨∫ v, B v ∂stabilizerMeasure F (fam.p I) (fam.iU J ≫ fam.p J) wA,
      integral_nonneg hB0, fun y => ?_⟩
    rw [hPint y, stabilizerIntegral, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hBint.mul_const _)
      (Filter.Eventually.of_forall fun v => hSbd v y)
  · have hinv := stabilizerIntegral_isLeftInvariantUnder (fam.p I) (fam.p J) (fam.iU J)
      hVr.isNormal wA Φ hΦP
    rw [← pc.geometry.rationalImage_right] at hinv
    intro x hx y
    rw [hPint, hPint]
    exact hinv x hx y

/-- If the constant term `C_{I₁} φ` is left invariant under `U_{I₁}(𝔸)`, the intertwining
integral of a Bruhat piece is left invariant under the adelic points of the radical of the
target parabolic `P_{J₁}`. -/
theorem pieceIntegral_radical_invariant [IsClosedImmersion (fam.p I).hom.hom.left]
    (pc : StandardBruhatPiece fam I J I₁ J₁ n) {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K) (φ : AdelicGroupPoints F G → ℂ)
    (hCT : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁))
      (fam.constantTerm I₁ φ))
    (lam : ComplexCharacterParameter F (fam.P I))
    (u : AdelicGroupPoints F G)
    (hu : u ∈ AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J)))
    (y : AdelicGroupPoints F G) :
    hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) (u * y) =
      hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val
        (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
        (parameterRestrict pc.source.inclusion lam) y := by
  have hVr := (fam.isUnipotentRadical J₁).1
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (SubgroupFunctor.range (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J))) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
      (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) hVr.smooth hVr.connectedSpace hVr.isUnipotent
  have hφ' : IsLeftInvariantUnder F G
      (parabolicUnipotentImage F (pc.source.inclusion ≫ fam.p I) (fam.iU I₁))
      (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ) := by
    have e1 : subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ =
        fam.constantTerm I₁ φ := funext fun g =>
      subgroupConstantTerm_eq_of_range_eq _ _ (by rw [pc.source.inclusion_comp]) φ g
    have e2 : parabolicUnipotentImage F (pc.source.inclusion ≫ fam.p I) (fam.iU I₁) =
        parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁) := by
      rw [pc.source.inclusion_comp]
    rw [e1, e2]
    exact hCT
  exact hK₁.intertwiningIntegral_adelicPoints_mul (fam.iU I₁)
    (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J) n.val (fam.isUnipotentRadical I₁).1.isUnipotent
    hφ' (parameterRestrict pc.source.inclusion lam) ⟨u, hu⟩ y

end Langlands.Global.StandardParabolicFamily
