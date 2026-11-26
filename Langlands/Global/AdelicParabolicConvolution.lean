import Langlands.Global.AdelicConstantTermComposition
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicStandardConstantTermTwist
import Langlands.Global.AdelicTwistedConvolution

/-! # Compact convolution on moderate functions and their radical constant terms -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)

/-- Right convolution preserves left invariance under any subgroup. -/
theorem rightConvolution_isLeftInvariantUnder {Γ : Subgroup A} {h f : A → ℂ}
    (hf : IsLeftInvariantUnder F G Γ f) :
    IsLeftInvariantUnder F G Γ (rightConvolution F G h f) := by
  intro x hx g
  unfold rightConvolution
  simp_rw [mul_assoc, hf x hx]

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {Kout : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p Kout)

/-- After cancelling the Iwasawa twist, compact right convolution preserves polynomial
height growth at every fixed complex parameter. -/
theorem IsIwasawaCompact.hasHeightGrowth_twistedConvolutionEnd {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {h : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F P)
    {f : C(A, ℂ)} (hf : HasHeightGrowth rho f) :
    HasHeightGrowth rho (hK.twistedConvolutionEnd hsmooth hh lam f) := by
  obtain ⟨C, r, hC, hr, hBound⟩ := hf
  let H := adelicHeight F G rho
  have hH (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  obtain ⟨D, hD⟩ := (hh.2.1.isCompact.image (continuous_adelicHeight F G rho hN)).bddAbove
  obtain ⟨B, hB⟩ := ((hK.isCompact.mul hh.2.1.isCompact).exists_bound_of_continuousOn
    (hK.continuous_heightPower lam).continuousOn)
  have hfactor (x t : A) (ht : t ∈ tsupport h) :
      ‖hK.heightPower lam (x * t) / hK.heightPower lam x‖ ≤ max 0 B := by
    obtain ⟨k, hk, heq⟩ := hK.exists_height_mul_eq_add x t
    have hpow : hK.heightPower lam (x * t) =
        hK.heightPower lam x * hK.heightPower lam (k * t) := by
      simp only [IsIwasawaCompact.heightPower, heq, map_add, Complex.exp_add]
    rw [hpow, mul_div_cancel_left₀ _ (hK.heightPower_ne_zero lam x)]
    exact (hB _ ⟨k, hk, t, ht, rfl⟩).trans (le_max_right _ _)
  let L := C * (max 1 D) ^ r * max 0 B
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hi : Integrable (fun t => ‖h t‖) dg :=
    hh.1.1.norm.integrable_of_hasCompactSupport hh.2.1.norm
  refine ⟨L * (∫ t, ‖h t‖ ∂dg), r, mul_nonneg hL (integral_nonneg fun _ => norm_nonneg _), hr,
    fun x => ?_⟩
  rw [IsIwasawaCompact.twistedConvolutionEnd_apply, rightConvolution, ← integral_div]
  calc
    _ ≤ ∫ t, (L * H x ^ r) * ‖h t‖ ∂dg := by
      apply norm_integral_le_of_norm_le (hi.const_mul (L * H x ^ r))
      apply Filter.Eventually.of_forall
      intro t
      by_cases ht : t ∈ tsupport h
      · have hHt : H t ≤ max 1 D :=
          (hD (show H t ∈ H '' tsupport h from ⟨t, ht, rfl⟩)).trans (le_max_right _ _)
        have hxt : H (x * t) ^ r ≤ H x ^ r * (max 1 D) ^ r := by
          rw [← Real.mul_rpow (by linarith [hH x]) (by positivity)]
          exact Real.rpow_le_rpow (by linarith [hH (x * t)])
            ((adelicHeight_mul_le F G rho hN x t).trans
              (mul_le_mul_of_nonneg_left hHt (by linarith [hH x]))) hr
        have hft := (hBound (x * t)).trans (mul_le_mul_of_nonneg_left hxt hC)
        have heq :
            h t * hK.parameterTwist f lam (x * t) / hK.heightPower lam x =
              (h t * f (x * t)) * (hK.heightPower lam (x * t) / hK.heightPower lam x) := by
          simp only [IsIwasawaCompact.parameterTwist, div_eq_mul_inv, mul_assoc]
        rw [heq, norm_mul, norm_mul]
        calc
          _ ≤ (‖h t‖ * (C * (H x ^ r * (max 1 D) ^ r))) * max 0 B :=
            mul_le_mul (mul_le_mul_of_nonneg_left hft (norm_nonneg _))
              (hfactor x t ht) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (mul_nonneg hC
                (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hH x)) _)
                  (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _))))
          _ = (L * H x ^ r) * ‖h t‖ := by dsimp [L]; ring
      · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul, zero_div, norm_zero, mul_zero]
    _ = _ := by rw [integral_const_mul]; ring

omit [LocallyOfFiniteType G.X.hom] in
/-- The height power is invariant under the subgroup defining the parabolic quotient. -/
theorem IsIwasawaCompact.heightPower_isLeftInvariantUnder_parabolicQuotient
    {U M : GroupScheme (Spec (CommRingCat.of F))} (iU : U ⟶ P) (l : M ⟶ P)
    (hU : IsUnipotent U) (lam : ComplexCharacterParameter F P) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (hK.heightPower lam) := by
  have hsub : parabolicQuotientSubgroup F p iU l ≤
      StandardParabolicFamily.scalarLeftStabilizer (hK.heightPower lam) := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      change ∀ g, hK.heightPower lam (map F U G (iU ≫ p) x * g) = hK.heightPower lam g
      intro g
      exact hK.heightPower_unipotent_mul hU iU lam x g
    · rintro _ ⟨x, rfl⟩
      change ∀ g, hK.heightPower lam (map F M G (l ≫ p) (rational F M x) * g) =
        hK.heightPower lam g
      intro g
      rw [← map_rational_affinePointsTarget l p]
      exact hK.heightPower_rational_mul lam _ g
  intro x hx g
  exact hsub hx g

omit [LocallyOfFiniteType G.X.hom] in
/-- Iwasawa twisting retains the inducing left invariance. -/
theorem IsIwasawaCompact.parameterTwist_isLeftInvariantUnder_parabolicQuotient
    {U M : GroupScheme (Spec (CommRingCat.of F))} (iU : U ⟶ P) (l : M ⟶ P)
    (hU : IsUnipotent U) (lam : ComplexCharacterParameter F P) {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) f) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) (hK.parameterTwist f lam) := by
  intro x hx g
  simp only [IsIwasawaCompact.parameterTwist, hf x hx,
    hK.heightPower_isLeftInvariantUnder_parabolicQuotient iU l hU lam x hx g]

/-- Convolution transported through the height twist preserves invariance under the subgroup
defining the parabolic quotient. -/
theorem IsIwasawaCompact.isLeftInvariantUnder_twistedConvolutionEnd {d : ℕ}
    {U M : GroupScheme (Spec (CommRingCat.of F))} (iU : U ⟶ P) (l : M ⟶ P)
    (hU : IsUnipotent U) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F P)
    {f : C(A, ℂ)} (hf : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) f) :
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l)
      (hK.twistedConvolutionEnd hsmooth hh lam f) := by
  have hp := hK.heightPower_isLeftInvariantUnder_parabolicQuotient iU l hU lam
  have hf' := hK.parameterTwist_isLeftInvariantUnder_parabolicQuotient iU l hU lam hf
  intro x hx g
  simp only [IsIwasawaCompact.twistedConvolutionEnd_apply]
  have hconv := rightConvolution_isLeftInvariantUnder (h := h) hf'
  exact congrArg₂ (· / ·) (hconv x hx g) (hp x hx g)

section ConstantTerm

open Langlands.Global.AdelicSubgroupPoints Langlands.Global.ConstantTermComposition

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left] (j : U ⟶ G)
  [IsClosedImmersion j.hom.hom.left]

local notation "V" => SubgroupFunctor.range j
local notation "Vₐ" => adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "ν" => normalizedRationalQuotientHaarMeasure F G V

/-- The compact radical constant term commutes with right convolution by a continuous
compactly supported kernel. Joint continuity is checked on the quotient. -/
theorem subgroupConstantTerm_rightConvolution [CompactSpace Q] {h f : A → ℂ}
    (hh : Continuous h) (hs : HasCompactSupport h) (hf : Continuous f)
    (hinv : IsRationalInvariant F G V f) :
    subgroupConstantTerm F j (rightConvolution F G h f) =
      rightConvolution F G h (subgroupConstantTerm F j f) := by
  let := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let T (x : A) (z : Q × A) := h z.2 * descendedIntegrand hinv (x * z.2) z.1
  have hcont (x : A) : Continuous (T x) := by
    rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap
      (IsOpenQuotientMap.id (X := A))).continuous_comp_iff]
    change Continuous (fun z : Vₐ × A => h z.2 * f (z.1.val * (x * z.2)))
    exact (hh.comp continuous_snd).mul (hf.comp
      ((continuous_subtype_val.comp continuous_fst).mul (continuous_const.mul continuous_snd)))
  have hcompact (x : A) : HasCompactSupport (T x) := by
    refine (isCompact_univ.prod hs.isCompact).of_isClosed_subset isClosed_closure
      (closure_minimal ?_ (isClosed_univ.prod isClosed_closure))
    intro z hz
    exact ⟨Set.mem_univ _, subset_tsupport _ (left_ne_zero_of_mul (by exact hz))⟩
  funext x
  unfold subgroupConstantTerm rightConvolution
  simp_rw [mul_assoc, ← integral_const_mul, ← descendedIntegrand_out hinv]
  exact integral_integral_swap_of_hasCompactSupport (hcont x) (hcompact x)

end ConstantTerm

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.StandardParabolicFamily

open AdelicGroupPoints AdelicSubgroupPoints ConstantTermComposition
open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G

/-- Invariance on a parabolic quotient supplies the hypotheses for commuting every smaller
standard constant term with compact right convolution. -/
theorem constantTerm_rightConvolution {P Q : Idx} (hQP : Q ≤ P)
    {h f : A → ℂ} (hh : Continuous h) (hs : HasCompactSupport h) (hf : Continuous f)
    (hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)) f) :
    fam.constantTerm Q (rightConvolution F G h f) =
      rightConvolution F G h (fam.constantTerm Q f) := by
  let V := SubgroupFunctor.range (fam.iU Q ≫ fam.p Q)
  let := fam.compactSpace_radicalRationalQuotient Q
  let : IsClosedImmersion (fam.p P).hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  have hle : V ≤ SubgroupFunctor.range (fam.p P) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((fam.le_iff_range_le Q P).mp hQP)
  let j := SubgroupFunctor.rangeFactor (fam.iU Q ≫ fam.p Q) (fam.p P) hle
  have hj : j ≫ fam.p P = fam.iU Q ≫ fam.p Q := SubgroupFunctor.rangeFactor_comp _ _ hle
  apply subgroupConstantTerm_rightConvolution (fam.iU Q ≫ fam.p Q) hh hs hf
  intro v hv x
  let y : A := v.val
  have hv' : y ∈ rationalImage F (fam.iU Q ≫ fam.p Q) :=
    (mem_rationalSubgroup_range_iff _ v).mp hv
  rw [← hj] at hv'
  exact hinv _ ((rationalImage_comp_le j _).trans (rationalImage_le_parabolicQuotientSubgroup
    _ _ _ (fam.isCompatible P).levi (fam.isUnipotentRadical P)) hv') x

/-- Each nested constant term intertwines convolution transported through the outer twist. -/
theorem constantTerm_twistedConvolutionEnd {P Q : Idx}
    [IsClosedImmersion (fam.p P).hom.hom.left] (hQP : Q ≤ P)
    {Kout : Subgroup A} (hK : IsIwasawaCompact (fam.p P) Kout)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F (fam.P P))
    {f : C(A, ℂ)}
    (hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p P) (fam.iU P) (fam.l P)) f) :
    fam.constantTerm Q (hK.twistedConvolutionEnd hsmooth hh lam f) =
      hK.parameterTwist (rightConvolution F G h (hK.parameterTwist (fam.constantTerm Q f) lam))
        (-lam) := by
  have hop : (hK.twistedConvolutionEnd hsmooth hh lam f : A → ℂ) =
      hK.parameterTwist (rightConvolution F G h (hK.parameterTwist f lam)) (-lam) := by
    funext x
    simp only [IsIwasawaCompact.twistedConvolutionEnd_apply, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, Complex.exp_neg, div_eq_mul_inv]
  have hinv' := hK.parameterTwist_isLeftInvariantUnder_parabolicQuotient
    (fam.iU P) (fam.l P) (fam.isUnipotentRadical P).1.isUnipotent lam hinv
  rw [hop, fam.constantTerm_parameterTwist P Q hK hQP,
    fam.constantTerm_rightConvolution hQP hh.1.1 hh.2.1
      (hK.continuous_parameterTwist f.continuous lam) hinv',
    fam.constantTerm_parameterTwist P Q hK hQP]

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- Convolution transported through the outer twist preserves moderate growth and parabolic
invariance, and acts on nested constant terms by the same transported convolution formula. -/
def ParabolicTwistedConvolutionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p P).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact (fam.p P) K),
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
      ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (h : AdelicGroupPoints F G → ℂ) (hh : IsAdelicTestFunction F G h)
        (lam : ComplexCharacterParameter F (fam.P P))
        (f : C(AdelicGroupPoints F G, ℂ)),
        fam.IsModerateContinuousOnParabolic rho P f →
        let v := hK.twistedConvolutionEnd hsmooth hh lam f
        fam.IsModerateContinuousOnParabolic rho P v ∧
          ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ P →
            fam.constantTerm Q v =
              hK.parameterTwist
                (rightConvolution F G h (hK.parameterTwist (fam.constantTerm Q f) lam)) (-lam)

theorem parabolicTwistedConvolution : ParabolicTwistedConvolutionStatement.{u} := by
  intro F _ _ G _ _ _ fam P _ K hK N d rho hN hsmooth h hh lam f hf
  let v := hK.twistedConvolutionEnd hsmooth hh lam f
  refine ⟨⟨?_, v.continuous, ?_⟩, fun Q hQP => ?_⟩
  · exact hK.isLeftInvariantUnder_twistedConvolutionEnd (fam.iU P) (fam.l P)
      (fam.isUnipotentRadical P).1.isUnipotent hsmooth hh lam hf.1
  · exact (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).2
      (hK.hasHeightGrowth_twistedConvolutionEnd rho hN hsmooth hh lam
        ((hasModerateGrowthFunction_iff_hasHeightGrowth hN _).1 hf.2.2))
  · exact fam.constantTerm_twistedConvolutionEnd hQP hK hsmooth hh lam hf.1

end Langlands.Global
