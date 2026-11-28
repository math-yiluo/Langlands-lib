import Langlands.Global.AdelicEisensteinWeakBruhatConstantTerm
import Langlands.Global.AdelicRelativeEisensteinShifts
import Langlands.Global.AdelicIntertwiningLeviHaarBalance
import Langlands.Global.AdelicIntertwiningLeftInvariance
import Langlands.Global.AdelicParameterTwistAutomorphyReduction
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof
import Langlands.Global.AdelicEisensteinStandardizationReduction
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.CuspidalTestExpansion.FullPiece

/-! # The normalized Weyl character of a full-source Bruhat summand -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints PositiveRealTorus Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "QuotSub" J =>
  parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)

attribute [local instance] isClosedImmersion_p closedU

set_option maxHeartbeats 2000000 in
/-- The unnormalized intertwiner from an inducing section with trivial split character
has the transported Weyl character after removing the target half modulus. -/
theorem intertwiningIntegral_splitCharacter {I L : Idx}
    {n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : fam.M L ⟶ fam.M I}
    (hw : IsWeylConjugation (fam.p I) (fam.l I) (fam.p L) (fam.l L) n c)
    (πL : fam.P L ⟶ fam.M L) (hπ : fam.l L ≫ πL = 𝟙 (fam.M L))
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKL : IsIwasawaCompact (fam.p L) K)
    {φ : Fun} (hc : Continuous φ) (hφ : IsLeftInvariantUnder F G (QuotSub I) φ)
    (heq : IsSplitComponentEquivariant (fam.p I) (fam.l I) φ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    let W := hKI.intertwiningIntegral (fam.iU I) (fam.iU L ≫ fam.p L) n φ lam
    IsLeftInvariantUnder F G (QuotSub L) W ∧
      ∀ b : fam.positiveSplitComponent L,
        fam.unnormalizedAction L b.val W =
          (fam.halfModulus L b.val * parameterPower F (fam.P L)
            (weylParameter (fam.l I) c πL lam) b.val) • W := by
  let hU := fam.isUnipotentRadical I
  let hV := fam.isUnipotentRadical L
  let : IsAffineHom (fam.U L).X.hom := hV.1.isClosedSubgroup.isAffineHom
  let : LocallyOfFiniteType (fam.U L).X.hom := hV.1.isClosedSubgroup.locallyOfFiniteType
  let u := fam.iU I
  let v := fam.iU L
  let W := hKI.intertwiningIntegral u (v ≫ fam.p L) n φ lam
  let lamL := weylParameter (fam.l I) c πL lam
  let A := hKI.intertwiningOperator hKL u (fam.l I) v c πL n φ lam
  have hW : W = hKL.parameterTwist A lamL := by
    funext g
    have hc₁ : hKL.heightPower (-lamL) g * hKL.heightPower lamL g = 1 := by
      simp only [IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply,
        ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    change W g = (hKL.heightPower (-lamL) g * W g) * hKL.heightPower lamL g
    rw [mul_right_comm, hc₁, one_mul]
  have hInvA : IsLeftInvariantUnder F G (QuotSub L) A :=
    hKI.intertwiningOperator_leftInvariant u v πL hKL hU hV hφ lam hw (fam.isCompatible I).levi
  have huInv : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I) u) φ :=
    fun x hx => hφ x (Subgroup.mem_sup_left hx)
  have hA : IsSplitComponentEquivariant (fam.p L) (fam.l L) A :=
    hKI.intertwiningOperator_splitComponentEquivariant u v hw hU.1.isNormal hV.1.isNormal
      (fam.closedU I) hV.1.isUnipotent hKL hπ hV.1.smooth hV.1.connectedSpace hU.1.isUnipotent
      hc huInv heq lam (fun m _ => intertwiningLeviHaarBalance_of_parabolics fam.connectedReductive
        (fam.isCompatible I).parabolic hU (fam.isCompatible I).levi
        (fam.isCompatible L).parabolic hV (fam.isCompatible L).levi hw m)
  change IsLeftInvariantUnder F G (QuotSub L) W ∧
    ∀ b : fam.positiveSplitComponent L, fam.unnormalizedAction L b.val W =
      (fam.halfModulus L b.val * parameterPower F (fam.P L) lamL b.val) • W
  rw [hW]
  refine ⟨hKL.isLeftInvariantUnder_parameterTwist v (fam.l L) hV.1.isUnipotent hInvA lamL, ?_⟩
  intro b
  funext g
  obtain ⟨a, ha, hab⟩ := b.property
  let m := map F (fam.A L).toGrp (fam.M L) (fam.a L) a
  have hm : m ∈ RestrictionSplitCentre.canonicalSubgroup F (fam.M L) := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible L).splitComponent]
    exact ⟨a, ha, rfl⟩
  have hb : map F (fam.M L) (fam.P L) (fam.l L) m = b.val := by
    rw [← map_comp_apply_of_hom]
    exact hab
  have hα := hA m hm g
  rw [hb] at hα
  change A (map F (fam.P L) G (fam.p L) b.val * g) *
      hKL.heightPower lamL (map F (fam.P L) G (fam.p L) b.val * g) =
    (fam.halfModulus L b.val * parameterPower F (fam.P L) lamL b.val) *
      (A g * hKL.heightPower lamL g)
  rw [hα, hKL.heightPower_map_mul]
  change (fam.halfModulus L b.val * A g) *
    (parameterPower F (fam.P L) lamL b.val * hKL.heightPower lamL g) = _
  ac_rfl

private theorem constantTerm_eq_of_unipotent_invariant (I : Idx) (φ : Fun)
    (hφ : IsLeftInvariantUnder F G (QuotSub I) φ) :
    subgroupConstantTerm F (fam.iU I ≫ fam.p I) φ = φ := by
  let U := SubgroupFunctor.range (fam.iU I ≫ fam.p I)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU I ≫ fam.p I)
  let := fam.compactSpace_radicalRationalQuotient I
  let dU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure dU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  funext g
  change (∫ x : AdelicSubgroupPoints.RationalQuotient F G U, φ (x.out.val * g) ∂dU) = φ g
  have h (x : AdelicSubgroupPoints.RationalQuotient F G U) : φ (x.out.val * g) = φ g :=
    hφ _ (Subgroup.mem_sup_left x.out.property) g
  simp only [h, integral_const, probReal_univ, one_smul]

set_option maxHeartbeats 1700000 in
private theorem fullSource_pieceIntegral {I J I₁ J₁ : Idx} {n : normalizerPoints fam.i}
    (pc : StandardBruhatPiece fam I J I₁ J₁ n) (hs : I₁ = I)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hK₁ : IsIwasawaCompact (pc.source.inclusion ≫ fam.p I) K)
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
    {φ : Fun} (hc : Continuous φ) (hφ : IsLeftInvariantUnder F G (QuotSub I) φ)
    (heq : IsSplitComponentEquivariant (fam.p I) (fam.l I) φ)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    let πL := ((fam.standardNestedLeviParabolic J₁ J₁ le_rfl).some).projection
    let lamL := weylParameter (fam.l I₁) pc.conjugation πL (parameterRestrict pc.source.inclusion lam)
    let W := hK₁.intertwiningIntegral (fam.iU I₁) (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J)
      n.val (subgroupConstantTerm F (fam.iU I₁ ≫ pc.source.inclusion ≫ fam.p I) φ)
      (parameterRestrict pc.source.inclusion lam)
    IsLeftInvariantUnder F G (QuotSub J₁) W ∧
      ∀ b : fam.positiveSplitComponent J₁,
        fam.unnormalizedAction J₁ b.val W =
          (fam.halfModulus J₁ b.val * parameterPower F (fam.P J₁) lamL b.val) • W := by
  subst I₁
  have hp : pc.source.inclusion ≫ fam.p I = fam.p I := pc.source.inclusion_comp
  have hinc : pc.source.inclusion = 𝟙 (fam.P I) := by
    apply ((fam.isCompatible I).parabolic.isClosedSubgroup.isRepresentedBy_range).hom_ext
    simpa only [Category.id_comp] using hp
  have ht : fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J = fam.iU J₁ ≫ fam.p J₁ := by
    rw [pc.target.inclusion_comp]
  let : IsClosedImmersion (fam.iU I ≫ pc.source.inclusion ≫ fam.p I).hom.hom.left := by
    rw [hp]
    exact fam.closedU I
  let : IsClosedImmersion (fam.iU J₁ ≫ pc.target.inclusion ≫ fam.p J).hom.hom.left := by
    rw [ht]
    exact fam.closedU J₁
  have hC : subgroupConstantTerm F (fam.iU I ≫ pc.source.inclusion ≫ fam.p I) φ = φ :=
    (subgroupConstantTerm_congr_hom (by rw [hp]) φ).trans
      (fam.constantTerm_eq_of_unipotent_invariant I φ hφ)
  let hI : IsIwasawaCompact (fam.p I) K := hK₁.of_range_eq (by rw [hp])
  let hL : IsIwasawaCompact (fam.p J₁) K :=
    ((pc.iwasawa K hKmin).2).of_range_eq (by rw [pc.target.inclusion_comp])
  let πL := ((fam.standardNestedLeviParabolic J₁ J₁ le_rfl).some).projection
  have hπ : fam.l J₁ ≫ πL = 𝟙 (fam.M J₁) :=
    ((fam.standardNestedLeviParabolic J₁ J₁ le_rfl).some).section_projection
  have hparam : parameterRestrict pc.source.inclusion lam = lam := by
    rw [hinc, parameterRestrict_id]
    rfl
  have hVal := (intertwining_congr_hom hp ht hK₁ hI (fam.iU I) n.val φ lam).1
  dsimp only
  rw [hC, hparam, hVal]
  exact fam.intertwiningIntegral_splitCharacter pc.weylLevi πL hπ hI hL hc hφ heq lam

namespace StandardBruhatConstantTermData

variable {fam}

/-- The relative Bruhat summand of a full-source piece has the normalized Weyl character
on the positive split component of the target. -/
def FullSourceBruhatCovarianceStatement {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K) : Prop :=
  ∀ w : b.FullSourceIndex, ∀ (φ : Fun), Continuous φ →
    IsLeftInvariantUnder F G (QuotSub I) φ →
    IsSplitComponentEquivariant (fam.p I) (fam.l I) φ →
    ∀ (lam : ComplexCharacterParameter F (fam.P I)) (a : fam.positiveSplitComponent J),
      fam.normalizedAction J a.val (b.summand hKmin w.val φ lam) =
        b.splitWeylCharacter w.val lam a • b.summand hKmin w.val φ lam

set_option maxHeartbeats 1800000 in
theorem fullSourceBruhatCovariance {I J : Idx} (b : fam.StandardBruhatConstantTermData I J)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K) :
    b.FullSourceBruhatCovarianceStatement hKmin := by
  intro w φ hc hφ heq lam a
  let pc := b.piece w.val
  let L := b.targetIndex w.val
  let hLJ : L ≤ J := b.targetIndex_le w.val
  let t := pc.target
  let W := b.intertwiningValue hKmin w.val φ lam
  let V := t.relativeEisensteinSeries W
  let aL := fam.splitLift hLJ a
  let χ := b.splitWeylCharacter w.val lam a
  obtain ⟨hInv, h⟩ := fam.fullSource_pieceIntegral pc w.property
    (b.sourceIwasawa hKmin w.val) hKmin hc hφ heq lam
  have hW : fam.unnormalizedAction J a.val W = (fam.halfModulus J a.val * χ) • W := by
    rw [← fam.unnormalizedAction_splitLift hLJ a]
    have hMod : fam.halfModulus L aL.val = fam.halfModulus J a.val :=
      standardNestedHalfModulusCompatibility F G fam L J hLJ a aL (fam.map_splitLift hLJ a)
    have hEq : fam.unnormalizedAction L aL.val W = (fam.halfModulus L aL.val * χ) • W := h aL
    rwa [hMod] at hEq
  have hInvW : IsLeftInvariantUnder F G (QuotSub L) W := hInv
  have hRel : fam.unnormalizedAction J a.val V = (fam.halfModulus J a.val * χ) • V := by
    rw [← (t.relativeEisensteinSeries_unnormalizedAction hLJ hInvW a).1, hW]
    funext g
    simp only [V, NestedLeviParabolic.relativeEisensteinSeries, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
  change fam.normalizedAction J a.val V = χ • V
  funext g
  change parameterPower F (fam.P J) (-halfModulusParameter F (fam.P J)) a.val *
      fam.unnormalizedAction J a.val V g = _
  rw [hRel, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    halfModulus, ← InducedInnerProductIntegrable.parameterPower_add, neg_add_cancel,
    InducedInnerProductIntegrable.parameterPower_zero, one_mul]

set_option maxHeartbeats 1500000 in
/-- The normalized Weyl character persists on the holomorphy domain of any continuation
of the full-source summand from the regular convergence chamber. -/
theorem fullSourceBruhatCovariance_of_continuation {I J : Idx}
    (b : fam.StandardBruhatConstantTermData I J) (w : b.FullSourceIndex)
    {K : Subgroup (AdelicGroupPoints F G)}
    (hKmin : IsIwasawaCompact (fam.p (fam.indexOfSimpleRoots ∅)) K)
    {φ : Fun} (hc : Continuous φ) (hφ : IsLeftInvariantUnder F G (QuotSub I) φ)
    (heq : IsSplitComponentEquivariant (fam.p I) (fam.l I) φ)
    (r : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A I).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (E : ComplexCharacterParameter F (fam.P I) → Fun) (D : Set (ComplexCharacterParameter F (fam.P I)))
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (R : ℝ) (hreg : ∀ lam, r.IsRegularParameter hA hT R lam →
      E lam = b.summand hKmin w.val φ lam) :
    ∀ lam ∈ D, ∀ a : fam.positiveSplitComponent J,
      fam.normalizedAction J a.val (E lam) = b.splitWeylCharacter w.val lam a • E lam := by
  intro lam hlam a
  funext g
  let : FiniteDimensional ℂ (ComplexCharacterParameter F (fam.P I)) := (hE g).1
  let s := parameterPower F (fam.P J) (-halfModulusParameter F (fam.P J)) a.val
  let g' := map F (fam.P J) G (fam.p J) a.val * g
  have hl : IsMeromorphicInCoordinatesOn (fun t => s * E t g') (Set.univ ∩ D) :=
    (isMeromorphicInCoordinatesOn_const s).mul (hE g')
  have hχ : IsMeromorphicInCoordinatesOn (fun t => b.splitWeylCharacter w.val t a) Set.univ :=
    isMeromorphicInCoordinatesOn_univ fun n e => by
      have hp := differentiable_parameterPower_affine
        ((b.transportedParameter w.val).comp e.toLinearMap) 0
        (fam.splitLift (b.targetIndex_le w.val) a).val
      change Differentiable ℂ (fun s => b.splitWeylCharacter w.val (e s) a)
      simpa only [splitWeylCharacter, LinearMap.comp_apply, LinearEquiv.coe_coe, add_zero] using hp
  have hr : IsMeromorphicInCoordinatesOn (fun t => b.splitWeylCharacter w.val t a * E t g)
      (Set.univ ∩ D) := hχ.mul (hE g)
  have hh := r.eqOn_of_regularParameter hA hT fam.connectedReductive hl hr R (by
    intro t ht
    have h := congrFun (b.fullSourceBruhatCovariance hKmin w φ hc hφ heq t a) g
    rw [← hreg t ht] at h
    exact h)
  exact hh ⟨⟨Set.mem_univ _, hlam⟩, ⟨Set.mem_univ _, hlam⟩⟩

end StandardBruhatConstantTermData

end Langlands.Global.StandardParabolicFamily
