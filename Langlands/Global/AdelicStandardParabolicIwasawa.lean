import Langlands.Global.AdelicIwasawaIntegrationProof
import Langlands.Global.AdelicParabolicModulusProof
import Langlands.Global.AdelicIntertwiningElementaryChainStatement
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Global.AdelicSubgroupHaarNormalization
import Langlands.Global.AdelicAutomorphicExponentDecompositionReduction
import Langlands.GroupScheme.Rational.LeviRetraction

/-! # The Iwasawa integration formula for the standard parabolics of a family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal CompactlySupported

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints _root_.Topology

section RadicalHaar

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom] (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

/-- Mathlib's Haar measure on `U(𝔸)`, transported to the closed subgroup `j(U(𝔸))` of `G(𝔸)`,
is a positive multiple of the normalized Haar measure of that subgroup. -/
theorem exists_integral_adelicRangeMap_eq_normalized
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))] :
    haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
        Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    ∃ β : ℝ, 0 < β ∧
      ∀ g : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) → ℂ,
        ∫ u, g (AdelicSubgroupPoints.adelicRangeMap F j u)
            ∂(Measure.haar : Measure (AdelicGroupPoints F U)) =
          β • ∫ v, g v
            ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)) := by
  have hcl : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  have : LocallyCompactSpace
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hcl.locallyCompactSpace
  let φ := AdelicSubgroupPoints.adelicRangeMap F j
  have hφc : Continuous φ := AdelicSubgroupPoints.continuous_adelicRangeMap F j
  have hφs : Function.Surjective φ := AdelicSubgroupPoints.adelicRangeMap_surjective F j
  have hemb : IsClosedEmbedding (map F U G j) := isClosedEmbedding_map F U G j
  have hφe : IsClosedEmbedding φ := by
    have h1 : IsEmbedding φ := by
      have h0 : IsEmbedding (fun u => ((φ u :
          AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
            AdelicGroupPoints F G)) := hemb.isEmbedding
      exact (IsEmbedding.subtypeVal.of_comp_iff).mp h0
    exact ⟨h1, by rw [hφs.range_eq]; exact isClosed_univ⟩
  have : (Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U))).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ φ hφc hφs hφe.tendsto_cocompact
  set b := Measure.haarScalarFactor (Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U)))
    (Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)))
    with hbdef
  have hb : Measure.map φ (Measure.haar : Measure (AdelicGroupPoints F U)) =
      b • (Measure.haar :
        Measure (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))) :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hbpos : 0 < b := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  set N := AdelicSubgroupPoints.quotientMassNormalizer F G (SubgroupFunctor.range j) with hNdef
  have hN0 : N ≠ 0 := AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G _
  have hNt : N ≠ ⊤ := AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G _
  have hNpos : 0 < N.toReal := ENNReal.toReal_pos hN0 hNt
  refine ⟨(b : ℝ) / N.toReal, div_pos (by exact_mod_cast hbpos) hNpos, ?_⟩
  intro g
  rw [← hφe.measurableEmbedding.integral_map, hb, integral_smul_nnreal_measure]
  unfold AdelicSubgroupPoints.normalizedHaarMeasure
  rw [integral_smul_measure, ← hNdef, smul_smul, div_mul_cancel₀ _ hNpos.ne', NNReal.smul_def]

end RadicalHaar

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

/-- The defining cocharacter of the standard parabolic `P_J`. -/
def definingCocharacter : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G :=
  CommGroupScheme.groupHom (fam.rootPresentation J).splitComponentCocharacter ≫
    fam.a J ≫ fam.l J ≫ fam.p J

theorem isRepresentedBy_parabolic :
    (Dynamic.parabolic (fam.definingCocharacter J)).IsRepresentedBy (fam.p J) :=
  let := (fam.isCompatible J).parabolic.isClosedSubgroup.mono
  ⟨Over.mono_of_mono_left _, (fam.rootPresentation J).parabolic_eq_splitComponentCocharacter⟩

theorem isRepresentedBy_centralizer :
    (Dynamic.centralizer (fam.definingCocharacter J)).IsRepresentedBy (fam.l J ≫ fam.p J) :=
  let := ((fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup).mono
  ⟨Over.mono_of_mono_left _, (fam.rootPresentation J).levi_eq_splitComponentCocharacter⟩

theorem isRepresentedBy_unipotent :
    (Dynamic.unipotent (fam.definingCocharacter J)).IsRepresentedBy (fam.iU J ≫ fam.p J) :=
  haveI : Smooth G.X.hom := fam.connectedReductive.smooth
  ⟨Over.mono_of_mono_left _,
    (fam.rootPresentation J).range_comp_radical_eq (fam.isUnipotentRadical J)⟩

/-- The modulus `δ_P` of the standard parabolic `P_J`, read on the Levi: the Haar modulus of
conjugation by `m ∈ M_J(𝔸)` on `U_J(𝔸)`. -/
def leviModulus (m : AdelicGroupPoints F (fam.M J)) : ℝ≥0 :=
  (parabolicModulus F (fam.isRepresentedBy_parabolic J) (fam.isRepresentedBy_unipotent J)
    (map F (fam.M J) (fam.P J) (fam.l J) m) : ℝ≥0)

theorem leviModulus_mul (m m' : AdelicGroupPoints F (fam.M J)) :
    fam.leviModulus J (m * m') = fam.leviModulus J m * fam.leviModulus J m' := by
  simp [leviModulus, map_mul]

theorem leviModulus_pos (m : AdelicGroupPoints F (fam.M J)) : 0 < fam.leviModulus J m :=
  pos_iff_ne_zero.mpr (Units.ne_zero _)

/-- The modulus is trivial on norm-one Levi points: by `adelicParabolicModulus` it is the idele
norm of a rational character of `P_J`, which restricts to a rational character of `M_J`. -/
theorem leviModulus_eq_one_of_mem_normOne {m : AdelicGroupPoints F (fam.M J)}
    (hm : m ∈ normOneSubgroup F (fam.M J)) : fam.leviModulus J m = 1 := by
  have hG := fam.connectedReductive
  have hP := fam.isRepresentedBy_parabolic J
  have hU := fam.isRepresentedBy_unipotent J
  have := isAffine_unipotent F hU
  have := locallyOfFiniteType_unipotent F hU
  have h1 := (adelicParabolicModulus F G hG (fam.definingCocharacter J) (fam.P J) (fam.U J)
    (fam.p J) (fam.iU J ≫ fam.p J) hP hU _ (Lie.finiteCoordinates (fam.U J))).1
    (map F (fam.M J) (fam.P J) (fam.l J) m)
  unfold leviModulus
  rw [h1, ← characterNorm_comp]
  exact congrArg Units.val ((mem_normOneSubgroup F (fam.M J) m).mp hm _)

/-- The Levi modulus is continuous. -/
theorem continuous_leviModulus : Continuous (fam.leviModulus J) := by
  have hG := fam.connectedReductive
  have hP := fam.isRepresentedBy_parabolic J
  have hU := fam.isRepresentedBy_unipotent J
  have := isAffine_unipotent F hU
  have := locallyOfFiniteType_unipotent F hU
  have h1 := (adelicParabolicModulus F G hG (fam.definingCocharacter J) (fam.P J) (fam.U J)
    (fam.p J) (fam.iU J ≫ fam.p J) hP hU _ (Lie.finiteCoordinates (fam.U J))).1
  have hc := continuous_parabolicModulus_of_eq F hP hU _ h1
  have h2 := (Units.continuous_val.comp hc).comp (map F (fam.M J) (fam.P J) (fam.l J)).continuous
  exact h2

/-- The Levi modulus of a product with a norm-one point. -/
theorem leviModulus_mul_normOne {x : AdelicGroupPoints F (fam.M J)}
    (hx : x ∈ normOneSubgroup F (fam.M J)) (m : AdelicGroupPoints F (fam.M J)) :
    fam.leviModulus J (x * m) = fam.leviModulus J m := by
  rw [leviModulus_mul, leviModulus_eq_one_of_mem_normOne _ _ hx, one_mul]

/-- The Iwasawa integration formula for a standard parabolic of the family, with the Levi
modulus. -/
theorem exists_iwasawaIntegration (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact (fam.p J) K) :
    haveI := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : C_c(AdelicGroupPoints F G, ℂ),
      ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        (c : ℝ) • ∫ k, ∫ m, ∫ u,
          ((fam.leviModulus J m : ℝ))⁻¹ •
            f (map F (fam.U J) G (fam.iU J ≫ fam.p J) u *
              map F (fam.M J) G (fam.l J ≫ fam.p J) m * (k : AdelicGroupPoints F G))
          ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.U J)))
          ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.M J)))
          ∂(compactHaarProbability F G K hK.isCompact) := by
  obtain ⟨c, hc0, hc⟩ := adelicIwasawaIntegration F G fam.connectedReductive
    (fam.definingCocharacter J) (fam.P J) (fam.M J) (fam.U J) (fam.p J) (fam.l J ≫ fam.p J)
    (fam.iU J ≫ fam.p J) (fam.isRepresentedBy_parabolic J) (fam.isRepresentedBy_centralizer J)
    (fam.isRepresentedBy_unipotent J) K hK.isCompact hK.range_mul
  refine ⟨c, hc0, fun f => (hc f).trans ?_⟩
  haveI := fam.isClosedImmersion_p J
  have hcTP : ∀ m : AdelicGroupPoints F (fam.M J),
      map F (fam.M J) (fam.P J) (Dynamic.centralizerToParabolic
        (fam.isRepresentedBy_parabolic J) (fam.isRepresentedBy_centralizer J)) m =
        map F (fam.M J) (fam.P J) (fam.l J) m := fun m =>
    (isClosedEmbedding_map F (fam.P J) G (fam.p J)).injective (by
      rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom,
        Dynamic.centralizerToParabolic_comp])
  simp only [leviModulus, hcTP]

/-- Conjugation of the radical by a norm-one Levi point preserves Haar measure on `U_J(𝔸)`. -/
theorem integral_conj_normOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : AdelicGroupPoints F (fam.M J)} (hx : x ∈ normOneSubgroup F (fam.M J))
    (f : AdelicGroupPoints F G → E) :
    haveI := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
    ∫ u, f ((map F (fam.M J) G (fam.l J ≫ fam.p J) x)⁻¹ *
        map F (fam.U J) G (fam.iU J ≫ fam.p J) u * map F (fam.M J) G (fam.l J ≫ fam.p J) x)
        ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.U J))) =
      ∫ u, f (map F (fam.U J) G (fam.iU J ≫ fam.p J) u)
        ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.U J))) := by
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  have := isAffine_unipotent F (fam.isRepresentedBy_unipotent J)
  have h := integral_conj_parabolicModulus F (fam.isRepresentedBy_parabolic J)
    (fam.isRepresentedBy_unipotent J) (map F (fam.M J) (fam.P J) (fam.l J) x)
    (Measure.haar : Measure (AdelicGroupPoints F (fam.U J))) f
  have hmap : map F (fam.P J) G (fam.p J) (map F (fam.M J) (fam.P J) (fam.l J) x) =
      map F (fam.M J) G (fam.l J ≫ fam.p J) x := (map_comp_apply_of_hom (fam.l J) x).symm
  rw [hmap] at h
  rw [h]
  have h1 : (parabolicModulus F (fam.isRepresentedBy_parabolic J)
      (fam.isRepresentedBy_unipotent J) (map F (fam.M J) (fam.P J) (fam.l J) x) : ℝ≥0) = 1 :=
    fam.leviModulus_eq_one_of_mem_normOne J hx
  rw [h1, one_smul]

local notation "A" => AdelicGroupPoints F G
local notation "ι" => map F (fam.M J) G (fam.l J ≫ fam.p J)
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)

/-- The radical kernel `m ↦ ∫_{U_J(𝔸)} β(g⁻¹ u ι(m) k) du` on `M_J(𝔸)`, for Mathlib's Haar
measure on `U_J(𝔸)`. -/
def radicalKernel (β : A → ℂ) (g k : A) (m : AdelicGroupPoints F (fam.M J)) : ℂ :=
  haveI := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  ∫ u, β (g⁻¹ * (ιU u * ι m * k)) ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.U J)))

/-- Iwasawa decomposition of a right convolution at a Levi translate: for a compactly supported
continuous `β`, a continuous `φ` left invariant under `U_J(𝔸)`, a norm-one Levi point `x` and
`g ∈ G(𝔸)`, the convolution `(β * φ)(ι(x) g)` is the Iwasawa integral of the fibres of `φ`
against the radical kernels. -/
theorem exists_rightConvolution_eq_iwasawa (K : Subgroup A) (hK : IsIwasawaCompact (fam.p J) K) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (β : C_c(A, ℂ)) (φ : A → ℂ), Continuous φ →
      (∀ (u : AdelicGroupPoints F (fam.U J)) (w : A), φ (ιU u * w) = φ w) →
      ∀ x ∈ normOneSubgroup F (fam.M J), ∀ g : A,
        AdelicGroupPoints.rightConvolution F G β φ (ι x * g) =
          (c : ℝ) • ∫ k, ∫ m, ((fam.leviModulus J m : ℝ))⁻¹ •
            (fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k : A)))
            ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.M J)))
            ∂(compactHaarProbability F G K hK.isCompact) := by
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  obtain ⟨c, hc0, hc⟩ := fam.exists_iwasawaIntegration J K hK
  refine ⟨c, hc0, fun β φ hφ hφU x hx g => ?_⟩
  set y : A := ι x * g with hy
  let Fz : C_c(A, ℂ) := ⟨⟨fun z => β (y⁻¹ * z) * φ z,
      (β.continuous.comp (continuous_const.mul continuous_id)).mul hφ⟩,
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft y⁻¹)).mul_right⟩
  have h1 : AdelicGroupPoints.rightConvolution F G β φ y = ∫ z, Fz z ∂Measure.haar := by
    unfold AdelicGroupPoints.rightConvolution
    rw [← integral_mul_left_eq_self (fun z => Fz z) y]
    congr 1
    funext s
    change β s * φ (y * s) = β (y⁻¹ * (y * s)) * φ (y * s)
    rw [inv_mul_cancel_left]
  rw [h1, hc Fz]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  dsimp only
  have hconj := fam.integral_conj_normOne J hx
    (fun w => ((fam.leviModulus J m : ℝ))⁻¹ • (β (g⁻¹ * (w * ι (x⁻¹ * m) * (k : A))) *
      φ (ι m * (k : A))))
  simp only at hconj
  symm
  rw [radicalKernel, ← integral_mul_const, ← integral_smul, ← hconj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change _ = ((fam.leviModulus J m : ℝ))⁻¹ • (β (y⁻¹ * (ιU u * ι m * (k : A))) *
      φ (ιU u * ι m * (k : A)))
  have hφ' : φ (ιU u * ι m * (k : A)) = φ (ι m * (k : A)) := by
    rw [mul_assoc, hφU]
  have harg : y⁻¹ * (ιU u * ι m * (k : A)) =
      g⁻¹ * ((ι x)⁻¹ * ιU u * ι x * ι (x⁻¹ * m) * (k : A)) := by
    rw [hy, map_mul, map_inv]
    group
  rw [hφ', harg]

/-- The Levi projection `P_J(𝔸) → M_J(𝔸)`. -/
def leviProjection : AdelicGroupPoints F (fam.P J) →ₜ* AdelicGroupPoints F (fam.M J) :=
  haveI := fam.isIso_subgroupMultiplication_levi_radical J
  map F (fam.P J) (fam.M J)
    (leviRetraction (fam.l J) (fam.iU J) (fam.isUnipotentRadical J).1.isNormal)

theorem leviProjection_radical (u : AdelicGroupPoints F (fam.U J)) :
    fam.leviProjection J (map F (fam.U J) (fam.P J) (fam.iU J) u) = 1 := by
  haveI := fam.isIso_subgroupMultiplication_levi_radical J
  exact (comp_leviRetraction_eq_one_iff (fam.l J) (fam.iU J)
    (fam.isUnipotentRadical J).1.isNormal _).mpr ⟨u, rfl⟩

theorem leviProjection_levi (m : AdelicGroupPoints F (fam.M J)) :
    fam.leviProjection J (map F (fam.M J) (fam.P J) (fam.l J) m) = m := by
  haveI := fam.isIso_subgroupMultiplication_levi_radical J
  change map F (fam.P J) (fam.M J) (leviRetraction (fam.l J) (fam.iU J)
    (fam.isUnipotentRadical J).1.isNormal) (map F (fam.M J) (fam.P J) (fam.l J) m) = m
  rw [← map_comp_apply_of_hom (fam.l J), levi_comp_leviRetraction]
  rfl

/-- The radical kernels for `g` and `k` in compact sets are supported in one compact subset of
`M_J(𝔸)`. -/
theorem exists_compact_radicalKernel_support (β : C_c(A, ℂ)) {Cg : Set A} (hCg : IsCompact Cg)
    {Ck : Set A} (hCk : IsCompact Ck) :
    ∃ C : Set (AdelicGroupPoints F (fam.M J)), IsCompact C ∧
      ∀ g ∈ Cg, ∀ k ∈ Ck, ∀ m, fam.radicalKernel J β g k m ≠ 0 → m ∈ C := by
  haveI := fam.isClosedImmersion_p J
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  let D : Set A := (fun p : A × A × A => p.1 * p.2.1 * p.2.2⁻¹) '' (Cg ×ˢ tsupport β ×ˢ Ck)
  have hD : IsCompact D := (hCg.prod (β.hasCompactSupport.prod hCk)).image
    ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      (continuous_snd.comp continuous_snd).inv)
  have hDP : IsCompact ((map F (fam.P J) G (fam.p J)) ⁻¹' D) :=
    (isClosedEmbedding_map F (fam.P J) G (fam.p J)).isCompact_preimage hD
  refine ⟨fam.leviProjection J '' ((map F (fam.P J) G (fam.p J)) ⁻¹' D),
    hDP.image (fam.leviProjection J).continuous, ?_⟩
  intro g hg k hk m hm
  have hex : ∃ u, β (g⁻¹ * (ιU u * ι m * k)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hm
    unfold radicalKernel
    exact (integral_congr_ae (Filter.Eventually.of_forall hcon)).trans (integral_zero _ _)
  obtain ⟨u, hu⟩ := hex
  refine ⟨map F (fam.U J) (fam.P J) (fam.iU J) u * map F (fam.M J) (fam.P J) (fam.l J) m, ?_, ?_⟩
  · have hmem : g⁻¹ * (ιU u * ι m * k) ∈ tsupport β := subset_tsupport _ hu
    refine ⟨(g, g⁻¹ * (ιU u * ι m * k), k), ⟨hg, hmem, hk⟩, ?_⟩
    change g * (g⁻¹ * (ιU u * ι m * k)) * k⁻¹ =
      map F (fam.P J) G (fam.p J) (map F (fam.U J) (fam.P J) (fam.iU J) u *
        map F (fam.M J) (fam.P J) (fam.l J) m)
    rw [map_mul, ← map_comp_apply_of_hom (fam.iU J), ← map_comp_apply_of_hom (fam.l J)]
    group
  · rw [map_mul, leviProjection_radical, leviProjection_levi, one_mul]

/-- For `g`, `k` and `m` in compact sets the radical integrand is supported in one compact subset
of `U_J(𝔸)`. -/
theorem exists_compact_radicalKernel_integrand_support (β : C_c(A, ℂ)) {Cg : Set A}
    (hCg : IsCompact Cg) {Ck : Set A} (hCk : IsCompact Ck)
    {Cm : Set (AdelicGroupPoints F (fam.M J))} (hCm : IsCompact Cm) :
    haveI := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
    ∃ S : Set (AdelicGroupPoints F (fam.U J)), IsCompact S ∧
      ∀ g ∈ Cg, ∀ k ∈ Ck, ∀ m ∈ Cm, ∀ u ∉ S, β (g⁻¹ * (ιU u * ι m * k)) = 0 := by
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  have := isAffine_unipotent F (fam.isRepresentedBy_unipotent J)
  have hcl : IsClosedImmersion (fam.iU J ≫ fam.p J).hom.hom.left := inferInstance
  let D : Set A := (fun p : A × A × A × AdelicGroupPoints F (fam.M J) =>
      p.1 * p.2.1 * p.2.2.1⁻¹ * (ι p.2.2.2)⁻¹) '' (Cg ×ˢ tsupport β ×ˢ Ck ×ˢ Cm)
  have hD : IsCompact D := (hCg.prod (β.hasCompactSupport.prod (hCk.prod hCm))).image (by
    fun_prop)
  refine ⟨ιU ⁻¹' D, (isClosedEmbedding_map F (fam.U J) G (fam.iU J ≫ fam.p J)).isCompact_preimage
    hD, fun g hg k hk m hm u hu => ?_⟩
  by_contra hne
  apply hu
  refine ⟨(g, g⁻¹ * (ιU u * ι m * k), k, m), ⟨hg, subset_tsupport _ hne, hk, hm⟩, ?_⟩
  change g * (g⁻¹ * (ιU u * ι m * k)) * k⁻¹ * (ι m)⁻¹ = ιU u
  group

/-- The radical kernel is jointly continuous in `g`, `k` and `m`. -/
theorem continuous_radicalKernel (β : C_c(A, ℂ)) :
    Continuous fun p : A × A × AdelicGroupPoints F (fam.M J) =>
      fam.radicalKernel J β p.1 p.2.1 p.2.2 := by
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨Cg, hCg, hCgn⟩ := exists_compact_mem_nhds p₀.1
  obtain ⟨Ck, hCk, hCkn⟩ := exists_compact_mem_nhds p₀.2.1
  obtain ⟨Cm, hCm, hCmn⟩ := exists_compact_mem_nhds p₀.2.2
  obtain ⟨S, hS, hSupp⟩ := fam.exists_compact_radicalKernel_integrand_support J β hCg hCk hCm
  have hcont : Continuous fun p : A × A × AdelicGroupPoints F (fam.M J) =>
      ∫ u in S, β (p.1⁻¹ * (ιU u * ι p.2.2 * p.2.1))
        ∂(Measure.haar : Measure (AdelicGroupPoints F (fam.U J))) := by
    refine continuous_parametric_integral_of_continuous ?_ hS
    exact β.continuous.comp (by fun_prop)
  refine (hcont.continuousAt).congr ?_
  have hnhds : ∀ᶠ p in nhds p₀, p ∈ Cg ×ˢ Ck ×ˢ Cm :=
    prod_mem_nhds hCgn (prod_mem_nhds hCkn hCmn)
  filter_upwards [hnhds] with p hp
  unfold radicalKernel
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu
  exact hSupp p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2 u hu

end StandardParabolicFamily

end Langlands.Global
