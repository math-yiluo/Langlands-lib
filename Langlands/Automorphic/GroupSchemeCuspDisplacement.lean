import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality
import Langlands.Global.AdelicFiniteTranslateHeightReduction
import Langlands.Global.AdelicMaximalUnipotentOscillation
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Small right translates in the cusps of a reductive adelic quotient -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme Langlands.Global AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

section Chamber

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (rT : T₀ ⟶ T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (hT₀ : IsSplitTorus T₀.toGrp)
  (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "J" => Set.diff (simpleRelativeRoots i ν) (Set.singleton α)
local notation "N" => Standard.unipotentScheme i ν J
local notation "jN" => Standard.unipotentHom i ν J
local notation "mN" => map F N G jN
local notation "aG" => positiveMap F G T i T₀ rT
local notation "R" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom mN)
local notation "P₀" => MonoidHom.range (ContinuousMonoidHom.toMonoidHom
  (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)))

include hG hi hν hT₀ hα in
/-- Deep in one simple-root direction, a translate by the associated maximal-parabolic
radical is, modulo rational radical translation, a small right translate. -/
private theorem exists_cuspDisplacement_in_chamber
    (Ω K : Set A) (hΩ : IsCompact Ω) (hK : IsCompact K) (hΩP : Ω ⊆ (P₀ : Set A))
    (b : ℝ≥0ˣ) (V : Set A) (hV : V ∈ 𝓝 (1 : A)) :
    ∃ s : ℝ, ∀ p ∈ Ω, ∀ a ∈ weakSimpleRootChamber F T₀ T rT G i ν b,
      s ≤ ((normCharacter F T₀ (rT ≫ α) a : ℝ≥0) : ℝ) →
      ∀ k ∈ K, ∀ n : AdelicGroupPoints F N, ∃ q : RationalGroupPoints F N,
        ∃ w ∈ V, mN (rational F N q) * (mN n * (p * aG a * k)) = (p * aG a * k) * w := by
  let hstruct := Standard.parabolicStructure i ν hG hi hν J sdiff_subset
  let hrad := hstruct.2.2.1.isGeometricUnipotentRadical
  let : IsAffineHom (N).X.hom := (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom
  let : IsAffine (N).X.left := isAffine_of_isAffineHom (N).X.hom
  let : IsClosedImmersion (jN).hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν J
  let : Smooth (N).X.hom := hrad.2.1
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let (v : NumberField.InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension (N).X.left _
    (N).X.hom hrad.2.1 hrad.2.2.1
  obtain ⟨W, hWo, hW1, hWW⟩ := exists_open_nhds_one_mul_subset hV
  have hpre : (ofFinite F G) ⁻¹' W ∈ 𝓝 (1 : Gf) := by
    apply ((ofFinite F G).continuous.isOpen_preimage _ hWo).mem_nhds
    change ofFinite F G (1 : Gf) ∈ W
    rwa [map_one]
  obtain ⟨L, _, hLW⟩ := (finiteAdelicGroupCompactOpenBasis F G).2.mem_iff.mp hpre
  let Y := finite F G '' (Ω * K)
  obtain ⟨D, hD, hrep⟩ := adelicUnipotentArchimedeanRepresentatives jN
    hrad.2.2.1 hrad.2.2.2.1 Y ((hΩ.mul hK).image (finite F G).continuous) L.toSubgroup L.isOpen
  obtain ⟨e, Q, hQ₀, _, hconj⟩ := adelicMaximalUnipotentContraction i ν rT jN hd
    hG hi hν α hα inferInstance (Standard.isRepresentedBy_unipotentHom i ν J).2
  let C (pu : A × InfiniteAdelicGroupPoints F N) := pu.1⁻¹ * mN (ofInfinite F N pu.2) * pu.1
  have hCc : Continuous C := (continuous_fst.inv.mul (((mN).continuous.comp
    (ofInfinite F N).continuous).comp continuous_snd)).mul continuous_fst
  let ΩN := mN ⁻¹' (C '' (Ω ×ˢ D))
  have hEmb : IsClosedEmbedding mN := isClosedEmbedding_map_of_isClosedSubgroup F jN
    (Standard.isClosedSubgroup_unipotentHom i ν J)
  obtain ⟨B, _, hBconj⟩ := hconj ΩN (hEmb.isCompact_preimage ((hΩ.prod hD).image hCc)) b
  have hnormalize : ∀ p ∈ Ω, p ∈ Subgroup.normalizer (R : Set A) := by
    intro p hp
    have hle := ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J
      (empty_subset _) sdiff_subset).1.mp (empty_subset _)
    let S := (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))
    have hp0 : p ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν ∅)).carrier S := hΩP hp
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2] at hp0
    have hpJ := hle S hp0
    have hN : R = (standardUnipotent i ν J).carrier S :=
      congrArg (fun U : SubgroupFunctor G => U.carrier S)
        (Standard.isRepresentedBy_unipotentHom i ν J).2
    rw [hN]
    have hNormPoint : (standardParabolic i ν J).carrier S ≤
        Subgroup.normalizer ((standardUnipotent i ν J).carrier S : Set A) := by
      rw [Subgroup.le_normalizer_iff]
      intro g hg n hn
      exact StandardLeviIntersection.conj_mem_standardUnipotent i ν hg hn
    exact hNormPoint hpJ
  let E := Fin e → mixedEmbedding.mixedSpace F
  let jInf := (N).affinePointsTarget jN (CommAlgCat.of F (InfiniteAdeleRing F))
  have hInf (z : AdelicGroupPoints F N) : infinite F G (mN z) = jInf (infinite F N z) :=
    DFunLike.congr_fun ((N).affinePointsTarget_naturality jN
      (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeles F)))) z
  let Ψ (z : E) := ofInfinite F G (jInf (Q.symm z))
  have hjInf : Continuous jInf := (N).continuous_affinePointsTarget _ jN
  have hΨc : Continuous Ψ := (ofInfinite F G).continuous.comp (hjInf.comp Q.symm.continuous)
  have hΨ₀ : Ψ 0 = 1 := by simp only [Ψ, ← hQ₀, Q.symm_apply_apply, map_one]
  have hnear : ∀ᶠ z in 𝓝 (0 : E), ∀ k ∈ K, k⁻¹ * Ψ z * k ∈ W := by
    apply hK.eventually_forall_of_forall_eventually
    intro k _
    let d (p : E × A) := p.2⁻¹ * Ψ p.1 * p.2
    have hd : Continuous d := (continuous_snd.inv.mul (hΨc.comp continuous_fst)).mul continuous_snd
    exact (hd.isOpen_preimage _ hWo).mem_nhds (show d (0, k) ∈ W by
      simpa only [d, hΨ₀, mul_one, inv_mul_cancel] using hW1)
  obtain ⟨ε, hε, hεW⟩ : ∃ ε > 0, Metric.ball (0 : E) ε ⊆ {z | ∀ k ∈ K, k⁻¹ * Ψ z * k ∈ W} :=
    Metric.mem_nhds_iff.mp hnear
  have hlim : Tendsto (fun t : ℝ => B * t ^ (-1 / (Module.finrank ℚ F : ℝ))) atTop (𝓝 0) := by
    have hpos : 0 < (1 : ℝ) / Module.finrank ℚ F :=
      one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
    simpa only [mul_zero, neg_div] using (tendsto_rpow_neg_atTop hpos).const_mul B
  obtain ⟨s, hs⟩ := eventually_atTop.mp (hlim (gt_mem_nhds hε))
  refine ⟨s, fun p hp a ha hsa k hk n => ?_⟩
  let x := p * aG a * k
  have hxY : finite F G x ∈ Y := by
    refine ⟨p * k, mul_mem_mul hp hk, ?_⟩
    simp only [x, map_mul, finite_positiveMap F G T i T₀ rT hT₀ a, mul_one]
  obtain ⟨nInf, hnInf, q, hq⟩ := hrep n
  obtain ⟨l, hl⟩ := hq x hxY
  have hcR : C (p, nInf) ∈ R := by
    have hn : p⁻¹ ∈ Subgroup.normalizer (R : Set A) := inv_mem (hnormalize p hp)
    simpa only [C, inv_inv] using (Subgroup.mem_normalizer_iff.mp hn (mN (ofInfinite F N nInf))).mp
      (show mN (ofInfinite F N nInf) ∈ R from ⟨_, rfl⟩)
  obtain ⟨z, hz⟩ := hcR
  change mN z = C (p, nInf) at hz
  have hzΩ : z ∈ ΩN := ⟨(p, nInf), ⟨hp, hnInf⟩, hz.symm⟩
  obtain ⟨y, hy, hyB⟩ := hBconj z hzΩ a ha
  have hyf : finite F G (mN y) = 1 := by
    rw [← hy, hz]
    simp only [C, finite_map, map_mul, map_inv, finite_ofInfinite, map_one, mul_one,
      inv_mul_cancel]
  let z' := Q (infinite F N y)
  have hz' : z' ∈ Metric.ball (0 : E) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hyB.trans_lt (hs _ hsa)
  have hyΨ : mN y = Ψ z' := by
    apply (split F G).injective
    simp only [split_apply, hyf, Ψ, z', Q.symm_apply_apply, hInf, infinite_ofInfinite,
      finite_ofInfinite]
  have heq : mN (ofInfinite F N nInf) * x = x * (k⁻¹ * mN y * k) := by
    rw [← hy, hz]
    dsimp only [x, C]
    group
  let w := (k⁻¹ * Ψ z' * k) * ofFinite F G l.val
  have hw : w ∈ V := hWW (mul_mem_mul (hεW hz' k hk) (hLW l.property))
  refine ⟨q, w, hw, ?_⟩
  rw [hl, heq, hyΨ, mul_assoc]

end Chamber

section Cover

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (Z : CommGroupScheme (Spec (CommRingCat.of F))) (jZ : Z.toGrp ⟶ G)
  (hjZ : Function.Injective (characterRestrict jZ)) [(characterRestrict jZ).range.FiniteIndex]
  (I : Type u) [Fintype I] (eZ : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral jZ)

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G Z jZ
local notation "Q" => PositiveRationalQuotient F G Z jZ

include hjZ I eZ hc in
/-- Outside a compact part of the positive rational quotient, the value of a continuous
cuspidal function is bounded by its oscillation under small right translations. -/
theorem exists_compact_groupSchemeCuspDisplacementCover (V : Set A)
    (hV : V ∈ 𝓝 (1 : A)) :
    ∃ C : Set Q, IsCompact C ∧
      ∀ ψ : C(Q, ℂ), positiveQuotientContinuousPullback F G Z jZ ψ ∈
        normalizedParabolicCuspidalSubrepresentation F G hPD hG →
      ∀ q ∉ C, ∀ M : ℝ,
        (∀ w ∈ V, ‖ψ q - ψ (LeftCosetSpace.rightTranslate Γ w q)‖ ≤ M) → ‖ψ q‖ ≤ M := by
  classical
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, i, ν, T₀, j, hsetup, C, b, W, hW, hcover⟩ :=
    hasFiniteRightSiegelCover_of_connectedReductive F G hG
  let D := canonicalStandardFactors F G T i ν
  let Ω := compactPrefix F G T i ν D C
  let K := (C.compactSubgroup : Set A) * W
  let aG := positiveMap F G T i T₀ j
  let Δ := simpleRelativeRoots i ν
  have hΩ : IsCompact Ω := isCompact_compactPrefix F G T i ν D C
  have hK : IsCompact K := C.compact_compactSubgroup.mul hW.isCompact
  have hΩP : Ω ⊆ ((map F _ G (Standard.parabolicHom i ν ∅)).toMonoidHom.range : Set A) := by
    intro p hp
    change p ∈ (map F _ G (Standard.unipotentHom i ν ∅) '' C.omegaN) *
      ((fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
        map F _ G (Standard.leviHom i ν ∅) m.val) '' C.omegaM) at hp
    rcases hp with ⟨_, ⟨n, _, rfl⟩, _, ⟨m, _, rfl⟩, rfl⟩
    let p₀ := map F _ G (Standard.parabolicHom i ν ∅)
    have hn₀ : p₀ (map F _ _ (Standard.unipotentToParabolic i ν ∅) n) =
        map F _ G (Standard.unipotentHom i ν ∅) n := by
      change map F _ G (Standard.parabolicHom i ν ∅) (map F _ _ (Standard.unipotentToParabolic i ν ∅) n) = _
      rw [← map_comp_apply_of_hom, Standard.unipotentToParabolic_comp]
    have hm₀ : p₀ (map F _ _ (Standard.leviToParabolic i ν ∅) m.val) =
        map F _ G (Standard.leviHom i ν ∅) m.val := by
      change map F _ G (Standard.parabolicHom i ν ∅) (map F _ _ (Standard.leviToParabolic i ν ∅) m.val) = _
      rw [← map_comp_apply_of_hom, Standard.leviToParabolic_comp]
    exact mul_mem ⟨_, hn₀⟩ ⟨_, hm₀⟩
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, hmax, _⟩ := hsetup.2.2.2.2.2.2.2.1
    exact hmax.1.1
  let : Finite Δ := (hsetup.1.1.1.finite_simpleRelativeRoots i ν).to_subtype
  choose s hs using fun α : Δ => exists_cuspDisplacement_in_chamber i ν j hG hsetup.1
    hsetup.2.1 hT₀ α.val α.property Ω K hΩ hK hΩP b V hV
  obtain ⟨r, hr⟩ := (Set.finite_range s).bddAbove
  let B := max (((b⁻¹ : ℝ≥0ˣ) : ℝ≥0)) r.toNNReal
  have hB (α : Δ) : s α ≤ (B : ℝ) :=
    (hr (mem_range_self α)).trans ((Real.le_coe_toNNReal r).trans (by exact_mod_cast le_max_right _ _))
  have hBb : B⁻¹ ≤ (b : ℝ≥0) := by
    have hb : 0 < ((b⁻¹ : ℝ≥0ˣ) : ℝ≥0) := (b⁻¹).ne_zero.bot_lt
    have h := inv_anti₀ hb (le_max_left (b⁻¹ : ℝ≥0ˣ).val r.toNNReal)
    simpa only [B, Units.val_inv_eq_inv_val, inv_inv] using h
  let X := {a : intrinsicSubgroup F T₀ | ∀ α ∈ Δ,
    B⁻¹ ≤ (normCharacter F T₀ (j ≫ α) a : ℝ≥0) ∧ (normCharacter F T₀ (j ≫ α) a : ℝ≥0) ≤ B}
  have hX : IsCompact X := simpleRootBoxCompactStatement_of_rootComplement
    relativeRootNegation relativeCharacterRootComplement F G hG T i ν T₀ j hsetup B
  let S := (Ω * (aG '' X)) * K
  let mk := LeftCosetSpace.mk Γ
  refine ⟨mk '' S, ((hΩ.mul (hX.image aG.continuous)).mul hK).image
    (LeftCosetSpace.continuous_mk Γ), ?_⟩
  intro ψ hψ q hq M hosc
  let e := positiveQuotientHomeomorph F G Z jZ hjZ I eZ hc
  obtain ⟨g, hg⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) (e.symm q)
  have hgq : mk (g : A) = q := by
    change e (LeftCosetSpace.mk (rationalNormOneSubgroup F G) g) = q
    rw [hg, e.apply_symm_apply]
  obtain ⟨rationalPoint, _, hsw, w, hw, heq⟩ := hcover g
  obtain ⟨n, hn, m, hm, a, ha, k, hk, hnm⟩ :=
    (mem_productSet_iff F G T i ν D C T₀ j _ _).mp hsw
  let p := map F _ G (Standard.unipotentHom i ν ∅) n *
    map F _ G (Standard.leviHom i ν ∅) m.val
  have hp : p ∈ Ω := mul_mem_mul ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
  have hkw : k * w ∈ K := mul_mem_mul hk hw
  let x := p * aG a * (k * w)
  have hx : x = rational F G rationalPoint * (g : A) := by
    change p * aG a * k = _ at hnm
    change p * aG a * (k * w) = _
    rw [← mul_assoc, hnm]
    exact heq
  have hrat (rationalPoint : RationalGroupPoints F G) : rational F G rationalPoint ∈ Γ :=
    rationalSubgroup_le_positiveRationalSubgroup F G Z jZ ⟨rationalPoint, rfl⟩
  have hxq : mk x = q := by
    rw [hx, show mk (rational F G rationalPoint * (g : A)) = mk (g : A) from
      LeftCosetSpace.mk_subgroup_mul Γ ⟨_, hrat rationalPoint⟩ _, hgq]
  have hlarge : ∃ α : Δ, B < (normCharacter F T₀ (j ≫ α.val) a : ℝ≥0) := by
    by_contra! hall
    have haX : a ∈ X := fun α hα =>
      ⟨hBb.trans (Units.val_le_val.mpr (ha α hα)), hall ⟨α, hα⟩⟩
    apply hq
    exact ⟨x, mul_mem_mul (mul_mem_mul hp ⟨a, haX, rfl⟩) hkw, hxq⟩
  obtain ⟨α, hα⟩ := hlarge
  let J := Δ \ {α.val}
  let N := Standard.unipotentScheme i ν J
  let jN := Standard.unipotentHom i ν J
  let pJ := Standard.parabolicHom i ν J
  let rJ := Standard.unipotentToParabolic i ν J
  have hstruct := Standard.parabolicStructure i ν hG hsetup.1 hsetup.2.1 J sdiff_subset
  have hrad := hstruct.2.2.1.isGeometricUnipotentRadical
  have hproper : SubgroupFunctor.range pJ ≠ ⊤ := by
    intro h
    have hle : standardParabolic i ν Δ ≤ standardParabolic i ν J := le_of_eq
      ((standardParabolicEndpoints F G hG T i hsetup.1 ν hsetup.2.1).2.2.1.trans
        (h.symm.trans (Standard.isRepresentedBy_parabolicHom i ν J).2))
    have hsub := ((standardParabolicOrder F G hG T i hsetup.1 ν hsetup.2.1).1 Δ J
      subset_rfl sdiff_subset).1.mpr hle
    exact (hsub α.property).2 rfl
  let P : ProperRationalParabolic G :=
    ⟨⟨SubgroupFunctor.range pJ, ⟨_, pJ, hstruct.1, rfl⟩⟩, hproper⟩
  let : IsAffineHom (Standard.parabolicScheme i ν J).X.hom := hstruct.1.isClosedSubgroup.isAffineHom
  let : IsAffineHom N.X.hom := (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom
  let : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  let : IsClosedImmersion jN.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν J
  let φ := positiveQuotientContinuousPullback F G Z jZ ψ
  have hct := (mem_normalizedParabolicCuspidalSubrepresentation_iff F G hPD hG φ).mp hψ P x
  have hP : properRationalParabolicRadicals hPD hG P = SubgroupFunctor.range jN := by
    rw [show jN = rJ ≫ pJ from (Standard.unipotentToParabolic_comp i ν J).symm]
    exact properRationalParabolicRadicals_eq hPD hG hstruct.1 hproper hrad.isUnipotentRadical
  have hcompare (U : SubgroupFunctor G) (hU : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set A))
      (h : U = SubgroupFunctor.range jN) :
      letI := hU
      AdelicSubgroupPoints.normalizedConstantTerm F G U φ x =
        subgroupConstantTerm F jN (evaluate F G φ) x := by
    subst U
    exact AdelicSubgroupPoints.normalizedConstantTerm_range_eq_subgroupConstantTerm F G jN φ x
  have hct' : subgroupConstantTerm F jN (evaluate F G φ) x = 0 :=
    (hcompare _ (isClosed_properRationalParabolicRadicalAdelicPoints F G hPD hG P) hP).symm.trans hct
  have hφR (rationalPoint : RationalGroupPoints F G) (z : A) :
      evaluate F G φ (rational F G rationalPoint * z) = evaluate F G φ z := φ.val.property rationalPoint z
  have hnorm := norm_sub_subgroupConstantTerm_le jN hrad.2.1 hrad.2.2.1 hrad.2.2.2.1
    (evaluate F G φ) φ.property
    (fun rationalPoint z => by rw [map_rational]; exact hφR _ z) x (B := M) (by
      intro n
      have hbα : s α ≤ ((normCharacter F T₀ (j ≫ α.val) a : ℝ≥0) : ℝ) :=
        (hB α).trans (by exact_mod_cast hα.le)
      obtain ⟨rationalPoint, d, hd, he⟩ := hs α p hp a ha hbα (k * w) hkw n
      have hleft : evaluate F G φ (map F N G jN (rational F N rationalPoint) * (map F N G jN n * x)) =
          evaluate F G φ (map F N G jN n * x) := by
        rw [map_rational]
        exact hφR _ _
      change map F N G jN (rational F N rationalPoint) * (map F N G jN n * x) = x * d at he
      rw [← hleft, he, norm_sub_rev]
      change ‖ψ (mk x) - ψ (LeftCosetSpace.rightTranslate Γ d (mk x))‖ ≤ M
      rw [hxq]
      exact hosc d hd)
  rw [hct', sub_zero] at hnorm
  change ‖ψ (mk x)‖ ≤ M at hnorm
  rwa [hxq] at hnorm

end Cover

end Langlands.Automorphic.GroupSchemeFunctions
