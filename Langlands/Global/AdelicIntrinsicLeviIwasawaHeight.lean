import Langlands.Global.AdelicCharacteristicShellCoordinates
import Langlands.Global.AdelicIntrinsicLeviChamber
import Langlands.Global.AdelicStandardParabolicFamilyConstruction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # The minimal Iwasawa compact and height inherited by a standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set Topology TensorProduct
open scoped CategoryTheory.MonObj Pointwise TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints AdelicSiegelFactors
  ArthurTruncation ArthurParabolicSpaces AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "M" => fam.M J
local notation "P" => fam.P J
local notation "U" => fam.U J
local notation "T" => fam.T
local notation "p" => fam.p J
local notation "l" => fam.l J
local notation "u" => fam.iU J
local notation "j" => fam.l J ≫ fam.p J
local notation "tL" => fam.torus J
local notation "hU" => fam.isUnipotentRadical J
local notation "H₀" => fam.minimalHeight hK
local notation "hcan" => fam.isIwasawaCompact_standardBot hK
local notation "hres" => fam.bijective_restrictToTorus_bot
local notation "P₀" => Standard.parabolicScheme fam.i fam.ν ∅
local notation "p₀" => Standard.parabolicHom fam.i fam.ν ∅
local notation "PL" => Standard.parabolicScheme (fam.torus J) fam.ν ∅
local notation "pL" => Standard.parabolicHom (fam.torus J) fam.ν ∅
local notation "Pmap" => map F P₀ G p₀
local notation "Lmap" => map F M G (fam.l J ≫ fam.p J)
local notation "KM" => K.comap (ContinuousMonoidHom.toMonoidHom (map F M G (fam.l J ≫ fam.p J)))

set_option quotPrecheck false in
local notation "hM'" => (fam.isCompatible J).levi.isConnectedReductive
local instance : IsAffineHom (M).X.hom := (hM').isAffineHom
local instance : IsClosedImmersion (p).hom.hom.left := fam.isClosedImmersion_p J
local instance : IsClosedImmersion (j).hom.hom.left :=
  (fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup
local instance : IsIso (subgroupMultiplication l u) :=
  Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
    (⟨⟨T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
      ParabolicRootPresentation p l (fam.a J)) fam.connectedReductive hU

omit [NumberField F] in
private theorem intrinsicLeviRootData :
    IsMaximalSplitTorus tL ∧ IsGenericCocharacter tL fam.ν ∧
      simpleRelativeRoots tL fam.ν = J.val ∧
      standardParabolic tL fam.ν ∅ = (standardParabolic fam.i fam.ν ∅).comap (j) := by
  have hj : IsClosedSubgroup (j) := inferInstanceAs (IsClosedImmersion (j).hom.hom.left)
  have hrep : (standardLevi fam.i fam.ν J.val).IsRepresentedBy (j) :=
    ⟨Over.mono_of_mono_left _, (fam.isCompatible J).levi_eq⟩
  let iL := standardLeviTorusFactor fam.i fam.ν J.val hrep
  have ht : iL = tL := hrep.hom_ext ((standardLeviTorusFactor_comp _ _ _ _).trans (fam.torus_comp J).symm)
  have hiL := fam.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor fam.i fam.ν J.val hrep hj
  obtain ⟨hr, hνL, hs⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter F G
    fam.connectedReductive T fam.i fam.maximalSplit fam.ν fam.generic J.val J.property M (hM') (j) hrep hj
  rw [← ht]
  exact ⟨hiL, hνL, hr, (hs ∅ (Set.empty_subset _)).1⟩

private theorem mem_minimalLeviParabolic_iff (m : AdelicGroupPoints F M) :
    m ∈ (map F PL M pL).toMonoidHom.range ↔ Lmap m ∈ (Pmap).toMonoidHom.range := by
  rw [mem_range_map_iff_of_isRepresentedBy F (Standard.isRepresentedBy_parabolicHom tL fam.ν ∅),
    mem_range_map_iff_of_isRepresentedBy F (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅),
    (fam.intrinsicLeviRootData J).2.2.2]
  rfl

omit [NumberField F] in
private theorem range_minimalLeviParabolic_le :
    SubgroupFunctor.range (pL ≫ (j)) ≤ SubgroupFunctor.range p₀ := by
  intro X x hx
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hm : s ≫ (pL).hom.hom ∈ (standardParabolic tL fam.ν ∅).carrier X := by
    rw [← (Standard.isRepresentedBy_parabolicHom tL fam.ν ∅).2]
    exact ⟨s, rfl⟩
  rw [(fam.intrinsicLeviRootData J).2.2.2] at hm
  rw [(Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2, Grp.comp_hom_hom, ← Category.assoc]
  exact hm

omit [NumberField F] in
private theorem range_minimalParabolic_le : SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p := by
  have h := (fam.isCompatible fam.bot).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm
  rw [← h]
  exact (fam.le_iff_range_le fam.bot J).mp (Set.empty_subset _)

omit [NumberField F] in
private theorem range_radical_le_minimal : SubgroupFunctor.range (u ≫ p) ≤ SubgroupFunctor.range p₀ := by
  have h := (fam.isCompatible fam.bot).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm
  rw [← h]
  have hbot : fam.bot ≤ J := Set.empty_subset _
  exact (fam.radical_le_of_le hbot).trans (SubgroupFunctor.range_comp_le _ _)

set_option maxHeartbeats 1600000 in
include hK in
/-- The maximal compact induced on the Levi has minimal Iwasawa coverage. -/
theorem intrinsicLevi_isIwasawaCompact (hKM : IsMaximalCompactSubgroup F M KM) :
    IsIwasawaCompact pL KM := by
  refine ⟨hKM.1, Set.eq_univ_of_univ_subset fun m _ => ?_⟩
  obtain ⟨q, k, hk, hq⟩ := (hcan).exists_eq (Lmap m)
  let inc := SubgroupFunctor.rangeFactor p₀ p (fam.range_minimalParabolic_le J)
  have hinc : inc ≫ p = p₀ := SubgroupFunctor.rangeFactor_comp _ _ _
  let r := map F P₀ P inc q
  have hr : map F P G p r = Pmap q := by
    change map F P G p (map F P₀ P inc q) = Pmap q
    rw [← map_comp_apply_of_hom, hinc]
  let c := r⁻¹ * map F M P l m
  have hc : map F P G p c = k := by
    change map F P G p (r⁻¹ * map F M P l m) = k
    rw [map_mul, map_inv, hr, ← map_comp_apply_of_hom, ← hq]
    exact inv_mul_cancel_left _ _
  let ret := leviRetraction l u (hU).1.isNormal
  let π := map F P M ret
  have hcK : π c ∈ KM := by
    rw [← map_parabolicCompact_retraction p u l hU hK.isCompact hKM]
    refine ⟨c, ?_, rfl⟩
    change map F P G p c ∈ K
    rwa [hc]
  let E := coordinates p u l hU
  let z := E.symm r
  have hz : E z = r := E.apply_symm_apply r
  have hv : π r = z.2 := by
    rw [← hz]
    exact proj_coordinates p u l hU z
  have hprod : z.1.val * Lmap z.2 = Pmap q := by
    rw [← hr, ← hz]
    exact (map_coordinates p u l hU z).symm
  have hn : z.1.val ∈ (Pmap).toMonoidHom.range := by
    apply (mem_range_map_iff_of_isRepresentedBy F
      (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅) _).mpr
    rw [← (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2]
    exact fam.range_radical_le_minimal J _ z.1.property
  have hm : z.2 ∈ (map F PL M pL).toMonoidHom.range := by
    apply (fam.mem_minimalLeviParabolic_iff J z.2).mpr
    have hy : Lmap z.2 = z.1.val⁻¹ * Pmap q := by rw [← hprod, inv_mul_cancel_left]
    rw [hy]
    exact (Pmap).toMonoidHom.range.mul_mem ((Pmap).toMonoidHom.range.inv_mem hn) ⟨q, rfl⟩
  obtain ⟨w, hw⟩ := hm
  refine ⟨_, ⟨w, rfl⟩, π c, hcK, ?_⟩
  change map F PL M pL w = z.2 at hw
  rw [hw, ← hv]
  change π r * π c = m
  rw [← map_mul]
  change π (r * (r⁻¹ * map F M P l m)) = m
  rw [mul_inv_cancel_left]
  change map F P M ret (map F M P l m) = m
  rw [← map_comp_apply_of_hom, levi_comp_leviRetraction]
  rfl

/-- The inherited positive-torus compatibility follows by mapping the Levi intersection into
the ambient minimal parabolic and using injectivity of the closed Levi inclusion. -/
theorem intrinsicLevi_isPositiveTorusCompatible
    (hCompat : IsPositiveTorusCompatible F G T fam.i fam.ν T (𝟙 T) K) :
    IsPositiveTorusCompatible F M T tL fam.ν T (𝟙 T) KM := by
  intro k hk hp b
  have hkG : Lmap k ∈ K := hk
  have hpG : Lmap k ∈ Set.range Pmap := (fam.mem_minimalLeviParabolic_iff J k).mp hp
  have ht : Lmap (positiveMap F M T tL T (𝟙 T) b) = positiveMap F G T fam.i T (𝟙 T) b := by
    change Lmap (map F (T).toGrp M (CommGroupScheme.groupHom (𝟙 T) ≫ tL) b.val) =
      map F (T).toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ fam.i) b.val
    rw [← map_comp_apply_of_hom, Category.assoc, fam.torus_comp]
  apply (isClosedEmbedding_map F M G (j)).injective
  rw [map_mul, map_mul, ht]
  exact (hCompat _ hkG hpG b).eq

/-- The intrinsic standard Levi uses the ambient minimal Iwasawa height on its adelic points. -/
def IntrinsicLeviIwasawaHeightStatement : Prop :=
  IsMaximalCompactSubgroup F M KM →
    ∃ (hiL : IsMaximalSplitTorus tL) (hKL : IsIwasawaCompact pL KM)
      (hρ : Function.Bijective (restrictToTorus F tL fam.ν ∅)),
      IsGenericCocharacter tL fam.ν ∧ simpleRelativeRoots tL fam.ν = J.val ∧
      ∀ m : AdelicGroupPoints F M, H₀ (Lmap m) = height hiL hKL hρ m

set_option maxHeartbeats 1500000 in
/-- Transport the lower minimal-parabolic factor into the ambient minimal parabolic. The
character logarithms agree via restriction to the same maximal split torus. -/
theorem intrinsicLeviIwasawaHeight : fam.IntrinsicLeviIwasawaHeightStatement J hK := by
  intro hKM
  obtain ⟨hiL, hνL, hr, _⟩ := fam.intrinsicLeviRootData J
  let : Mono (tL).hom.hom.left := hiL.isSplitSubtorus.mono
  let hKL := fam.intrinsicLevi_isIwasawaCompact J hK hKM
  let hρ := bijective_restrictToTorus_minimal F M T tL fam.ν (hM') hiL hνL
  refine ⟨hiL, hKL, hρ, hνL, hr, fun m => ?_⟩
  let f := SubgroupFunctor.rangeFactor (pL ≫ (j)) p₀ (fam.range_minimalLeviParabolic_le J)
  have hf : f ≫ p₀ = pL ≫ (j) := SubgroupFunctor.rangeFactor_comp _ _ _
  have ht : torusToParabolic F tL fam.ν ∅ ≫ f = torusToParabolic F fam.i fam.ν ∅ := by
    apply (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).hom_ext
    rw [Category.assoc, hf, ← Category.assoc, torusToParabolic_comp, fam.torus_comp, torusToParabolic_comp]
  obtain ⟨q, k, hk, he⟩ := hKL.exists_eq m
  have he' : Pmap (map F PL P₀ f q) * Lmap k = Lmap m := by
    rw [← map_comp_apply_of_hom, hf, map_comp_apply_of_hom, ← map_mul, he]
  have hGLog := (hcan).height_eq (show Lmap k ∈ K from hk) he'
  have hLLog := hKL.height_eq hk he
  apply (isPerfPair_of_isSplitTorus fam.maximalSplit.isSplitSubtorus.1).bijective_right.injective
  apply LinearMap.ext
  intro y
  obtain ⟨χ, rfl⟩ := (hres).surjective y
  let x := rationalCharacterRestrictReal f χ
  have hx : restrictToTorus F tL fam.ν ∅ x = restrictToTorus F fam.i fam.ν ∅ χ := by
    change rationalCharacterRestrictReal (torusToParabolic F tL fam.ν ∅) (rationalCharacterRestrictReal f χ) = _
    rw [rationalCharacterRestrictReal_comp_apply, ht]
    rfl
  change pair T (restrictToTorus F fam.i fam.ν ∅ χ) (H₀ (Lmap m)) =
    pair T (restrictToTorus F fam.i fam.ν ∅ χ) (height hiL hKL hρ m)
  rw [minimalHeight, height, hGLog, pair_toA0, characterLog_map,
    realParameterPairing_realCharacterDualMap, ← hx, height, hLLog, pair_toA0]

set_option maxHeartbeats 1400000 in
/-- The Levi quotient factor of the actual shell is the intrinsic characteristic region,
with the cutoffs projected along the relative split space. -/
theorem intrinsicLeviCharacteristicRegion (hKM : IsMaximalCompactSubgroup F M KM) :
    ∃ (hiL : IsMaximalSplitTorus tL) (hKL : IsIwasawaCompact pL KM)
      (hρ : Function.Bijective (restrictToTorus F tL fam.ν ∅)),
      haveI := hiL.isSplitSubtorus.mono
      ∀ (DL : RelativeRootReflectionData tL)
        (CL : CompactFactors F M (Standard.unipotentScheme tL fam.ν ∅)
          (Standard.leviScheme tL fam.ν ∅)),
        IsRationalCovering CL → ∀ T₀ Tp : V T,
          let proj := ArthurRelative.levelProjection fam.connectedReductive fam.maximalSplit fam.ν
            fam.coroots J.val
          fam.characteristicLeviHeightRegion J hK T₀ Tp =
            characteristicRegion (hM') hiL DL hKL hρ CL (T₀ - proj T₀) (Tp - proj Tp) := by
  obtain ⟨hiL, hKL, hρ, hνL, he, hheight⟩ := fam.intrinsicLeviIwasawaHeight J hK hKM
  refine ⟨hiL, hKL, hρ, fun DL CL hcov T₀ Tp => ?_⟩
  let : Mono (tL).hom.hom.left := hiL.isSplitSubtorus.mono
  let lower := StandardParabolicFamily.ofMaximalSplitTorus (hM') tL hiL fam.ν hνL
  have hLower : IsIwasawaCompact (lower.p lower.bot) KM := hKL
  let proj := ArthurRelative.levelProjection fam.connectedReductive fam.maximalSplit fam.ν fam.coroots J.val
  let W := characteristicChamber fam.ν (hM') hiL DL (T₀ - proj T₀) (Tp - proj Tp)
  have hChamber : characteristicLeviChamber fam.connectedReductive fam.maximalSplit fam.coroots J T₀ Tp = W :=
    intrinsicLeviChamber fam.connectedReductive fam.maximalSplit (hM') hiL (j)
      fam.coroots DL J (fam.torus_comp J) hνL fam.generic he T₀ Tp
  let Γ := rationalNormOneSubgroup F M
  let ΓL := parabolicRationalNormOneSubgroup (F := F) (lower.p lower.top)
  let f := LeftCosetSpace.projectionOfLE (lower.parabolicRationalNormOneSubgroup_le lower.top)
  let A₀ : Set (normOneSubgroup F M) := Subtype.val ⁻¹'
    characteristicHeightProduct hiL hKL hρ CL W
  let A₁ : Set (normOneSubgroup F M) := {m | height hiL hKL hρ m.val ∈ W}
  have h : LeftCosetSpace.mk ΓL '' A₀ = LeftCosetSpace.mk ΓL '' A₁ :=
    lower.characteristicHeightLift hLower lower.top CL hcov W
  have hImage (A : Set (normOneSubgroup F M)) :
      f '' (LeftCosetSpace.mk ΓL '' A) = LeftCosetSpace.mk Γ '' A :=
    Set.image_image f (LeftCosetSpace.mk ΓL) A
  have hᵢ := (hImage A₁).symm.trans ((congrArg (Set.image f) h.symm).trans (hImage A₀))
  change LeftCosetSpace.mk Γ '' {m : normOneSubgroup F M | H₀ (Lmap m.val) ∈ _} =
    LeftCosetSpace.mk Γ '' A₀
  simp_rw [hheight, hChamber]
  exact hᵢ

end Langlands.Global.StandardParabolicFamily
