import Langlands.Global.AdelicChamberFromRankOneHeight

/-! # The minimal-parabolic norm-one coordinate homeomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

section Embeddings

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
  (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)

include hS in
/-- The Levi projection continuously recovers both factor images of an ordered product. -/
private theorem isEmbedding_unipotentLeviProduct :
    IsEmbedding (fun x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) ×
        AdelicGroupPoints F (Standard.leviScheme i ν ∅) =>
      map F _ G (Standard.unipotentHom i ν ∅) x.1 *
        map F _ G (Standard.leviHom i ν ∅) x.2) := by
  let N := Standard.unipotentScheme i ν ∅
  let M := Standard.leviScheme i ν ∅
  let P := standardParabolicImage F G T i ν
  let ιN := map F N G (Standard.unipotentHom i ν ∅)
  let ιM := map F M G (Standard.leviHom i ν ∅)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hNc := Standard.isClosedSubgroup_unipotentHom i ν ∅
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffine N.X.left := isAffine_of_isClosedSubgroup F G _ hNc
  have : IsAffine M.X.left := isAffine_of_isClosedSubgroup F G _ hMc
  have hN : IsEmbedding ιN :=
    (isClosedEmbedding_map_of_isClosedSubgroup F _ hNc).isEmbedding
  have hM : IsEmbedding ιM :=
    (isClosedEmbedding_map_of_isClosedSubgroup F _ hMc).isEmbedding
  obtain ⟨f, hf, _, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hS
  have hnP (n : AdelicGroupPoints F N) : ιN n ∈ P :=
    standardUnipotentImage_le_parabolic F G T i ν ⟨n, rfl⟩
  have hmP (m : AdelicGroupPoints F M) : ιM m ∈ P :=
    standardLeviImage_le_parabolic F G T i ν ⟨m, rfl⟩
  let product : AdelicGroupPoints F N × AdelicGroupPoints F M → P :=
    fun x => ⟨ιN x.1 * ιM x.2, P.mul_mem (hnP x.1) (hmP x.2)⟩
  have hproduct : Continuous product :=
    ((ιN.continuous.comp continuous_fst).mul (ιM.continuous.comp continuous_snd)).subtype_mk _
  have hproject (x : AdelicGroupPoints F N × AdelicGroupPoints F M) :
      f (product x) = ιM x.2 := by
    change f ((⟨ιN x.1, hnP x.1⟩ : P) * ⟨ιM x.2, hmP x.2⟩) = _
    have hn : f (⟨ιN x.1, hnP x.1⟩ : P) = 1 := (hfker _).mpr ⟨x.1, rfl⟩
    rw [map_mul, hn, one_mul]
    exact hfid (ιM x.2) ⟨x.2, rfl⟩
  let recover : P → AdelicGroupPoints F G × AdelicGroupPoints F G :=
    fun p => ((p : AdelicGroupPoints F G) * (f p)⁻¹, f p)
  have hrecover : Continuous recover :=
    (continuous_subtype_val.mul hf.inv).prodMk hf
  have hcomp : recover ∘ product = Prod.map ιN ιM := by
    funext x
    change (ιN x.1 * ιM x.2 * (f (product x))⁻¹, f (product x)) = (ιN x.1, ιM x.2)
    rw [hproject, mul_inv_cancel_right]
  exact IsEmbedding.subtypeVal.comp
    (IsEmbedding.of_comp hproduct hrecover (hcomp.symm ▸ hN.prodMap hM))

include hS in
/-- Restrict the minimal Levi's split-component coordinates to positive points of the derived
split subtorus. The resulting embedding gives the specified ambient Levi and torus product. -/
private theorem exists_leviNormOnePositiveEmbedding :
    ∃ lift : normOneSubgroup F (Standard.leviScheme i ν ∅) ×
        PositiveRealTorus.intrinsicSubgroup F T₀ →
          AdelicGroupPoints F (Standard.leviScheme i ν ∅),
      IsEmbedding lift ∧
        ∀ x, map F _ G (Standard.leviHom i ν ∅) (lift x) =
          map F _ G (Standard.leviHom i ν ∅) x.1 * positiveMap F G T i T₀ j x.2 := by
  obtain ⟨hTmax, -, -, hRL, -, hlevi, -, ⟨D, d, t₀, hd, hT₀max, ht₀⟩, -⟩ := hS
  let M := Standard.leviScheme i ν ∅
  let t := torusToStandardLevi F G T i ν
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  have : IsAffineHom M.X.hom := hMc.isAffineHom
  have hmax : IsMaximalSplitTorus t :=
    hTmax.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
      (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral t := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi]
  have hsplitM : IsSplitComponent t :=
    ⟨⟨hmax.1, hcent⟩, fun A a ha g hg => hmax.2 A a ha.1 g hg⟩
  let e := PositiveRealTorus.splitComponentNormOneDecomposition
    centralSplitTorusCharacter F M hRL.isConnectedReductive T t hsplitM
  have hjG : IsClosedSubgroup (CommGroupScheme.groupHom j ≫ i) :=
    ht₀ ▸ hT₀max.1.2.comp hd.1
  have hj : IsClosedSubgroup (CommGroupScheme.groupHom j) :=
    IsClosedSubgroup.of_comp hTmax.1.2 hjG
  have : IsAffineHom T.toGrp.X.hom := hTmax.1.1.isAffineHom
  have : IsAffineHom T₀.toGrp.X.hom := hT₀max.1.1.isAffineHom
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsAffine T₀.toGrp.X.left := isAffine_of_isAffineHom T₀.toGrp.X.hom
  let torusMap := map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j)
  let positiveInclusion :
      PositiveRealTorus.intrinsicSubgroup F T₀ → PositiveRealTorus.intrinsicSubgroup F T :=
    fun a => ⟨torusMap a, PositiveRealTorus.map_intrinsicSubgroup_le F T₀ T j ⟨a, a.property, rfl⟩⟩
  have htorusMap : IsEmbedding torusMap :=
    (isClosedEmbedding_map_of_isClosedSubgroup F _ hj).isEmbedding
  have hval : IsEmbedding (Subtype.val :
      PositiveRealTorus.intrinsicSubgroup F T → AdelicGroupPoints F T.toGrp) :=
    IsEmbedding.subtypeVal
  have hpositive : IsEmbedding positiveInclusion :=
    hval.of_comp_iff.mp (htorusMap.comp IsEmbedding.subtypeVal)
  have hpair : IsEmbedding (fun x : normOneSubgroup F M × PositiveRealTorus.intrinsicSubgroup F T₀ =>
      (positiveInclusion x.2, x.1)) :=
    (hpositive.prodMap IsEmbedding.id).comp (Homeomorph.prodComm _ _).isEmbedding
  refine ⟨fun x => e (positiveInclusion x.2, x.1), e.toHomeomorph.isEmbedding.comp hpair, ?_⟩
  intro x
  change map F M G (Standard.leviHom i ν ∅) (e (positiveInclusion x.2, x.1)) = _
  have hc := PositiveRealTorus.positivePointMap_commute F M T t hcent (positiveInclusion x.2)
    (x.1 : AdelicGroupPoints F M)
  rw [PositiveRealTorus.splitComponentNormOneDecomposition_apply, hc.eq, map_mul]
  congr 1
  rw [PositiveRealTorus.positivePointMap_apply, ← adelicPointsMap_comp_apply, torusToStandardLevi_comp]
  exact (adelicPointsMap_comp_apply F G (CommGroupScheme.groupHom j) i x.2).symm

end Embeddings

/-- Ordered multiplication gives the coordinate homeomorphism onto the part of the minimal
parabolic cut out by the ambient norm-one condition. -/
theorem minimalParabolicNormCoordinates : MinimalParabolicNormCoordinatesStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS
  let N := Standard.unipotentScheme i ν ∅
  let M := Standard.leviScheme i ν ∅
  let P := standardParabolicImage F G T i ν
  let ιN := map F N G (Standard.unipotentHom i ν ∅)
  let ιM := map F M G (Standard.leviHom i ν ∅)
  let positive := positiveMap F G T i T₀ j
  have hn : ιN.toMonoidHom.range ≤ normOneSubgroup F G :=
    range_le_normOne_of_charactersTrivialAlong F N G _
      (hS.charactersTrivialAlong_unipotent F G T i ν T₀ j)
  have hm := map_normOneSubgroup_le F M G (Standard.leviHom i ν ∅)
  have hnP := standardUnipotentImage_le_parabolic F G T i ν
  have hmP := standardLeviImage_le_parabolic F G T i ν
  have haP := positiveMap_mem_standardLeviImage F G T i ν T₀ j
  let product : AdelicGroupPoints F N ×
      (normOneSubgroup F M × PositiveRealTorus.intrinsicSubgroup F T₀) →
        standardParabolicNormOneImage F G T i ν :=
    fun x => ⟨⟨ιN x.1 * ιM x.2.1 * positive x.2.2,
      (normOneSubgroup F G).mul_mem
        ((normOneSubgroup F G).mul_mem (hn ⟨x.1, rfl⟩) (hm ⟨x.2.1, x.2.1.property, rfl⟩))
        (hS.positiveMap_mem_normOne F G T i ν T₀ j x.2.2)⟩,
      P.mul_mem (P.mul_mem (hnP ⟨x.1, rfl⟩) (hmP ⟨x.2.1, rfl⟩)) (hmP (haP x.2.2))⟩
  obtain ⟨lift, hlift, hlift_eq⟩ := exists_leviNormOnePositiveEmbedding F G T i ν T₀ j hS
  let coeAmbient : standardParabolicNormOneImage F G T i ν → AdelicGroupPoints F G :=
    fun p => ((p : normOneSubgroup F G) : AdelicGroupPoints F G)
  have hcoe : IsEmbedding coeAmbient := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hcomp : coeAmbient ∘ product =
      (fun x : AdelicGroupPoints F N × AdelicGroupPoints F M => ιN x.1 * ιM x.2) ∘
        Prod.map id lift := by
    funext x
    change ιN x.1 * ιM x.2.1 * positive x.2.2 = ιN x.1 * ιM (lift x.2)
    rw [hlift_eq x.2, mul_assoc]
  have hemb : IsEmbedding product := hcoe.of_comp_iff.mp (by
    rw [hcomp]
    exact (isEmbedding_unipotentLeviProduct F G T i ν T₀ j hS).comp
      (IsEmbedding.id.prodMap hlift))
  have hsurj : Function.Surjective product := by
    intro p
    obtain ⟨n, m, a, heq⟩ := hS.hasMinimalParabolicNormFactors F G T i ν T₀ j hG p.1 p.2
    exact ⟨(n, m, a), Subtype.ext (Subtype.ext heq)⟩
  exact ⟨hemb.toHomeomorphOfSurjective hsurj, fun _ => rfl⟩

end Langlands.Global.AdelicSiegelFactors
