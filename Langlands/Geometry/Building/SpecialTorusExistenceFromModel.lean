import Langlands.Geometry.Building.SpecialTorusIntegralModelStatement
import Langlands.GroupScheme.Rational.CommutingTorusImage
import Langlands.GroupScheme.Rational.SplitRankMaximality
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Torus.HenselianSubgroupLifting
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.ResidueRankComparison
import Langlands.GroupScheme.Torus.StrictHenselianRelativeSplit
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.IntegralModel.TorusModelPowerIntegrality
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.Galois.Local.SeparableHenselian
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Special tori from an adapted smooth model (KP Proposition 9.3.4) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Commute

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Points of a generic torus `S` commute with the generic fibre of anything lying in the
centralizer of an integral extension `𝒮` of `S`. -/
theorem _root_.Langlands.GroupScheme.IntegralModel.commute_generic_of_torusCentralizer
    {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {iS : S.toGrp ⟶ G}
    (𝒮 : CommGroupScheme (Spec (CommRingCat.of R))) (j : 𝒮.toGrp ⟶ M.group)
    (eS : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮 ≅ S)
    (hgen : M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom eS.hom ≫ iS)
    {Z : GroupScheme (Spec (CommRingCat.of R))} {z : Z ⟶ M.group}
    (hZrep : (torusCentralizer j).IsRepresentedBy z)
    {𝒯 : GroupScheme (Spec (CommRingCat.of R))} (i : 𝒯 ⟶ Z)
    (U : Over (Spec (CommRingCat.of K))) (x : U ⟶ S.X)
    (y : U ⟶ ((GroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯).X) :
    Commute (x ≫ iS.hom.hom)
      (y ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map (i ≫ z) ≫
        M.genericIso.hom).hom.hom) := by
  have hZF : (torusCentralizer (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j)).IsRepresentedBy
        ((GroupScheme.baseChange (Spec.algebraMap R K)).map z) := by
    rw [torusCentralizer_baseChange]
    exact hZrep.baseChange _
  have hmem : (y ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map i).hom.hom) ≫
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map z).hom.hom ∈
        (torusCentralizer (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒮)
          ((GroupScheme.baseChange (Spec.algebraMap R K)).map j)).carrier U := by
    rw [← hZF.2]
    exact ⟨_, rfl⟩
  have hc := hmem U (𝟙 U) (x ≫ (CommGroupScheme.groupHom eS.inv).hom.hom)
  rw [Category.id_comp] at hc
  have hiS : CommGroupScheme.groupHom eS.inv ≫
      (GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ M.genericIso.hom = iS := by
    change CommGroupScheme.groupHom eS.inv ≫ M.genericTorusMap 𝒮 j = iS
    rw [hgen, ← Category.assoc]
    change CommGroupScheme.groupHom (eS.inv ≫ eS.hom) ≫ iS = iS
    rw [Iso.inv_hom_id]
    exact Category.id_comp iS
  rw [← hiS]
  have h2 := congrArg (· ≫ M.genericIso.hom.hom.hom) hc.symm.eq
  simp only [MonObj.mul_comp, Category.assoc] at h2
  simp only [Functor.map_comp, Grp.comp_hom_hom, Category.assoc]
  exact h2

end Commute

section Field

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance specialTorusIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialTorusIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance specialTorusResidueAlgebra :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- The generic square `Spec K ⟶ Spec F ⟶ Spec 𝒪[F]` = `Spec K ⟶ Spec O_K ⟶ Spec 𝒪[F]`. -/
theorem specialTorus_genericSquare :
    algebraBaseMap F (inertiaFixedField F) ≫ Spec.algebraMap ↥𝒪[F] F =
      Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) ≫
        Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) := by
  rw [algebraBaseMap, ← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map ?_
  ext x
  rfl

set_option maxHeartbeats 800000 in
/-- **Special tori from an adapted model.** The reduction of KP Proposition 9.3.4 to the
model of `SpecialTorusIntegralModelStatement`, for a fixed local field. -/
theorem exists_specialTorus_of_model
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hS : IsMaximalSplitTorus iS) (M : IntegralModel ↥𝒪[F] F G) (hMsm : M.IsSmooth)
    [ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group).X.left]
    (𝒮 : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))) (j : 𝒮.toGrp ⟶ M.group)
    (eS : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮 ≅ S)
    (h𝒮 : IsSplitTorus 𝒮.toGrp) (hjc : IsClosedSubgroup j)
    (hgen : M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom eS.hom ≫ iS)
    (𝒜 : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
    (a : 𝒜.toGrp ⟶ M.baseChangeUnramified.group) (h𝒜 : IsSplitTorus 𝒜.toGrp)
    (hac : IsClosedSubgroup a)
    (hamax : IsMaximalSplitTorus (M.baseChangeUnramified.genericTorusMap 𝒜 a)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
      CommGroupScheme.groupHom f ≫ iT = iS ∧ IsClosedSubgroup iT ∧
        IsMaximalSplitTorus
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) := by
  let O := ↥𝒪[F]
  let K := inertiaFixedField F
  let s := Spec.algebraMap O 𝓀[F]
  let bF := Spec.algebraMap O F
  let bK := algebraBaseMap F K
  let β := Spec.algebraMap O (fixedFieldIntegers F)
  let γK := Spec.algebraMap (fixedFieldIntegers F) K
  have hMsm' : Smooth M.group.X.hom := hMsm
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  -- The smooth closed centralizer `Z` of `𝒮` in `M`.
  obtain ⟨Z, z, hzc, hZsm, hZrep⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing j h𝒮 hMsm'
  have : Smooth Z.X.hom := hZsm
  have : IsAffineHom Z.X.hom := hzc.isAffineHom_source
  -- A maximal torus `T0` of the special fibre containing `𝒮_k`, inside `Z_k`.
  let Mk := (GroupScheme.baseChange s).obj M.group
  have : Smooth Mk.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd M.group.X.hom s))
  have : IsAffineHom Mk.X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd M.group.X.hom s))
  have hSk : IsTorus ((CommGroupScheme.baseChange s).obj 𝒮).toGrp :=
    (h𝒮.baseChange s).isTorus
  obtain ⟨T0, t0', f0, ht0max, hf0⟩ := EnvelopeInfiniteReduction.exists_isMaximalTorus_factor Mk
    ((GroupScheme.baseChange s).map j) hSk (hjc.baseChange s)
  have hZk : (torusCentralizer (T := (CommGroupScheme.baseChange s).obj 𝒮)
      ((GroupScheme.baseChange s).map j)).IsRepresentedBy ((GroupScheme.baseChange s).map z) := by
    rw [torusCentralizer_baseChange]
    exact hZrep.baseChange s
  have hle := range_le_torusCentralizer_of_factor _ t0' f0 hf0
  let t0 := SubgroupFunctor.IsRepresentedBy.factorHom hZk t0' hle
  have ht0 : t0 ≫ (GroupScheme.baseChange s).map z = t0' :=
    SubgroupFunctor.IsRepresentedBy.factorHom_comp hZk t0' hle
  have ht0c : IsClosedSubgroup t0 :=
    IsClosedSubgroup.of_comp (hzc.baseChange s) (by rw [ht0]; exact ht0max.2.1)
  -- Lift `T0` to a closed relative torus `𝒯` of `Z`.
  let : HenselianLocalRing O := Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer
  obtain ⟨⟨𝒯, i, hic, h𝒯, e, -⟩⟩ :=
    HenselianTorusLifting.nonempty_liftData (R := O) (k := 𝓀[F]) IsLocalRing.residue_surjective Z
      t0 ht0c (IsTorus.isRelativeTorus ht0max.1)
  -- `𝒯` splits over `O_K`.
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  have : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  obtain ⟨I, _, ⟨eT⟩⟩ := RelativeTorus.IsTorus.isSplitTorus_of_isSepClosed (fixedFieldIntegers F)
    (h𝒯.baseChange β)
  -- Rank comparison with the maximal split torus `𝒜` over `O_K`.
  obtain ⟨JA, _, ⟨eA⟩⟩ := h𝒜
  have hsq : Spec.map (CommRingCat.ofHom
        (algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))) ≫ s =
      Spec.algebraMap (fixedFieldIntegers F) (IsLocalRing.ResidueField (fixedFieldIntegers F)) ≫
        β :=
    (IntegralModel.unramifiedResidue_specMap_comp (F := F)).symm
  have hrankA : Nat.card JA ≤ Nat.card I :=
    card_le_card_of_residue_isMaximalTorus hsq M.group ht0max.1 ht0max.2.1 ht0max 𝒯 e I eT
      (a := a) hac JA eA
  -- The generic fibre `T₁` of `𝒯` and its map into `G`.
  let T₁ := (GroupScheme.baseChange bF).obj 𝒯
  let t₁ : T₁ ⟶ G := (GroupScheme.baseChange bF).map (i ≫ z) ≫ M.genericIso.hom
  have ht₁c : IsClosedSubgroup t₁ := ((hic.comp hzc).baseChange bF).comp_iso M.genericIso
  let eT₁ : (GroupScheme.baseChange bK).obj T₁ ≅ splitTorus (Spec (CommRingCat.of K)) I :=
    baseChangeSquareIso specialTorus_genericSquare 𝒯 ≪≫ (GroupScheme.baseChange γK).mapIso eT ≪≫
      splitTorus.baseChangeIso γK I
  -- `S` and `T₁` commute in `G`, since `𝒯` lies in the centralizer `Z` of `𝒮`.
  have hcomm : ∀ (U : Over (Spec (CommRingCat.of F))) (x : U ⟶ S.X) (y : U ⟶ T₁.X),
      Commute (x ≫ iS.hom.hom) (y ≫ t₁.hom.hom) :=
    M.commute_generic_of_torusCentralizer 𝒮 j eS hgen hZrep i
  -- The closed torus `T` generated by `S` and `T₁`.
  have hSK : IsSplitTorus ((GroupScheme.baseChange bK).obj S.toGrp) := hS.1.1.baseChange bK
  have hT₁K : IsSplitTorus ((GroupScheme.baseChange bK).obj T₁) :=
    ⟨I, inferInstance, ⟨eT₁⟩⟩
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨T, iT, f, g, hf, hg, hiTc, hTK⟩ :=
    exists_closedTorus_of_commute K iS t₁ hcomm hSK hT₁K
  obtain ⟨J, _, ⟨eTK⟩⟩ := hTK
  have hIJ : Nat.card I ≤ Nat.card J := by
    refine card_le_card_of_comp_isClosedSubgroup ((GroupScheme.baseChange bK).map g)
      ((GroupScheme.baseChange bK).map iT) ?_ I J eT₁ eTK
    rw [← Functor.map_comp, hg]
    exact ht₁c.baseChange bK
  -- `T_K` has at least the split rank of `G_K`, so it is a maximal split torus.
  have hGK : IsConnectedReductive ((GroupScheme.baseChange bK).obj G) :=
    connectedReductiveFieldExtensionStatement F K G hG
  let eAK : ((CommGroupScheme.baseChange γK).obj 𝒜).toGrp ≅
      splitTorus (Spec (CommRingCat.of K)) JA :=
    (GroupScheme.baseChange γK).mapIso eA ≪≫ splitTorus.baseChangeIso γK JA
  refine ⟨T, iT, f, hf, hiTc, ?_⟩
  exact IsSplitSubtorus.isMaximalSplitTorus_of_card_le
    ((maximalSplitTorusConjugacy K ((GroupScheme.baseChange bK).obj G) hGK).2)
    ⟨⟨J, inferInstance, ⟨eTK⟩⟩, hiTc.baseChange bK⟩ hamax JA J eAK eTK (hrankA.trans hIJ)

end Field

/-- **Special tori exist** (KP Proposition 9.3.4), assuming the adapted smooth model of
`SpecialTorusIntegralModelStatement`. -/
theorem specialTorusExistence_of_integralModel (h : SpecialTorusIntegralModelStatement.{u}) :
    SpecialTorusExistenceStatement.{u} := by
  intro F _ _ _ _ G hG S iS hS
  obtain ⟨M, hMsm, hconn, ⟨𝒮, j, eS, h𝒮, hjc, hgen⟩, ⟨𝒜, a, h𝒜, hac, hamax⟩⟩ :=
    h F G hG S iS hS
  exact exists_specialTorus_of_model hG hS M hMsm 𝒮 j eS h𝒮 hjc hgen 𝒜 a h𝒜 hac hamax

end Langlands.Geometry.Building
