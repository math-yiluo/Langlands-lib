import Langlands.BruhatTits.IntegralModels.UnramifiedTorusClauseStatement
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.GroupScheme.Torus.HenselianSplitRank
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # The integral split torus clause for a supplied descended model -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.BruhatTits.IntegralModels

local instance {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

private def commIsoToGroupIso {B : Scheme.{u}} {T T' : CommGroupScheme B}
    (e : T ≅ T') : T.toGrp ≅ T'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id

private theorem maximalSplitTorus_iso_comp
    {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (e : T.toGrp ≅ T'.toGrp) {i : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) : IsMaximalSplitTorus (e.hom ≫ i) := by
  refine ⟨⟨IsSplitTorus.of_iso e hi.1.1, hi.1.2.iso_comp e⟩, ?_⟩
  intro A a ha f hf
  have hfac : (e.inv ≫ f) ≫ a = i := by
    rw [Category.assoc, hf, Iso.inv_hom_id_assoc]
  have h := hi.2 A a ha (e.inv ≫ f) hfac
  exact (isIso_comp_left_iff e.inv f).mp h

/-- The exact integral split torus clause for a supplied descended parahoric model. -/
theorem unramifiedTorusClause : UnramifiedTorusClauseStatement.{u} := by
  intro F _ _ _ _ G _ hG S iS hiS C E Ya _hYa _hbounded hfixed g D hD
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  let b := baseMap F (inertiaFixedField F)
  let i := iS ≫ (G.innerIso g).hom
  have hi : IsMaximalSplitTorus i := hiS.comp_iso (G.innerIso g)
  have hb : (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) S.toGrp)).map
        (rationalPoints.map ((GroupScheme.baseChange b).map i)) ≤
      D.neutral.baseChangeUnramified.integralPoints := by
    rw [hD]
    rintro _ ⟨s, hs, rfl⟩
    have hconj :
        rationalPoints.map ((GroupScheme.baseChange b).map i) s =
          rationalExtend F (inertiaFixedField F) G g *
            rationalPoints.map ((GroupScheme.baseChange b).map iS) s *
              (rationalExtend F (inertiaFixedField F) G g)⁻¹ := by
      dsimp only [i]
      rw [Functor.map_comp, baseChange_innerIso_hom,
        ← rationalExtend_eq_baseChangeBasePoint]
      change rationalPoints.map
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)).hom
        (rationalPoints.map ((GroupScheme.baseChange b).map iS) s) = _
      rw [rationalPoints_map_innerIso]
      rfl
    rw [hconj]
    constructor
    · apply E.normal_zeroPoints.conj_mem
      exact E.map_split_characterValuationKernel_le_zeroPoints hGK
        ((CommGroupScheme.baseChange b).obj S)
        ((GroupScheme.baseChange b).map iS)
        ⟨hiS.1.1.baseChange b, hiS.1.2.baseChange b⟩ ⟨s, hs, rfl⟩
    · change _ ∈ C.apartment.pointwiseFixer _
      rw [KPApartmentData.mem_pointwiseFixer]
      rintro _ ⟨x, hx, rfl⟩
      simpa only [mul_smul, inv_smul_smul] using
        congrArg (fun y => rationalExtend F (inertiaFixedField F) G g • y)
          (hfixed s hs x hx)
  have hv (a : (fixedFieldIntegers F)ˣ) :
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 :=
    (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr
      ((Langlands.LocalGalois.Separable.isUnit_iff_eq_one (fixedFieldValuation F)
        (a : fixedFieldIntegers F)).mp a.isUnit)
  obtain ⟨𝒮, j, e, h𝒮, hj, hgen⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange
      D.neutral (fixedFieldIntegers F) (inertiaFixedField F)
      (MaximalUnramified.valuation F) hv
      (fun x hx => (IntegralModel.unramifiedIntegerRange_intersection x).mp hx)
      i hi.1.1 hi.1.2 hb
  let T : IntegralTorusData D S i :=
    { torus := 𝒮
      genericIso := commIsoToGroupIso e
      inclusion := j
      generic_comm := hgen }
  refine ⟨T, ⟨h𝒮, hj⟩, ?_⟩
  have hjK : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮)
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map j) := by
    apply (IsMaximalSplitTorus.comp_iso_iff _ D.neutral.genericIso).mp
    change IsMaximalSplitTorus (D.neutral.genericTorusMap 𝒮 j)
    rw [hgen]
    exact maximalSplitTorus_iso_comp (commIsoToGroupIso e) hi
  exact isMaximalSplitTorus_residue_of_generic
    (IsLocalRing.residue_surjective : Function.Surjective
      (algebraMap ↥𝒪[F] (IsLocalRing.ResidueField ↥𝒪[F])))
    D.neutral.group (hG.of_iso D.neutral.genericIso) 𝒮 h𝒮 j hj hjK

end Langlands.BruhatTits.IntegralModels
