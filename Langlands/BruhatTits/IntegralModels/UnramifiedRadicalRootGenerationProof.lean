import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalConjugation
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalDescent

/-! # Radical generation for descended maximal-unramified models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

private instance radicalReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

private theorem smooth_baseChangeUnramified {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ↥𝒪[F] F G) (hM : M.IsSmooth) :
    M.baseChangeUnramified.IsSmooth := by
  let : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
    Valuation.HasExtension.instAlgebraInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  let : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  exact M.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hM

set_option maxHeartbeats 1600000 in
private theorem radicalPreimage_eq_conjugate
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hMs : M.IsSmooth) (Ω : Set C.Apartment) (g : rationalPoints G)
    (hM : M.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ω))
    (H : Subgroup (rationalPoints G))
    (hgen : ∀ (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G),
      N.IsSmooth →
      N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      ∀ (U : GroupScheme
          (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
        (i : U ⟶ N.specialFibre), IsUnipotentRadical i →
        N.specialFibreSubgroupPoints (rationalPoints.map i).range =
          H ⊔ ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a Ω)
    (U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
    (i : U ⟶ M.specialFibre) (hi : IsUnipotentRadical i) :
    M.specialFibreSubgroupPoints (rationalPoints.map i).range =
      (H ⊔ ⨆ a : relativeRoots C.i, C.rootFixerPlus a Ω).map
        (MulAut.conj g).toMonoidHom := by
  let N := M.transport (G.innerIso g⁻¹)
  have hNpoints : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) :=
    M.integralPoints_transport_innerIso_same_zeroDatum C E g Ω hM
  have hNgen : N.specialFibreSubgroupPoints (rationalPoints.map i).range =
      H ⊔ ⨆ a : relativeRoots C.i, C.apartment.rootFixerPlus a Ω :=
    hgen N hMs hNpoints U i hi
  exact (M.specialFibreSubgroupPoints_eq_map_innerIso
    (rationalPoints.map i).range g).trans
      (congrArg (fun P => P.map (MulAut.conj g).toMonoidHom) hNgen)

set_option maxHeartbeats 1600000 in
/-- The upstairs root-generation formula implies the descended target,
using the actual unramified radical-identification theorem. -/
theorem unramifiedRadicalRootGeneration_of_upstairs
    (hup : UnramifiedUpstairsRadicalRootGenerationStatement.{u}) :
    UnramifiedRadicalRootGenerationStatement.{u} := by
  intro F _ _ _ _ G _ C E
  obtain ⟨H, hH, _, hgen⟩ :=
    hup F (baseChanged F (inertiaFixedField F) G) C E
  refine ⟨H, hH, ?_⟩
  intro Ω hΩ hfacet g D hDs hD Q hQ
  obtain ⟨U, i, hi, hki⟩ := Q.exists_unramifiedRadical hQ
  have hMgen := radicalPreimage_eq_conjugate C E D.neutral.baseChangeUnramified
    (smooth_baseChangeUnramified D.neutral hDs) Ω g hD H
    (hgen Ω hΩ hfacet) U i hi
  exact (Q.positivePoints_eq_comap_unramifiedKernelPoints hQ.2.1).trans
    (congrArg (fun P => P.comap (rationalExtend F (inertiaFixedField F) G))
      (hki.trans hMgen))

/-- One common centralizer subgroup and the positive root fixers generate
all descended radical preimages, with the original quantifiers and hypotheses. -/
theorem unramifiedRadicalRootGeneration :
    UnramifiedRadicalRootGenerationStatement.{u} :=
  unramifiedRadicalRootGeneration_of_upstairs
    unramifiedUpstairsRadicalRootGeneration

end Langlands.BruhatTits.IntegralModels
