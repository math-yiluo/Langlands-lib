import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerStatement
import Langlands.Geometry.Building.SplitIntegralPinningSpecialStabilizer
import Langlands.Geometry.Building.SplitIntegralPinningOfRoots
import Langlands.Geometry.Building.RegularUnitExistence
import Langlands.GroupScheme.IntegralModel.StrictHenselianModelPinning
import Langlands.GroupScheme.IntegralModel.UnramifiedGenericSplitTorus
import Langlands.GroupScheme.IntegralModel.UnramifiedModelClassification
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Reductive.LocalSplitRootGroupProof
import Langlands.LinearAlgebra.RootDatumBaseExists
import Langlands.Galois.Local.SeparableHenselian
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # The special-stabilizer identity after maximal unramified base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

/-- Given a split integral pinning over the maximal unramified extension whose integral
subgroup is the image of the model, with an Iwasawa decomposition along a generic
cocharacter, the special-stabilizer identity holds for every supplied building data. -/
theorem unramifiedSpecialStabilizer_of_pinning {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom]
    (M : IntegralModel ↥𝒪[F] F G)
    (hP : ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (i : (SplitIntegralPinning.coordTorus (inertiaFixedField F) I).toGrp ⟶
        baseChanged F (inertiaFixedField F) G),
      IsMaximalSplitTorus i ∧ IsMaximalTorus i ∧
      ∃ (_ : Mono i.hom.hom.left) (P : SplitIntegralPinning (MaximalUnramified.valuation F) i),
        P.K = M.baseChangeUnramified.integralPoints ∧
        ∃ ν, IsGenericCocharacter i ν ∧ ∀ g, ∃ κ ∈ P.K,
          ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
            (Over.mk (𝟙 _)), g = κ * p)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)) :
    ∃ x : C.ReducedBuilding, C.IsSpecialPoint x ∧
      M.baseChangeUnramified.integralPoints = C.oneStabilizer x ∧
      ∀ y : C.ReducedBuilding,
        (∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
          g ∈ M.baseChangeUnramified.integralPoints → g • y = y) → y = x := by
  obtain ⟨I, _, _, i, hsplit, hmax, _, P, hPK, ν, hν, hIw⟩ := hP
  have := MaximalUnramified.infinite_residueField F
  obtain ⟨x, hx, hK, huniq⟩ :=
    C.exists_isSpecialPoint_eq_oneStabilizer_of_pinning hsplit hmax P ν hν hIw
  refine ⟨x, hx, hPK ▸ hK, fun y hy => huniq y fun g hg => hy g (hPK ▸ hg)⟩

/-- **Split integral pinning of the maximal unramified base change.** For a good model `M`
(connected reductive generic fibre and special fibre), the base change
`M.baseChangeUnramified` has a closed coordinate split torus whose generic fibre is a maximal
split and maximal torus of `G_L` carrying a split integral pinning with subgroup the integral
points of `M.baseChangeUnramified`, together with a generic cocharacter along which these
integral points give an Iwasawa decomposition. -/
theorem exists_splitIntegralPinning_baseChangeUnramified {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (M : IntegralModel ↥𝒪[F] F G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (i : (SplitIntegralPinning.coordTorus (inertiaFixedField F) I).toGrp ⟶
        baseChanged F (inertiaFixedField F) G),
      IsMaximalSplitTorus i ∧ IsMaximalTorus i ∧
      ∃ (_ : Mono i.hom.hom.left) (P : SplitIntegralPinning (MaximalUnramified.valuation F) i),
        P.K = M.baseChangeUnramified.integralPoints ∧
        ∃ ν, IsGenericCocharacter i ν ∧ ∀ g, ∃ κ ∈ P.K,
          ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
            (Over.mk (𝟙 _)), g = κ * p := by
  classical
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  have hN := M.isReductive_baseChangeUnramified hG hSpecial
  have hH : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  let := hN.smooth
  let := hN.isAffineHom
  obtain ⟨I, _, i, hic, hmax⟩ :=
    exists_coordinate_fibrewiseMaximalTorus_of_strictHenselian (fixedFieldIntegers F)
      M.baseChangeUnramified.group hN
  obtain ⟨J, P, hP⟩ :=
    localSplitFibrewiseRootDatumExistence _ M.baseChangeUnramified.group hN I i hic hmax
  have := hP.finite
  have := hP.isReduced
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨u, hu, hw⟩ :=
    localSplitRootGroup _ M.baseChangeUnramified.group hN I i hic hmax J P hP b
  have hsplit := M.baseChangeUnramified.isMaximalSplitTorus_genericSplitTorusHom i hmax
  obtain ⟨hmono, Pin, hPin⟩ :=
    M.baseChangeUnramified.exists_splitIntegralPinning_genericSplitTorusHom
      (MaximalUnramified.valuation F) MaximalUnramified.valuation_le_one_iff_mem_range hH hN
      i hic hmax P hP b u hu hw
      (fun t ht hk => M.baseChangeUnramified_map_genericSplitTorusHom_mem_integralPoints hH i
        hic hsplit t ht hk)
  refine ⟨I, inferInstance, inferInstance, M.baseChangeUnramified.genericSplitTorusHom i,
    hsplit, M.baseChangeUnramified.isMaximalTorus_genericSplitTorusHom i hmax, hmono, Pin, hPin,
    SplitIntegralPinning.doubleRhoCheck P b,
    SplitIntegralPinning.isGenericCocharacter_doubleRhoCheck
      (M.baseChangeUnramified.isRootDatumOf_genericSplitTorusHom i hP) b, fun g => ?_⟩
  rw [hPin]
  exact M.baseChangeUnramified_exists_integral_mul_parabolic_genericSplitTorus hG hSpecial i _ g

/-- **The unramified special-stabilizer identity** (Bruhat–Tits II, Propositions 4.6.31,
4.6.28(i) and 4.6.29(i)). -/
theorem unramifiedSpecialStabilizer : UnramifiedSpecialStabilizerStatement.{u} := by
  intro F _ _ _ _ G hG M hSpecial C
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact M.unramifiedSpecialStabilizer_of_pinning
    (M.exists_splitIntegralPinning_baseChangeUnramified hG hSpecial) C

end Langlands.GroupScheme.IntegralModel
