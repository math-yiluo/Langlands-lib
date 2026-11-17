import Langlands.BruhatTits.IntegralModels.UnramifiedComponentModelComparison
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetModelAttainment
import Langlands.BruhatTits.IntegralModels.UnramifiedPairTorusImages
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.ResidueSplitTorusGenericLift

/-! # Split-source lifts from a recovered pair to a recovered reference facet -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3200000

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance pairFacetExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local instance pairFacetIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance pairFacetIntegerTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

variable
  (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (Z : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (D₀ D₁ : RelativeComponentModelData ↥𝒪[F] F G)
  (E₀ E₁ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (p q : B.ReducedBuilding) (Fc : B.BuildingFacet)

/-- Actual recovered pair and reference-facet models lift the same integral
split source, with its prescribed reference-quotient map and fixed-point units. -/
def UnramifiedPairFacetSplitSourceStatement : Prop :=
  Nonempty (UnramifiedComponentModelRecovery D₀ E₀) →
  Nonempty (UnramifiedComponentModelRecovery D₁ E₁) →
  IsConnectedReductive G → p ∈ Fc.val →
  E₀.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓ B.pointwiseFixer {p, q} →
  E₀.neutral.integralPoints = Z.zeroPoints ⊓ B.pointwiseFixer {p, q} →
  E₁.neutral.integralPoints = Z.zeroPoints ⊓ B.pointwiseFixer Fc.val →
  ∀ (Q : SpecialFibreQuotientData D₁), Q.IsReductiveQuotient →
    (∀ (P : GroupScheme (Spec (CommRingCat.of 𝓀[F]))) (i : P ⟶ Q.quotient),
      IsParabolicSubgroup i → IsIso i) →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))),
      IsSplitTorus S.toGrp →
      ∀ (a : ((CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj S).toGrp ⟶ G),
        IsMaximalSplitTorus a →
        ∀ (s : ((CommGroupScheme.baseChange
          (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj S).toGrp ⟶ Q.quotient),
          IsMaximalSplitTorus s →
          ∃ (φ : D₀.neutral.Hom D₁.neutral (𝟙 G))
            (j : S.toGrp ⟶ D₀.neutral.group),
            IsClosedSubgroup j ∧
            (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).map j ≫
              φ.specialFibreMap ≫ Q.projection = s ∧
            IsMaximalSplitTorus
              (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj S)
              ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).map j) ∧
            IsMaximalSplitTorus (D₀.neutral.genericTorusMap S j) ∧
            IsFixedByUnramifiedTorusUnits F (D₀.neutral.genericTorusMap S j) q

/-- Use zero-facet no inversions for the comparison, full-pair maximal-torus
preservation for its residue map, and the published same-source lift. -/
theorem unramifiedPairFacetSplitSource :
    UnramifiedPairFacetSplitSourceStatement B Z D₀ D₁ E₀ E₁ p q Fc := by
  rintro ⟨e₀⟩ ⟨e₁⟩ hG hp hfull hpair hfacet Q hQ hpar S hS a ha s hs
  have hle : E₀.neutral.integralPoints ≤ E₁.neutral.integralPoints := by
    rw [hpair, hfacet,
      ← Z.zeroFixer_eq_of_nonempty_subset_buildingFacet B
        MaximalUnramified.zeroFacetNoInversions (Set.singleton_nonempty p)
        (Set.singleton_subset_iff.mpr hp)]
    intro g hg
    refine ⟨hg.1, B.apartment.mem_pointwiseFixer.mpr ?_⟩
    intro y hy
    have hy' : y = p := Set.mem_singleton_iff.mp hy
    subst y
    exact B.apartment.mem_pointwiseFixer.mp hg.2 p (Set.mem_insert p {q})
  obtain ⟨φ⟩ := (e₀.nonempty_neutralHom_iff e₁
    IntegralModel.unramifiedSmoothHomExtension).mpr hle
  let : Smooth D₀.neutral.group.X.hom := D₀.neutral_smooth
  let : Smooth D₁.neutral.group.X.hom := D₁.neutral_smooth
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom D₁.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd D₁.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : LocallyOfFiniteType D₁.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D₁.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  have hbound : characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) ⊓ B.pointwiseFixer {p, q} ≤
        D₀.full.baseChangeUnramified.integralPoints := by
    rw [e₀.full_integralPoints_eq, hfull]
  have hmax : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of 𝓀[F])))
      (i : T'.toGrp ⟶ D₀.neutral.specialFibre),
      IsMaximalTorus i → IsMaximalTorus (i ≫ φ.specialFibreMap ≫ Q.projection) := by
    intro T' i hi
    have hi' := isMaximalTorus_specialFibreMap_of_unramified_full_pair
      B D₀ p q hbound φ hi
    simpa only [Category.assoc] using
      hi'.comp_of_perfect_field_unipotent_kernel Q.radicalInclusion
        hQ.1.isClosedSubgroup hQ.1.isUnipotent Q.projection hQ.2.1
  have hfix : ∀ g ∈ D₀.neutral.baseChangeUnramified.integralPoints, g • q = q := by
    intro g hg
    rw [e₀.neutral_integralPoints_eq, hpair] at hg
    exact B.apartment.mem_pointwiseFixer.mp hg.2 q (by simp)
  obtain ⟨j, hj, hjs, hjres, hjgen, hjfix⟩ :=
    D₀.neutral.exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits
      hG S hS a ha Q.quotient (φ.specialFibreMap ≫ Q.projection) hmax
      hQ.2.2 hpar s hs q hfix
  exact ⟨φ, j, hj, hjs, hjres, hjgen, hjfix⟩

end Langlands.BruhatTits.IntegralModels
