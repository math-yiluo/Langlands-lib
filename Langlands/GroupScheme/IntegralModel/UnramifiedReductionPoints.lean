import Langlands.GroupScheme.IntegralModel.TorusModelPowerIntegrality
import Langlands.GroupScheme.IntegralModel.SemilinearPoints
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.IdentityComponentRationalGalois

/-! # Unramified descent of special-fibre kernel preimages -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme.Descent

/-- Transport a morphism on an intermediate fibre through a commuting
pullback square. -/
irreducible_def squareComparisonMap {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B)
    {H : GroupScheme U} (q : (baseChange d).obj G ⟶ H) :
    (baseChange c).obj ((baseChange b).obj G) ⟶ (baseChange e).obj H :=
  (squareComparison b c d e h G).hom ≫ (baseChange e).map q

/-- The commuting-square comparison also respects a morphism on the
intermediate fibre. -/
theorem squareComparison_section_map {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B)
    {H : GroupScheme U} (q : (baseChange d).obj G ⟶ H)
    (x : Over.mk (𝟙 B) ⟶ G.X) :
    baseChangeSectionHom c ((baseChange b).obj G)
        (baseChangeSectionHom b G x) ≫
        (squareComparisonMap b c d e h G q).hom.hom =
      baseChangeSectionHom e H
        (baseChangeSectionHom d G x ≫ q.hom.hom) := by
  rw [squareComparisonMap_def]
  change _ ≫ ((squareComparison b c d e h G).hom.hom.hom ≫
    ((baseChange e).map q).hom.hom) = _
  rw [← Category.assoc, squareComparison_section]
  exact (baseChangeSectionHom_naturality e q
    (baseChangeSectionHom d G x)).symm

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel

section KernelPoints

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}

/-- The generic image of sections whose reduction is killed by an actual
special-fibre morphism. -/
def specialFibreKernelPoints (q : M.specialFibre ⟶ H) :
    Subgroup (rationalPoints G) :=
  ((rationalPoints.map q).comp M.reduction).ker.map M.integralPointMap

theorem mem_specialFibreKernelPoints (q : M.specialFibre ⟶ H)
    (g : rationalPoints G) :
    g ∈ M.specialFibreKernelPoints q ↔
      ∃ x : M.integralSections,
        rationalPoints.map q (M.reduction x) = 1 ∧ M.integralPointMap x = g :=
  Iff.rfl

end KernelPoints

open Langlands.LocalGalois.Separable GaloisPointComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

variable {H : GroupScheme (Spec (CommRingCat.of 𝓀[F]))}

private theorem unramifiedResidueBaseMap_comp :
    residueBaseMap (fixedFieldIntegers F) ≫
        Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) =
      Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) ≫
        residueBaseMap ↥𝒪[F] :=
  unramifiedResidue_specMap_comp

/-- Extend a special-fibre morphism through the actual unramified residue-fibre
comparison. -/
def unramifiedSpecialFibreMap (q : M.specialFibre ⟶ H) :
    M.baseChangeUnramified.specialFibre ⟶
      (GroupScheme.baseChange (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj H :=
  Descent.squareComparisonMap
      (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      (residueBaseMap (fixedFieldIntegers F))
      (residueBaseMap ↥𝒪[F])
      (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
      unramifiedResidueBaseMap_comp M.group q

/-- Reduction of an extended integral section commutes with every supplied
special-fibre morphism. -/
theorem unramifiedSpecialFibreMap_reduction
    (q : M.specialFibre ⟶ H) (x : M.integralSections) :
    rationalPoints.map (M.unramifiedSpecialFibreMap q)
        (M.baseChangeUnramified.reduction
          (baseChangeSectionHom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
            M.group x)) =
      baseChangeSectionHom (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) H
          (rationalPoints.map q (M.reduction x)) := by
  exact Descent.squareComparison_section_map
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (residueBaseMap (fixedFieldIntegers F))
    (residueBaseMap ↥𝒪[F])
    (Spec.algebraMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
    unramifiedResidueBaseMap_comp M.group q x

private theorem residueSection_injective [IsAffineHom H.X.hom] :
    Function.Injective
      (baseChangeSectionHom (Spec.algebraMap 𝓀[F]
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) H) := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  intro x y hxy
  apply (rationalCoeffEquiv 𝓀[F] H).injective
  apply GaloisPoint.extend_injective 𝓀[F]
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) H
  have h := congrArg (baseChangeCoeffEquiv 𝓀[F]
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) H) hxy
  simpa only [← rationalExtend_eq_baseChangeSectionHom,
    baseChangeCoeffEquiv_rationalExtend] using h

/-- Vanishing under the special-fibre morphism can be tested after actual
maximal-unramified extension. -/
theorem unramifiedSpecialFibreMap_reduction_eq_one_iff [IsAffineHom H.X.hom]
    (q : M.specialFibre ⟶ H) (x : M.integralSections) :
    rationalPoints.map (M.unramifiedSpecialFibreMap q)
        (M.baseChangeUnramified.reduction
          (baseChangeSectionHom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
            M.group x)) = 1 ↔
      rationalPoints.map q (M.reduction x) = 1 := by
  rw [M.unramifiedSpecialFibreMap_reduction q x]
  exact (residueSection_injective (H := H)).eq_iff' (map_one _)

/-- The extended integral section evaluates to the existing extension of its
generic point. -/
theorem baseChangeUnramified_integralPointMap (x : M.integralSections) :
    M.baseChangeUnramified.integralPointMap
        (baseChangeSectionHom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
          M.group x) =
      rationalExtend F (inertiaFixedField F) G (M.integralPointMap x) :=
  (M.baseChange_integralPointMap (fixedFieldIntegers F) (inertiaFixedField F) x).trans
    (rationalExtend_eq_baseChangeSectionHom F (inertiaFixedField F)
      (M.integralPointMap x)).symm

/-- The generic image of a special-fibre kernel is the exact preimage of the
extended kernel image under actual maximal-unramified scalar extension. -/
theorem specialFibreKernelPoints_eq_comap_unramified [IsAffineHom H.X.hom]
    (q : M.specialFibre ⟶ H) :
    M.specialFibreKernelPoints q =
      (M.baseChangeUnramified.specialFibreKernelPoints
        (M.unramifiedSpecialFibreMap q)).comap
          (rationalExtend F (inertiaFixedField F) G) := by
  ext g
  change
    (∃ x : M.integralSections,
      rationalPoints.map q (M.reduction x) = 1 ∧ M.integralPointMap x = g) ↔
    ∃ y : M.baseChangeUnramified.integralSections,
      rationalPoints.map (M.unramifiedSpecialFibreMap q)
        (M.baseChangeUnramified.reduction y) = 1 ∧
      M.baseChangeUnramified.integralPointMap y =
        rationalExtend F (inertiaFixedField F) G g
  constructor
  · rintro ⟨x, hx, hg⟩
    refine ⟨baseChangeSectionHom
      (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) M.group x,
      (M.unramifiedSpecialFibreMap_reduction_eq_one_iff q x).mpr hx, ?_⟩
    exact (M.baseChangeUnramified_integralPointMap x).trans
      (congrArg (rationalExtend F (inertiaFixedField F) G) hg)
  · rintro ⟨y, hy, hg⟩
    have hint : rationalExtend F (inertiaFixedField F) G g ∈
        M.baseChangeUnramified.integralPoints := ⟨y, hg⟩
    obtain ⟨x, hx⟩ :=
      (M.mem_integralPoints_rationalExtend_iff_unramified g).mp hint
    have hxy : baseChangeSectionHom
        (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) M.group x = y := by
      apply M.baseChangeUnramified.integralPointMap_injective
      exact (M.baseChangeUnramified_integralPointMap x).trans
        ((congrArg (rationalExtend F (inertiaFixedField F) G) hx).trans hg.symm)
    refine ⟨x, (M.unramifiedSpecialFibreMap_reduction_eq_one_iff q x).mp ?_, hx⟩
    rwa [hxy]

end Langlands.GroupScheme.IntegralModel
