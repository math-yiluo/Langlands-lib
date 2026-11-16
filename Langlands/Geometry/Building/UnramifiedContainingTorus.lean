import Langlands.Geometry.Building.UnramifiedUnitFixedNeutralTorus
import Langlands.GroupScheme.Torus.HenselianContainingMaximal
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # Generic tori containing a prescribed unit-fixed split source -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- A relative integral torus with maximal residue inclusion and a generic
factorization of the original split source. -/
structure UnitFixedContainingTorusData
    (M : IntegralModel ↥𝒪[F] F G) (iS : S.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))
  relativeTorus : RelativeTorus.IsTorus torus.toGrp
  inclusion : torus.toGrp ⟶ M.group
  closed : IsClosedSubgroup inclusion
  residueMaximal : IsMaximalTorus
    (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj torus)
    ((baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).map inclusion)
  sourceHom : S ⟶ (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj torus
  source_comm : CommGroupScheme.groupHom sourceHom ≫ M.genericTorusMap torus inclusion = iS

/-- Extend the closed integral split source to a residue-maximal relative
torus, retaining its factorization over the original field. -/
def unitFixedContainingTorusData
    {M : IntegralModel ↥𝒪[F] F G} {iS : S.toGrp ⟶ G}
    (hM : M.IsSmooth) (A : UnitFixedIntegralTorusData M iS) :
    UnitFixedContainingTorusData M iS := by
  let : HenselianLocalRing ↥𝒪[F] :=
    Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer
  let : Smooth M.group.X.hom := hM
  let L := HenselianTorusLifting.containingMaximalData
    (k := 𝓀[F]) IsLocalRing.residue_surjective A.inclusion A.isSplit A.closed
  refine {
    torus := L.torus
    relativeTorus := L.relativeTorus
    inclusion := L.inclusion
    closed := L.closed
    residueMaximal := L.residueMaximal
    sourceHom := A.genericIso.inv ≫
      Additive.ofMul ((baseChange (Spec.algebraMap ↥𝒪[F] F)).map L.subtorusHom)
    source_comm := ?_ }
  change (CommGroupScheme.groupHom A.genericIso.inv ≫
    (baseChange (Spec.algebraMap ↥𝒪[F] F)).map L.subtorusHom) ≫
      ((baseChange (Spec.algebraMap ↥𝒪[F] F)).map L.inclusion ≫ M.genericIso.hom) = iS
  rw [Category.assoc, ← Category.assoc _ _ M.genericIso.hom,
    ← Functor.map_comp, L.contains]
  change CommGroupScheme.groupHom A.genericIso.inv ≫
    M.genericTorusMap A.torus A.inclusion = iS
  rw [A.generic_comm, ← Category.assoc]
  change CommGroupScheme.groupHom (A.genericIso.inv ≫ A.genericIso.hom) ≫ iS = iS
  rw [Iso.inv_hom_id]
  exact Category.id_comp _

namespace UnitFixedContainingTorusData

variable {M : IntegralModel ↥𝒪[F] F G} {iS : S.toGrp ⟶ G}
  (B : UnitFixedContainingTorusData M iS)

/-- The actual torus over the original field. -/
abbrev genericTorus : CommGroupScheme (Spec (CommRingCat.of F)) :=
  (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj B.torus

/-- Its inclusion in the original generic group. -/
def genericInclusion : B.genericTorus.toGrp ⟶ G :=
  M.genericTorusMap B.torus B.inclusion

theorem genericIsTorus : IsTorus B.genericTorus.toGrp :=
  (B.relativeTorus.baseChange (Spec.algebraMap ↥𝒪[F] F)).isTorus

theorem genericClosed : IsClosedSubgroup B.genericInclusion :=
  (B.closed.baseChange (Spec.algebraMap ↥𝒪[F] F)).comp_iso M.genericIso

/-- The same integral torus over maximal-unramified coefficients. -/
abbrev unramifiedTorus :
    CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))) :=
  (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).obj B.torus

/-- Its actual inclusion in the coefficient extension of the supplied model. -/
def unramifiedInclusion : B.unramifiedTorus.toGrp ⟶ M.baseChangeUnramified.group :=
  (baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map B.inclusion

theorem unramifiedClosed : IsClosedSubgroup B.unramifiedInclusion :=
  B.closed.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))

theorem unramifiedIsSplit : IsSplitTorus B.unramifiedTorus.toGrp := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  exact (B.relativeTorus.baseChange
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).isSplitTorus_of_henselian
      (k := IsLocalRing.ResidueField (fixedFieldIntegers F)) IsLocalRing.residue_surjective

/-- Read the relative torus as its own integral model of its generic fibre. -/
def integralModel : IntegralModel ↥𝒪[F] F B.genericTorus.toGrp := by
  let : Smooth B.torus.toGrp.X.hom := B.relativeTorus.smooth
  exact {
    group := B.torus.toGrp
    affine := B.closed.isAffineHom
    flat := inferInstance
    finiteType := inferInstance
    genericIso := Iso.refl _ }

/-- The torus inclusion is a model homomorphism for its exact generic map. -/
def modelHom : B.integralModel.Hom M B.genericInclusion where
  hom := B.inclusion
  generic_comm := (Category.id_comp _).symm

/-- The two coefficient towers give the specified generic torus identification. -/
def unramifiedGenericIso :
    (CommGroupScheme.baseChange
      (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F))).obj B.unramifiedTorus ≅
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj B.genericTorus :=
  CommGroupScheme.isoOfGroupIso B.integralModel.baseChangeUnramified.genericIso

theorem unramifiedGeneric_comm :
    M.baseChangeUnramified.genericHom B.unramifiedInclusion =
      CommGroupScheme.groupHom B.unramifiedGenericIso.hom ≫
        (baseChange (algebraBaseMap F (inertiaFixedField F))).map B.genericInclusion :=
  B.integralModel.baseChangeGenericIso_naturality
    (fixedFieldIntegers F) (inertiaFixedField F) M B.modelHom

end UnitFixedContainingTorusData

end Langlands.Geometry.Building
