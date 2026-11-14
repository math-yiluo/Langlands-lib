import Langlands.GroupScheme.ChevalleyIntegral.MatrixMaps
import Langlands.GroupScheme.IntegralModel.SchematicClosureProof
import Langlands.GroupScheme.SplitExistence.Assembly
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Generic Chevalley closures over Dedekind domains -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.ChevalleyIntegral

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The standard matrix group is an integral model of its generic fibre. -/
def ambientModel : IntegralModel R K (D.GLk K) where
  group := D.GLR (CommRingCat.of R)
  affine := inferInstance
  flat := by
    have := GeneralLinear.smoothStatement (Fin D.n) (CommRingCat.of R)
    infer_instance
  finiteType := by
    have := GeneralLinear.smoothStatement (Fin D.n) (CommRingCat.of R)
    infer_instance
  genericIso := GeneralLinear.baseChangeIso (Fin D.n) (Spec.algebraMap R K)

variable (C : D.ChevGroup K)

local instance genericClosed : IsClosedImmersion C.i.hom.hom.left := C.closed

/-- The schematic closure of the chosen generic Chevalley group. -/
def genericModel : IntegralModel R K C.H :=
  IntegralModel.SchematicClosureConstruction.closureModel (ambientModel D R K) C.i

/-- The compatible closed model morphism into the standard matrix group. -/
def genericModelHom : (genericModel D R K C).Hom (ambientModel D R K) C.i :=
  IntegralModel.SchematicClosureConstruction.closureModelHom (ambientModel D R K) C.i

theorem genericModelHom_isSchematicClosure :
    (genericModelHom D R K C).IsSchematicClosure :=
  IntegralModel.SchematicClosureConstruction.closureModelHom_isSchematicClosure
    (ambientModel D R K) C.i

/-- The integral model is a closed subgroup of the standard matrix group. -/
def modelInclusion : (genericModel D R K C).group ⟶ D.GLR (CommRingCat.of R) :=
  (genericModelHom D R K C).hom

theorem modelInclusion_closed : IsClosedSubgroup (modelInclusion D R K C) :=
  (genericModelHom_isSchematicClosure D R K C).1

/-- Finite type over a Dedekind domain is locally of finite presentation. -/
instance genericModel_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (genericModel D R K C).group.X.hom := by
  infer_instance

/-- The generic identification respects the original inclusion into matrices. -/
theorem modelInclusion_generic :
    (baseChange (Spec.algebraMap R K)).map (modelInclusion D R K C) ≫
        (ambientModel D R K).genericIso.hom =
      (genericModel D R K C).genericIso.hom ≫ C.i :=
  (genericModelHom D R K C).generic_comm

/-- The lifted integers form a domain, by transport from `ℤ`. -/
instance liftedIntegers_domain : IsDomain (ULift.{u} ℤ) :=
  MulEquiv.isDomain ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv

/-- The lifted integers are a principal ideal ring, by transport from `ℤ`. -/
instance liftedIntegers_principal : IsPrincipalIdealRing (ULift.{u} ℤ) :=
  IsPrincipalIdealRing.of_surjective
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.surjective

/-- Choose a generic Chevalley group over the fraction field of the lifted integers. -/
def integerGenericGroup [Finite J] [Module.Finite ℤ X] :
    D.ChevGroup (FractionRing (ULift.{u} ℤ)) :=
  Classical.choice (D.nonempty_chevGroup (FractionRing (ULift.{u} ℤ)))

/-- One actual affine flat finite-type group over the lifted integers, with its
specified generic Chevalley fibre. -/
def integerModel [Finite J] [Module.Finite ℤ X] :
    IntegralModel (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ)) (integerGenericGroup D).H :=
  genericModel D (ULift.{u} ℤ) (FractionRing (ULift.{u} ℤ)) (integerGenericGroup D)

end Langlands.GroupScheme.ChevalleyIntegral
