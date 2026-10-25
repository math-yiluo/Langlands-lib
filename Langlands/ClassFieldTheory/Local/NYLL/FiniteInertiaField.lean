import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.LocalField.RelativeIntegers
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Abelian

/-! # The finite inertia fixed field and its actual comparison maps -/

noncomputable section

namespace Langlands.LocalClassField.NYLL

universe u v

open IsLocalRing

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (TF : F.TopologicalData)

local instance : FiniteDimensional F.Carrier E.Carrier :=
  FiniteDimensional.right (Padic p) F.Carrier E.Carrier

/-- The actual finite residue-action kernel for the norm constructed from the
supplied base realization. -/
def finiteInertiaSubgroup : Subgroup Gal(E.Carrier/F.Carrier) := by
  letI := TF.topology
  letI := TF.valuativeRel
  letI := TF.localField
  letI := LocalGalois.localNormedField F.Carrier
  letI := LocalGalois.localNormedField_ultrametric F.Carrier
  letI := LocalGalois.localNormedField_complete F.Carrier
  exact LocalGalois.inertia F.Carrier E.Carrier

/-- The actual fixed intermediate field of the finite inertia subgroup. -/
def finiteInertiaField : IntermediateField F.Carrier E.Carrier :=
  IntermediateField.fixedField (finiteInertiaSubgroup F E TF)

/-- Literal inclusion of the inertia fixed field into the original extension. -/
def finiteInertiaEmbedding : finiteInertiaField F E TF →ₐ[F.Carrier] E.Carrier :=
  (finiteInertiaField F E TF).val

@[simp] theorem finiteInertiaEmbedding_apply (x : finiteInertiaField F E TF) :
    finiteInertiaEmbedding F E TF x = (x : E.Carrier) := rfl

/-- The same subtype field, with its inherited finite extension structure over `Padic p`. -/
abbrev finiteInertiaPadicField : PadicField.{v} p := by
  letI : FiniteDimensional (Padic p) (finiteInertiaField F E TF) :=
    FiniteDimensional.trans (Padic p) F.Carrier (finiteInertiaField F E TF)
  exact { Carrier := finiteInertiaField F E TF }

/-- Base embedding with the specified `Padic p` scalars. -/
def finiteInertiaBaseEmbedding :
    F.Carrier →ₐ[Padic p] (finiteInertiaPadicField F E TF).Carrier :=
  IsScalarTower.toAlgHom (Padic p) F.Carrier (finiteInertiaField F E TF)

/-- Inclusion of the same intermediate field, viewed over `Padic p`. -/
def finiteInertiaPadicEmbedding :
    (finiteInertiaPadicField F E TF).Carrier →ₐ[Padic p] E.Carrier :=
  (finiteInertiaEmbedding F E TF).restrictScalars (Padic p)

@[simp] theorem finiteInertiaPadicEmbedding_base (x : F.Carrier) :
    finiteInertiaPadicEmbedding F E TF (finiteInertiaBaseEmbedding F E TF x) =
      algebraMap F.Carrier E.Carrier x := rfl

/-- The inherited scalar tower from the p-adic base through the fixed field. -/
theorem finiteInertiaPadicTower :
    IsScalarTower (Padic p) (finiteInertiaPadicField F E TF).Carrier E.Carrier :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The original base acts on the same intermediate subtype. -/
theorem finiteInertiaBaseTower :
    IsScalarTower (Padic p) F.Carrier (finiteInertiaPadicField F E TF).Carrier :=
  inferInstance

/-- The field maps form the actual intermediate-field tower. -/
theorem finiteInertiaFieldTower :
    IsScalarTower F.Carrier (finiteInertiaPadicField F E TF).Carrier E.Carrier :=
  inferInstance

/-- Finiteness over the original base is inherited from the ambient extension. -/
theorem finiteInertiaField_finiteDimensional :
    FiniteDimensional F.Carrier (finiteInertiaPadicField F E TF).Carrier :=
  inferInstance

attribute [local instance] finiteInertiaPadicTower

section Supplied

variable (TU : (finiteInertiaPadicField F E TF).TopologicalData) (TE : E.TopologicalData)

/-- Integer inclusion for arbitrary supplied realizations of the two fields. -/
abbrev finiteInertiaIntegerMap : TU.Integers →+* TE.Integers :=
  PadicField.TopologicalData.relativeIntegerMap TU TE

/-- Residue inclusion induced by the supplied-data integer map. -/
abbrev finiteInertiaResidueMap : TU.ResidueField →+* TE.ResidueField :=
  PadicField.TopologicalData.relativeResidueMap TU TE

/-- Integer map from the original base into the inertia fixed field. -/
abbrev finiteInertiaBaseIntegerMap : TF.Integers →+* TU.Integers :=
  PadicField.TopologicalData.relativeIntegerMap TF TU

/-- Residue map from the original base into the inertia fixed field. -/
abbrev finiteInertiaBaseResidueMap : TF.ResidueField →+* TU.ResidueField :=
  PadicField.TopologicalData.relativeResidueMap TF TU

/-- The already constructed actual integer-ring action on the fixed field. -/
abbrev finiteInertiaIntegerAction :
    Gal(finiteInertiaField F E TF/F.Carrier) →* RingAut TU.Integers :=
  Ramification.Padic.integerAutHom TU F.Carrier

/-- The already constructed actual action on its supplied residue field. -/
abbrev finiteInertiaResidueAction :
    Gal(finiteInertiaField F E TF/F.Carrier) →* RingAut TU.ResidueField :=
  Ramification.Padic.residueHom TU F.Carrier

/-- These supplied-data maps factor the original integer map. -/
theorem finiteInertiaIntegerMap_comp :
    (finiteInertiaIntegerMap F E TF TU TE).comp (finiteInertiaBaseIntegerMap F E TF TU) =
      PadicField.TopologicalData.relativeIntegerMap TF TE :=
  (PadicField.TopologicalData.relativeIntegerMap_comp TF TU TE).symm

/-- These supplied-data maps factor the original residue map. -/
theorem finiteInertiaResidueMap_comp :
    (finiteInertiaResidueMap F E TF TU TE).comp (finiteInertiaBaseResidueMap F E TF TU) =
      PadicField.TopologicalData.relativeResidueMap TF TE :=
  (PadicField.TopologicalData.relativeResidueMap_comp TF TU TE).symm

end Supplied

section Galois

variable [IsGalois F.Carrier E.Carrier]

/-- Normality of the residue kernel gives Galoisness of its actual fixed field. -/
theorem finiteInertiaField_isGalois : IsGalois F.Carrier (finiteInertiaField F E TF) := by
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  exact IsGalois.of_fixedField_normal_subgroup (LocalGalois.inertia F.Carrier E.Carrier)

attribute [local instance] finiteInertiaField_isGalois

/-- Restriction of actual field automorphisms to the inertia fixed field. -/
def finiteInertiaRestriction :
    Gal(E.Carrier/F.Carrier) →* Gal(finiteInertiaField F E TF/F.Carrier) :=
  AlgEquiv.restrictNormalHom (finiteInertiaField F E TF)

@[simp] theorem finiteInertiaRestriction_apply (σ : Gal(E.Carrier/F.Carrier))
    (x : finiteInertiaField F E TF) :
    finiteInertiaEmbedding F E TF (finiteInertiaRestriction F E TF σ x) =
      σ (finiteInertiaEmbedding F E TF x) :=
  AlgEquiv.restrictNormal_commutes σ (finiteInertiaField F E TF) x

end Galois

/-- In the abelian case the fixed field is abelian over the original base. -/
theorem finiteInertiaField_isAbelianGalois [IsAbelianGalois F.Carrier E.Carrier] :
    IsAbelianGalois F.Carrier (finiteInertiaPadicField F E TF).Carrier :=
  inferInstance

end Langlands.LocalClassField.NYLL
