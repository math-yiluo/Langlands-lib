import Langlands.CommutativeAlgebra.FiniteSeparableNilradicalEtaleModel
import Langlands.AlgebraicGeometry.FiniteSeparableNilradicalGenericPoint
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual finite etale covers over nonreduced irreducible affine bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.FiniteSeparableNilradicalEtaleModel

variable {R K L : Type u} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
  [Field K] [Field L]

local instance nilradicalIsPrime : (nilradical R).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance

variable [Algebra (R ⧸ nilradical R) K] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra (R ⧸ nilradical R) L] [Algebra K L]
  [IsScalarTower (R ⧸ nilradical R) K L]
  [Algebra R K] [IsScalarTower R (R ⧸ nilradical R) K]
  [Algebra.IsAlgebraic K L]

variable (d : FiniteSeparableNilradicalEtaleModel R K L)

/-- The specified extension is an algebra over the actual localized model. -/
instance extensionAlgebra : Algebra d.Carrier L :=
  (d.genericEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := d.Base) (A := K)).toRingHom).toAlgebra

instance carrierNontrivial : Nontrivial d.Carrier :=
  (algebraMap d.Carrier L).domain_nontrivial

/-- The spectrum of the actual localized base ring. -/
abbrev baseScheme : Scheme.{u} := Spec (CommRingCat.of d.Base)

/-- The spectrum of the actual localized monic model. -/
abbrev modelScheme : Scheme.{u} := Spec (CommRingCat.of d.Carrier)

/-- The spectrum of the original monic model before base shrinking. -/
abbrev liftedModelScheme : Scheme.{u} :=
  Spec (CommRingCat.of d.toFiniteSeparableNilradicalModel.Carrier)

instance liftedIrreducible : IrreducibleSpace d.liftedModelScheme :=
  FiniteSeparableNilradicalModel.irreducibleSpectrum d.toFiniteSeparableNilradicalModel

/-- The localization structure on the actual right tensor factor. -/
instance liftedAlgebra : Algebra d.toFiniteSeparableNilradicalModel.Carrier d.Carrier :=
  Algebra.TensorProduct.rightAlgebra

instance liftedLocalization :
    IsLocalization.Away
      (algebraMap R d.toFiniteSeparableNilradicalModel.Carrier d.denominator) d.Carrier :=
  IsLocalization.Away.tensorRight (S := d.toFiniteSeparableNilradicalModel.Carrier)
    d.denominator d.Base

/-- The actual principal-open embedding into the original monic model. -/
def toLiftedModel : d.modelScheme ⟶ d.liftedModelScheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap d.toFiniteSeparableNilradicalModel.Carrier d.Carrier))

instance : IsOpenImmersion d.toLiftedModel := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap d.toFiniteSeparableNilradicalModel.Carrier d.Carrier)))
  exact IsOpenImmersion.of_isLocalization
    (algebraMap R d.toFiniteSeparableNilradicalModel.Carrier d.denominator)

instance modelIrreducible : IrreducibleSpace d.modelScheme :=
  d.toLiftedModel.isOpenEmbedding.irreducibleSpace

/-- The actual finite etale structural map. -/
def toBase : d.modelScheme ⟶ d.baseScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap d.Base d.Carrier))

instance : IsFinite d.toBase := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

instance : Etale d.toBase := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

instance : Surjective d.toBase := by
  exact ⟨Algebra.IsIntegral.comap_surjective d.Base d.Carrier⟩

/-- The chosen nonempty principal open in the original base. -/
def baseOpen : (Spec (CommRingCat.of R)).Opens :=
  PrimeSpectrum.basicOpen d.denominator

/-- The base-localization map to the original affine scheme. -/
def localizationMap : d.baseScheme ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R d.Base))

instance : IsOpenImmersion d.localizationMap := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R d.Base)))
  infer_instance

/-- The actual localization spectrum is the chosen open subscheme. -/
def localizationIso : d.baseScheme ≅ d.baseOpen.toScheme :=
  IsOpenImmersion.isoOfRangeEq d.localizationMap d.baseOpen.ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range d.Base d.denominator)

omit [IrreducibleSpace (PrimeSpectrum R)] [IsScalarTower (R ⧸ nilradical R) K L]
  [Algebra.IsAlgebraic K L] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra R K] [IsScalarTower R (R ⧸ nilradical R) K] in
@[reassoc (attr := simp)]
theorem localizationIso_hom_ι :
    d.localizationIso.hom ≫ d.baseOpen.ι = d.localizationMap :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The model covers an actual open of the original base. -/
def coverMap : d.modelScheme ⟶ d.baseOpen.toScheme :=
  d.toBase ≫ d.localizationIso.hom

instance : IsFinite d.coverMap := by
  change IsFinite (d.toBase ≫ d.localizationIso.hom)
  infer_instance
instance : Etale d.coverMap := by
  change Etale (d.toBase ≫ d.localizationIso.hom)
  infer_instance
instance : Surjective d.coverMap := by
  change Surjective (d.toBase ≫ d.localizationIso.hom)
  infer_instance
instance : IsAffine d.modelScheme := inferInstance

omit [IsFractionRing (R ⧸ nilradical R) K] [IsScalarTower (R ⧸ nilradical R) K L]
  [Algebra R K] [IsScalarTower R (R ⧸ nilradical R) K] [Algebra.IsAlgebraic K L] in
/-- The denominator avoids the base generic prime, so the open is nonempty. -/
theorem baseOpen_nonempty : (d.baseOpen : Set (Spec (CommRingCat.of R))).Nonempty :=
  ⟨⟨nilradical R, inferInstance⟩, d.denominator_notMem⟩

omit [IrreducibleSpace (PrimeSpectrum R)] in
/-- The generic point of the localization maps to the previously specified
actual generic prime of the lifted model. -/
theorem toLiftedModel_genericPoint :
    d.toLiftedModel (genericPoint d.modelScheme) =
      FiniteSeparableNilradicalModel.genericPrime d.toFiniteSeparableNilradicalModel := by
  exact (genericPoint_eq_of_isOpenImmersion d.toLiftedModel).trans
    ((genericPoint_spec d.liftedModelScheme).eq
      (FiniteSeparableNilradicalModel.isGenericPoint_genericPrime
        d.toFiniteSeparableNilradicalModel))

/-- Principal localization preserves the specified actual generic residue field. -/
def modelGenericResidueFieldIso :
    Spec (CommRingCat.of L) ≅
      Spec (d.modelScheme.residueField (genericPoint d.modelScheme)) :=
  FiniteSeparableNilradicalModel.modelGenericResidueFieldIso
      d.toFiniteSeparableNilradicalModel ≪≫
    Scheme.Spec.mapIso
      (d.liftedModelScheme.residueFieldCongr d.toLiftedModel_genericPoint).op ≪≫
    (asIso (Spec.map (d.toLiftedModel.residueFieldMap (genericPoint d.modelScheme)))).symm

omit [IrreducibleSpace (PrimeSpectrum R)] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem modelGenericResidueFieldIso_hom_toLiftedModel :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) ≫ d.toLiftedModel =
      (FiniteSeparableNilradicalModel.modelGenericResidueFieldIso
        d.toFiniteSeparableNilradicalModel).hom ≫
        d.liftedModelScheme.fromSpecResidueField
          (FiniteSeparableNilradicalModel.genericPrime d.toFiniteSeparableNilradicalModel) := by
  rw [← d.toLiftedModel.SpecMap_residueFieldMap_fromSpecResidueField]
  simp only [modelGenericResidueFieldIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, Functor.mapIso_hom, Iso.op_hom, Category.assoc, IsIso.inv_hom_id_assoc]
  exact congrArg (fun m =>
    (FiniteSeparableNilradicalModel.modelGenericResidueFieldIso
      d.toFiniteSeparableNilradicalModel).hom ≫ m)
    (d.liftedModelScheme.residueFieldCongr_fromSpecResidueField d.toLiftedModel_genericPoint)

omit [IrreducibleSpace (PrimeSpectrum R)] [IsFractionRing (R ⧸ nilradical R) K]
  [IsScalarTower (R ⧸ nilradical R) K L] [Algebra R K]
  [IsScalarTower R (R ⧸ nilradical R) K] [Algebra.IsAlgebraic K L] in
set_option backward.isDefEq.respectTransparency false in
/-- Both coefficient factorizations give the actual map to the original base. -/
@[reassoc]
theorem coverMap_ι :
    d.coverMap ≫ d.baseOpen.ι =
      d.toLiftedModel ≫
        FiniteSeparableNilradicalModel.toOriginalBase d.toFiniteSeparableNilradicalModel := by
  rw [coverMap, Category.assoc, localizationIso_hom_ι]
  simp only [toBase, localizationMap, toLiftedModel,
    FiniteSeparableNilradicalModel.toOriginalBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change algebraMap d.Base d.Carrier (algebraMap R d.Base r) =
    algebraMap d.toFiniteSeparableNilradicalModel.Carrier d.Carrier
      (algebraMap R d.toFiniteSeparableNilradicalModel.Carrier r)
  rw [← IsScalarTower.algebraMap_apply R d.Base d.Carrier,
    ← IsScalarTower.algebraMap_apply R d.toFiniteSeparableNilradicalModel.Carrier d.Carrier]

omit [IrreducibleSpace (PrimeSpectrum R)] in
set_option backward.isDefEq.respectTransparency false in
/-- The generic residue-field comparison preserves the originally specified
extension and its map to the original nonreduced affine base. -/
@[reassoc]
theorem modelGenericResidueFieldIso_hom_coverMap_ι :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) ≫
        d.coverMap ≫ d.baseOpen.ι =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        FiniteSeparableNilradicalModel.originalGenericBaseMap (R := R) (K := K) := by
  rw [coverMap_ι, modelGenericResidueFieldIso_hom_toLiftedModel_assoc]
  exact FiniteSeparableNilradicalModel.modelGenericResidueFieldIso_hom_toOriginalBase
    d.toFiniteSeparableNilradicalModel

end Langlands.CommutativeAlgebra.FiniteSeparableNilradicalEtaleModel
