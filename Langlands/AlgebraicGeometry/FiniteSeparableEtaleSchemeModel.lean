import Langlands.CommutativeAlgebra.FiniteSeparableEtaleModel
import Langlands.AlgebraicGeometry.Picard.GenericFractionField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Actual finite etale scheme models of separable generic extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.FiniteSeparableEtaleModel

variable {R K L : Type u} [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

variable (d : FiniteSeparableEtaleModel R K L)

/-- The actual spectrum of the localized base. -/
abbrev baseScheme : Scheme.{u} := Spec (CommRingCat.of d.Base)

/-- The actual spectrum of the finite free etale domain model. -/
abbrev modelScheme : Scheme.{u} := Spec (CommRingCat.of d.Carrier)

/-- The actual finite etale structural morphism. -/
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

instance : IsIntegral d.modelScheme := inferInstance

instance : IrreducibleSpace d.modelScheme := inferInstance

/-- The nonempty principal open in the original base. -/
def baseOpen : (Spec (CommRingCat.of R)).Opens :=
  PrimeSpectrum.basicOpen d.denominator

/-- The map from the localized base to the original spectrum. -/
def localizationMap : d.baseScheme ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R d.Base))

instance : IsOpenImmersion d.localizationMap := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R d.Base)))
  infer_instance

/-- The standard localization spectrum is the actual principal-open subscheme. -/
def localizationIso : d.baseScheme ≅ d.baseOpen.toScheme :=
  IsOpenImmersion.isoOfRangeEq d.localizationMap d.baseOpen.ι (by
    rw [Scheme.Opens.range_ι]
    exact PrimeSpectrum.localization_away_comap_range d.Base d.denominator)

omit [IsDomain R] [IsFractionRing R K] [IsScalarTower R K L] in
@[reassoc (attr := simp)]
theorem localizationIso_hom_ι :
    d.localizationIso.hom ≫ d.baseOpen.ι = d.localizationMap :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The model is a cover of an actual nonempty open of the original spectrum. -/
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

omit [IsFractionRing R K] [IsScalarTower R K L] in
/-- The principal open is nonempty because the chosen denominator is nonzero. -/
theorem baseOpen_nonempty : (d.baseOpen : Set (Spec (CommRingCat.of R))).Nonempty := by
  exact ⟨d.localizationMap (genericPoint d.baseScheme), by
    rw [← d.localizationIso_hom_ι]
    exact (d.localizationIso.hom (genericPoint d.baseScheme)).property⟩

instance fractionRing : IsFractionRing d.Base K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers d.denominator) d.Base K

/-- The original specified fraction field maps to the localized base spectrum. -/
def genericBaseMap : Spec (CommRingCat.of K) ⟶ d.baseScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap d.Base K))

/-- The actual generic pullback is the spectrum of the specified extension. -/
def genericIso [Algebra.IsAlgebraic K L] :
    pullback d.genericBaseMap d.toBase ≅ Spec (CommRingCat.of L) :=
  pullbackSpecIso d.Base K d.Carrier ≪≫
    Scheme.Spec.mapIso d.genericEquiv.toRingEquiv.symm.toCommRingCatIso.op

omit [IsDomain R] in
@[reassoc (attr := simp)]
theorem genericIso_inv_fst [Algebra.IsAlgebraic K L] :
    d.genericIso.inv ≫ pullback.fst d.genericBaseMap d.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  simp only [genericIso, genericBaseMap, toBase, Iso.trans_inv,
    Functor.mapIso_inv, Category.assoc,
    pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom d.genericEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[d.Base] d.Carrier))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact d.genericEquiv.toAlgHom.comp_algebraMap

/-- The specified fraction field is the actual generic residue field of the
localized base, as a scheme over that base. -/
def genericResidueFieldIso :
    Spec (CommRingCat.of K) ≅
      Spec (d.baseScheme.residueField (genericPoint d.baseScheme)) :=
  Langlands.AlgebraicGeometry.fractionFieldGenericPointIso (CommRingCat.of d.Base) K

omit [IsScalarTower R K L] in
@[reassoc (attr := simp)]
theorem genericResidueFieldIso_hom_fromSpecResidueField :
    d.genericResidueFieldIso.hom ≫
      d.baseScheme.fromSpecResidueField (genericPoint d.baseScheme) = d.genericBaseMap :=
  Langlands.AlgebraicGeometry.fractionFieldGenericPointIso_hom_fromSpecResidueField
    (CommRingCat.of d.Base) K

/-- Base change along the specified fraction field identifies with the actual
residue-field fibre, including its two projections. -/
def genericPullbackToFiberIso :
    pullback d.genericBaseMap d.toBase ≅ d.toBase.fiber (genericPoint d.baseScheme) :=
  (asIso (pullback.map _ _ _ _ d.genericResidueFieldIso.hom (𝟙 _) (𝟙 _)
    (by simp) (by simp))) ≪≫
    pullbackSymmetry _ _

/-- The actual scheme-theoretic generic fibre is the specified extension
spectrum. -/
def genericFiberIso [Algebra.IsAlgebraic K L] :
    d.toBase.fiber (genericPoint d.baseScheme) ≅ Spec (CommRingCat.of L) :=
  d.genericPullbackToFiberIso.symm ≪≫ d.genericIso

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem genericFiberIso_inv_toSpecResidueField [Algebra.IsAlgebraic K L] :
    d.genericFiberIso.inv ≫ d.toBase.fiberToSpecResidueField (genericPoint d.baseScheme) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ d.genericResidueFieldIso.hom := by
  simp only [genericFiberIso, genericPullbackToFiberIso,
    Scheme.Hom.fiberToSpecResidueField, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    asIso_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst,
    genericIso_inv_fst_assoc]

end Langlands.CommutativeAlgebra.FiniteSeparableEtaleModel
