import Langlands.AlgebraicGeometry.FiniteSeparableEtaleSchemeModel

/-! # The specified fraction field at the model's generic point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors TensorProduct

namespace Langlands.CommutativeAlgebra.FiniteSeparableEtaleModel

variable {R K L : Type u} [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

variable (d : FiniteSeparableEtaleModel R K L) [Algebra.IsAlgebraic K L]

/-- Map the actual model into the specified extension using the proved generic
comparison, without replacing the original `K`-algebra structure. -/
instance extensionAlgebra : Algebra d.Carrier L :=
  (d.genericEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := d.Base) (A := K)).toRingHom).toAlgebra

omit [IsDomain R] in
@[simp]
theorem algebraMap_extension_tmul (s : d.Base)
    (a : d.toFiniteSeparablePolynomialModel.Carrier) :
    algebraMap d.Carrier L (s ⊗ₜ[R] a) =
      algebraMap K L (algebraMap d.Base K s) * (a : L) := by
  change d.genericEquiv (1 ⊗ₜ[d.Base] (s ⊗ₜ[R] a)) = _
  simp

omit [IsDomain R] in
/-- The map into the extension agrees with its originally specified field map
on the localized base. -/
theorem algebraMap_extension_comp_base :
    (algebraMap d.Carrier L).comp (algebraMap d.Base d.Carrier) =
      (algebraMap K L).comp (algebraMap d.Base K) := by
  ext s
  change algebraMap d.Carrier L (s ⊗ₜ[R] 1) = _
  simp

/-- The specified extension is a localization of the actual model at the
nonzero elements of the localized original base. -/
instance extensionLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid d.Carrier d.Base⁰) L := by
  let : Algebra d.Carrier (K ⊗[d.Base] d.Carrier) :=
    Algebra.TensorProduct.rightAlgebra
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (R := d.Carrier) (S := K ⊗[d.Base] d.Carrier) (P := L)
    (Algebra.algebraMapSubmonoid d.Carrier d.Base⁰) d.genericEquiv.toRingEquiv).mp
      inferInstance

/-- The specified extension is the fraction field of the actual model ring. -/
instance extensionFractionRing : IsFractionRing d.Carrier L := by
  let M := Algebra.algebraMapSubmonoid d.Carrier d.Base⁰
  have hM : M ≤ d.Carrier⁰ :=
    map_le_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective d.Base d.Carrier) le_rfl
  have hinj := IsLocalization.injective L hM
  exact IsLocalization.of_le M d.Carrier⁰ hM (by
    intro a ha
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
      (hinj (h.trans (map_zero (algebraMap d.Carrier L)).symm)))

/-- The spectrum map of the constructed inclusion into the specified field. -/
def modelGenericMap : Spec (CommRingCat.of L) ⟶ d.modelScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap d.Carrier L))

omit [IsDomain R] in
@[reassoc]
theorem modelGenericMap_toBase :
    d.modelGenericMap ≫ d.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ d.genericBaseMap := by
  simp only [modelGenericMap, toBase, genericBaseMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact d.algebraMap_extension_comp_base

omit [Algebra.IsAlgebraic K L] in
/-- The model's generic point lies over the generic point of the base. -/
theorem toBase_genericPoint :
    d.toBase (genericPoint d.modelScheme) = genericPoint d.baseScheme := by
  change PrimeSpectrum.comap (algebraMap d.Base d.Carrier)
    (genericPoint (Spec (CommRingCat.of d.Carrier))) =
      genericPoint (Spec (CommRingCat.of d.Base))
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  ext r
  exact map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective d.Base d.Carrier)

/-- The actual generic residue field of the model is the specified extension. -/
def modelGenericResidueFieldIso :
    Spec (CommRingCat.of L) ≅
      Spec (d.modelScheme.residueField (genericPoint d.modelScheme)) :=
  Langlands.AlgebraicGeometry.fractionFieldGenericPointIso
    (CommRingCat.of d.Carrier) L

@[reassoc]
theorem modelGenericResidueFieldIso_hom_fromSpecResidueField :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) =
        d.modelGenericMap :=
  Langlands.AlgebraicGeometry.fractionFieldGenericPointIso_hom_fromSpecResidueField
    (CommRingCat.of d.Carrier) L

@[reassoc]
theorem modelGenericResidueFieldIso_hom_toBase :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) ≫ d.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ d.genericBaseMap := by
  rw [← Category.assoc, d.modelGenericResidueFieldIso_hom_fromSpecResidueField,
    d.modelGenericMap_toBase]

/-- The actual map on generic residue-field spectra, with the base point
identified by `toBase_genericPoint`. -/
def genericResidueMap :
    Spec (d.modelScheme.residueField (genericPoint d.modelScheme)) ⟶
      Spec (d.baseScheme.residueField (genericPoint d.baseScheme)) :=
  Spec.map (d.toBase.residueFieldMap (genericPoint d.modelScheme)) ≫
    Spec.map (d.baseScheme.residueFieldCongr d.toBase_genericPoint).inv

omit [Algebra.IsAlgebraic K L] in
@[reassoc]
theorem genericResidueMap_fromSpecResidueField :
    d.genericResidueMap ≫
      d.baseScheme.fromSpecResidueField (genericPoint d.baseScheme) =
      d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) ≫ d.toBase := by
  dsimp only [genericResidueMap]
  rw [Category.assoc]
  rw [show Spec.map (d.baseScheme.residueFieldCongr d.toBase_genericPoint).inv ≫
      d.baseScheme.fromSpecResidueField (genericPoint d.baseScheme) =
      d.baseScheme.fromSpecResidueField (d.toBase (genericPoint d.modelScheme)) from
    d.baseScheme.residueFieldCongr_fromSpecResidueField d.toBase_genericPoint.symm]
  exact d.toBase.SpecMap_residueFieldMap_fromSpecResidueField _

/-- Under the two actual generic residue-field identifications, the actual
map induced by the cover is the originally specified field extension. -/
@[reassoc]
theorem modelGenericResidueFieldIso_hom_genericResidueMap :
    d.modelGenericResidueFieldIso.hom ≫ d.genericResidueMap =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ d.genericResidueFieldIso.hom := by
  apply (cancel_mono (d.baseScheme.fromSpecResidueField (genericPoint d.baseScheme))).mp
  rw [Category.assoc, d.genericResidueMap_fromSpecResidueField,
    d.modelGenericResidueFieldIso_hom_toBase, Category.assoc,
    d.genericResidueFieldIso_hom_fromSpecResidueField]

end Langlands.CommutativeAlgebra.FiniteSeparableEtaleModel
