import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField

/-! # A chosen fraction field and the generic point -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- The local ring at the generic point of an integral scheme is already a field,
so passage to its residue field is an isomorphism. -/
theorem isIso_genericPoint_residue (X : Scheme.{u}) [IsIntegral X] :
    IsIso (X.residue (genericPoint X)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

variable (R : CommRingCat.{u}) [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The unique isomorphism from a chosen fraction field to the function field
of the spectrum, oriented contravariantly on spectra. -/
def fractionFieldSpecIso :
    Spec (CommRingCat.of K) ≅ Spec (Spec R).functionField :=
  Scheme.Spec.mapIso
    ((IsLocalization.algEquiv (nonZeroDivisors R)
      (Spec R).functionField K).toRingEquiv.toCommRingCatIso).op

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem fractionFieldSpecIso_hom_fromSpecStalk :
    (fractionFieldSpecIso R K).hom ≫
        (Spec R).fromSpecStalk
          (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [Spec.fromSpecStalk_eq']
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (IsLocalization.algEquiv (nonZeroDivisors R)
    (Spec R).functionField K).commutes r

/-- A chosen fraction field identifies over the original spectrum with the
residue field of its generic point. -/
def fractionFieldGenericPointIso :
    Spec (CommRingCat.of K) ≅
      Spec ((Spec R).residueField
        (genericPoint (Spec R))) := by
  have := isIso_genericPoint_residue (Spec R)
  exact fractionFieldSpecIso R K ≪≫
    (asIso (Spec.map ((Spec R).residue
      (genericPoint (Spec R))))).symm

@[reassoc]
theorem fractionFieldGenericPointIso_hom_fromSpecResidueField :
    (fractionFieldGenericPointIso R K).hom ≫
        (Spec R).fromSpecResidueField
          (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  have := isIso_genericPoint_residue (Spec R)
  simp only [fractionFieldGenericPointIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Scheme.fromSpecResidueField, Category.assoc, IsIso.inv_hom_id_assoc]
  exact fractionFieldSpecIso_hom_fromSpecStalk R K

end Langlands.AlgebraicGeometry
