import Langlands.GroupScheme.Descent.FiniteUnramifiedSpectralModel
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.Normal.Basic

/-! # Compatible finite and maximal-unramified coefficient automorphisms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance liftNormedField : NontriviallyNormedField F := localNormedField F
local instance liftUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance liftComplete : CompleteSpace F := localNormedField_complete F

/-- Restrict a field automorphism of the inertia fixed field to its actual
integer ring. -/
def fixedFieldIntegerAut (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    fixedFieldIntegers F ≃+* fixedFieldIntegers F :=
  (fixedFieldIntegersEquiv F).trans
    ((integerAut F (inertiaFixedField F) σ).toRingEquiv.trans (fixedFieldIntegersEquiv F).symm)

@[simp] theorem fixedFieldIntegerAut_coe
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (x : fixedFieldIntegers F) :
    (fixedFieldIntegerAut F σ x : inertiaFixedField F) = σ (x : inertiaFixedField F) := rfl

/-- The corresponding actual automorphism of the maximal-unramified integer spectrum. -/
abbrev fixedIntegerBaseAut (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :=
  Spec.map (CommRingCat.ofHom (fixedFieldIntegerAut F σ).toRingHom)

instance fixedIntegerBaseAut_isIso (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    IsIso (fixedIntegerBaseAut F σ) :=
  isIso_SpecMap_iff.mpr (fixedFieldIntegerAut F σ).bijective

/-- The field and actual integer automorphisms commute with generic inclusion. -/
theorem fixedIntegerBaseAut_generic
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    galoisBaseMap F (inertiaFixedField F) σ ≫
        Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) =
      Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) ≫ fixedIntegerBaseAut F σ := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact (fixedFieldIntegerAut_coe F σ x).symm

variable (E : IntermediateField F (SeparableClosure F)) (hE : E ≤ inertiaFixedField F)

/-- A finite-stage field automorphism extended to the actual inertia fixed field. -/
def liftAutomorphism (σ : E ≃ₐ[F] E) :
    inertiaFixedField F ≃ₐ[F] inertiaFixedField F := by
  letI : Algebra E (inertiaFixedField F) := (IntermediateField.inclusion hE).toAlgebra
  letI : IsScalarTower F E (inertiaFixedField F) := IsScalarTower.of_algebraMap_eq' rfl
  exact σ.liftNormal (inertiaFixedField F)

/-- The chosen lift restricts along the specified actual field inclusion. -/
theorem liftAutomorphism_commutes (σ : E ≃ₐ[F] E) (x : E) :
    liftAutomorphism F E hE σ (IntermediateField.inclusion hE x) =
      IntermediateField.inclusion hE (σ x) := by
  let : Algebra E (inertiaFixedField F) := (IntermediateField.inclusion hE).toAlgebra
  let : IsScalarTower F E (inertiaFixedField F) := IsScalarTower.of_algebraMap_eq' rfl
  exact σ.liftNormal_commutes (inertiaFixedField F) x

/-- The actual finite-to-inertia field spectrum map. -/
abbrev inertiaFieldMap :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hE).toRingHom)

/-- The finite and lifted field automorphisms commute with the actual inclusion. -/
theorem liftAutomorphism_fieldSquare (σ : E ≃ₐ[F] E) :
    galoisBaseMap F (inertiaFixedField F) (liftAutomorphism F E hE σ) ≫ inertiaFieldMap F E hE =
      inertiaFieldMap F E hE ≫ galoisBaseMap F E σ := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact liftAutomorphism_commutes F E hE σ x

/-- The spectral integer inclusion is the same specified field inclusion. -/
theorem spectralIntegerInclusion_inertia (x : extensionIntegers F E) :
    (spectralIntegerInclusion F E hE x : inertiaFixedField F) =
      IntermediateField.inclusion hE (x : E) :=
  Subtype.ext (spectralIntegerInclusion_coe F E hE x)

/-- The lifted integer automorphism commutes with the actual integer inclusion. -/
theorem liftAutomorphism_integerCommutes (σ : E ≃ₐ[F] E) :
    (fixedFieldIntegerAut F (liftAutomorphism F E hE σ)).toRingHom.comp
        (spectralIntegerInclusion F E hE) =
      (spectralIntegerInclusion F E hE).comp (integerAut F E σ).toRingHom := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change liftAutomorphism F E hE σ (spectralIntegerInclusion F E hE x : inertiaFixedField F) =
    (spectralIntegerInclusion F E hE (integerAut F E σ x) : inertiaFixedField F)
  rw [spectralIntegerInclusion_inertia, spectralIntegerInclusion_inertia,
    liftAutomorphism_commutes]
  rfl

/-- The finite integer and lifted integer spectrum maps form an actual commuting square. -/
theorem liftAutomorphism_integerSquare (σ : E ≃ₐ[F] E) :
    fixedIntegerBaseAut F (liftAutomorphism F E hE σ) ≫ spectralIntegerMap F E hE =
      spectralIntegerMap F E hE ≫ Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (liftAutomorphism_integerCommutes F E hE σ)

/-- Finite integer and field automorphisms commute with the actual generic inclusion. -/
theorem finiteIntegerBaseAut_generic (σ : E ≃ₐ[F] E) :
    galoisBaseMap F E σ ≫ Spec.algebraMap (extensionIntegers F E) E =
      Spec.algebraMap (extensionIntegers F E) E ≫
        Spec.map (CommRingCat.ofHom (integerAut F E σ).toRingHom) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1

/-- The actual spectral inclusion from a finite stage to maximal-unramified
integers is fpqc. No finiteness or Galois hypothesis is needed here. -/
theorem spectralIntegerMap_fpqc :
    Surjective (spectralIntegerMap F E hE) ∧ Flat (spectralIntegerMap F E hE) ∧
      QuasiCompact (spectralIntegerMap F E hE) := by
  let : Algebra E (inertiaFixedField F) := (IntermediateField.inclusion hE).toAlgebra
  let : IsScalarTower F E (inertiaFixedField F) := IsScalarTower.of_algebraMap_eq' rfl
  let : (spectralValuation F E).HasExtension (fixedFieldValuation F) :=
    { val_isEquiv_comap := by
        intro x y
        change spectralValuation F E x ≤ spectralValuation F E y ↔
          fixedFieldValuation F (algebraMap E (inertiaFixedField F) x) ≤
            fixedFieldValuation F (algebraMap E (inertiaFixedField F) y)
        rw [fixedFieldValuation_eq_spectralValuation]
        change spectralNorm F E x ≤ spectralNorm F E y ↔
          spectralNorm F (inertiaFixedField F) (algebraMap E (inertiaFixedField F) x) ≤
            spectralNorm F (inertiaFixedField F) (algebraMap E (inertiaFixedField F) y)
        rw [← spectralNorm.eq_of_tower x, ← spectralNorm.eq_of_tower y] }
  have hm : Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F) =
      spectralIntegerMap F E hE := by
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro x
    apply Subtype.ext
    exact (spectralIntegerInclusion_inertia F E hE x).symm
  rw [← hm]
  exact valuationInteger_fpqc (spectralValuation F E) (fixedFieldValuation F)

end Langlands.GroupScheme.Descent.FiniteUnramified
