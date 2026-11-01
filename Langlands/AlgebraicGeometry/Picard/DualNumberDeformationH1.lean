import Langlands.AlgebraicGeometry.Picard.DualNumberCocycleBundles
import Langlands.AlgebraicGeometry.Modules.CechResolution.CohomologyIso

/-! # Actual ordinary first-order line-bundle classes and derived H1 -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.CechResolution

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Actual line-bundle isomorphism classes whose actual zero-section pullback is trivial. -/
def DeformationClasses : Subgroup (LineBundle.IsoClasses preservation (thickening f)) :=
  (LineBundle.pullbackHom preservation (closedPoint f)).ker

variable (𝒰 : X.OrderedAffineCover)

/-- The actual deformation class of an additive cocycle on the fixed cover. -/
def cocycleDeformationClass
    (z : allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    DeformationClasses preservation f :=
  ⟨LineBundle.isoClass preservation
    (cocycleBundle f 𝒰.U 𝒰.iSup_eq_top z.1 z.2),
    LineBundle.isoClass_eq_of_iso
      (ObjectProperty.isoMk _ (cocycleBundleReductionIso f 𝒰.U 𝒰.iSup_eq_top z.1 z.2))⟩

/-- Tensor product makes the cocycle construction additive. -/
def cocycleDeformationHom :
    allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰 →+
      Additive (DeformationClasses preservation f) :=
  AddMonoidHom.mk' (fun z ↦ Additive.ofMul (cocycleDeformationClass preservation f 𝒰 z))
    (fun z w ↦ by
      apply congrArg Additive.ofMul
      apply Subtype.ext
      exact isoClass_cocycleBundle_add f 𝒰.U preservation 𝒰.iSup_eq_top
        z.1 w.1 z.2 w.2 (z + w).2)

/-- Equality of the actual deformation classes is exactly an additive coboundary difference. -/
lemma cocycleDeformationHom_eq_iff
    (z w : allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    cocycleDeformationHom preservation f 𝒰 z = cocycleDeformationHom preservation f 𝒰 w ↔
      CechDegreeOne.IsCoboundary (G := structureSheaf X) 𝒰.U
        (fun a b ↦ w.1 a b - z.1 a b) := by
  change cocycleDeformationClass preservation f 𝒰 z =
      cocycleDeformationClass preservation f 𝒰 w ↔ _
  rw [Subtype.ext_iff]
  exact isoClass_cocycleBundle_eq_iff f 𝒰.U preservation 𝒰.iSup_eq_top z.1 w.1 z.2 w.2

variable [IsSeparated f]

local instance structureSheaf_isQuasicoherent :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (structureSheaf X) :=
  CechDegreeOne.isQuasicoherent_unit X

/-- The actual H1 quotient kernel is killed by the cocycle-to-bundle homomorphism. -/
lemma h1Map_ker_le_cocycleDeformationHom_ker :
    (allPairsH1Map f 𝒰 (structureSheaf X)).toAddMonoidHom.ker ≤
      (cocycleDeformationHom preservation f 𝒰).ker := by
  intro z hz
  have hb := (allPairsH1Map_eq_zero_iff f 𝒰 (structureSheaf X) z).mp hz
  have he : cocycleDeformationHom preservation f 𝒰 0 =
      cocycleDeformationHom preservation f 𝒰 z :=
    (cocycleDeformationHom_eq_iff preservation f 𝒰 0 z).mpr (by simpa using hb)
  simpa using he.symm

/-- Actual derived H1 maps to actual zero-section-trivial line-bundle classes. -/
def h1DeformationHom :
    (DerivedSections.relativeCohomology f 1).obj (structureSheaf X) →+
      Additive (DeformationClasses preservation f) :=
  (allPairsH1Map f 𝒰 (structureSheaf X)).toAddMonoidHom.liftOfSurjective
    (allPairsH1Map_surjective f 𝒰 (structureSheaf X))
    ⟨cocycleDeformationHom preservation f 𝒰,
      h1Map_ker_le_cocycleDeformationHom_ker preservation f 𝒰⟩

/-- The descended map retains the actual coefficient-cocycle formula. -/
lemma h1DeformationHom_allPairsH1Map
    (z : allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    h1DeformationHom preservation f 𝒰 (allPairsH1Map f 𝒰 (structureSheaf X) z) =
      cocycleDeformationHom preservation f 𝒰 z :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Exact coboundary classification makes the descended actual map injective. -/
lemma h1DeformationHom_injective :
    Function.Injective (h1DeformationHom preservation f 𝒰) := by
  intro a b hab
  obtain ⟨z, rfl⟩ := allPairsH1Map_surjective f 𝒰 (structureSheaf X) a
  obtain ⟨w, rfl⟩ := allPairsH1Map_surjective f 𝒰 (structureSheaf X) b
  rw [h1DeformationHom_allPairsH1Map, h1DeformationHom_allPairsH1Map] at hab
  have hb := (cocycleDeformationHom_eq_iff preservation f 𝒰 z w).mp hab
  have hzero := (allPairsH1Map_eq_zero_iff f 𝒰 (structureSheaf X) (w - z)).mpr hb
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero.symm

/-- Normalized frames on the prescribed affine cover present every actual deformation. -/
lemma h1DeformationHom_surjective :
    Function.Surjective (h1DeformationHom preservation f 𝒰) := by
  intro q
  obtain ⟨L, hL⟩ := Quotient.exists_rep q.toMul.val
  change LineBundle.isoClass preservation L = q.toMul.val at hL
  have hred :
      LineBundle.isoClass preservation ((LineBundle.pullback (closedPoint f)).obj L) =
        LineBundle.isoClass preservation (LineBundle.trivial X) := by
    change LineBundle.pullbackHom preservation (closedPoint f)
      (LineBundle.isoClass preservation L) = 1
    rw [hL]
    exact q.toMul.property
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp hred
  obtain ⟨z, hz, ⟨ez⟩⟩ := exists_cocycle_presentation f 𝒰.U 𝒰.iSup_eq_top
    𝒰.isAffineOpen L ((LineBundle.forget X).mapIso e)
  refine ⟨allPairsH1Map f 𝒰 (structureSheaf X) ⟨z, hz⟩, ?_⟩
  rw [h1DeformationHom_allPairsH1Map]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change LineBundle.isoClass preservation (cocycleBundle f 𝒰.U 𝒰.iSup_eq_top z hz) =
    q.toMul.val
  rw [← hL]
  exact LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ ez.symm)

/-- Actual first-order line-bundle deformation classes are the actual derived structure-sheaf
`H¹`, with tensor product corresponding to addition. -/
def deformationH1AddEquiv :
    Additive (DeformationClasses preservation f) ≃+
      (DerivedSections.relativeCohomology f 1).obj (structureSheaf X) :=
  (AddEquiv.ofBijective (h1DeformationHom preservation f 𝒰)
    ⟨h1DeformationHom_injective preservation f 𝒰,
      h1DeformationHom_surjective preservation f 𝒰⟩).symm

/-- The comparison sends each actual normalized cocycle bundle to its derived cocycle class. -/
lemma deformationH1AddEquiv_cocycleDeformationClass
    (z : allPairsCocycles (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    deformationH1AddEquiv preservation f 𝒰
        (Additive.ofMul (cocycleDeformationClass preservation f 𝒰 z)) =
      allPairsH1Map f 𝒰 (structureSheaf X) z := by
  apply (deformationH1AddEquiv preservation f 𝒰).symm.injective
  rw [AddEquiv.symm_apply_apply]
  exact (h1DeformationHom_allPairsH1Map preservation f 𝒰 z).symm

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
