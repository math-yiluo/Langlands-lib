import Langlands.AlgebraicGeometry.Modules.CechResolution.LineBundleBaseChange
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChangeZero
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Canonical global-functions base change over a field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Modules

namespace CechResolution

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  [IsAffineHom g] [IsSeparated f] [CompactSpace X]
  (L : LineBundle X)

/-- Flat affine base change makes the actual scalar map on ordinary
line-bundle sections invertible. -/
lemma isIso_scalarSectionsBaseChangeMap_lineBundle
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w L.obj) := by
  have hc := isIso_scalarBaseChangeMap_lineBundle g φ f f' w L h hφ 0
  rw [scalarBaseChangeMap_zero] at hc
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hc

/-- The canonical scalar map on ordinary line-bundle sections, packaged
as an isomorphism. -/
def lineBundleSectionsScalarBaseChangeIso
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj L.obj) ≅
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj L.obj) := by
  have := isIso_scalarSectionsBaseChangeMap_lineBundle φ f f' g w L h hφ
  exact asIso (scalarSectionsBaseChangeMap φ f f' g w L.obj)

@[simp]
lemma lineBundleSectionsScalarBaseChangeIso_hom
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    (lineBundleSectionsScalarBaseChangeIso φ f f' g w L h hφ).hom =
      scalarSectionsBaseChangeMap φ f f' g w L.obj := rfl

end CechResolution

namespace FieldGlobalFunctions

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual global functions with scalars supplied by the structure map. -/
abbrev sections : ModuleCat.{u} k :=
  (relativeGlobalSections f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- A morphism to the spectrum of a field is flat. -/
lemma flat : AlgebraicGeometry.Flat f := inferInstance

/-- The actual global-functions module of a proper field scheme is finite. -/
lemma finite [IsProper f] : Module.Finite k (sections f) := by
  have hq : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    (LineBundle.trivial X).property.isQuasicoherent
  have hf := properCoherentCohomologyFinite k X f inferInstance
    (SheafOfModules.unit X.ringCatSheaf) hq
    (fun U => inferInstanceAs (Module.Finite Γ(X, U.1) Γ(X, U.1)))
  let := hf.1 0
  exact Module.Finite.equiv
    ((relativeCohomologyZeroIso f).app (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv

variable [IsProper f] {Y : Scheme.{u}} {S : CommRingCat.{u}}
  (φ : CommRingCat.of k ⟶ S) (f' : Y ⟶ Spec S) (g : Y ⟶ X)
  (h : IsPullback g f' f (Spec.map φ))

/-- Canonical affine base change of global functions on any proper field
scheme, for an arbitrary target ring. -/
def baseChangeIso :
    (ModuleCat.extendScalars φ.hom).obj (sections f) ≅
      (relativeGlobalSections f').obj (SheafOfModules.unit Y.ringCatSheaf) := by
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsAffineHom g :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact CechResolution.lineBundleSectionsScalarBaseChangeIso φ f f' g h.w
      (LineBundle.trivial X) h (RingHom.Flat.of_isField (Field.toIsField k) φ.hom) ≪≫
    (relativeGlobalSections f').mapIso (Langlands.Scheme.Modules.pullbackUnitIso g)

/-- The isomorphism uses the actual scalar sections map and the canonical
identification of the pulled-back structure sheaf. -/
lemma baseChangeIso_hom :
    (baseChangeIso f φ f' g h).hom =
      scalarSectionsBaseChangeMap φ f f' g h.w (SheafOfModules.unit X.ringCatSheaf) ≫
        (relativeGlobalSections f').map
          (Langlands.Scheme.Modules.pullbackUnitIso g).hom := rfl

end FieldGlobalFunctions

end Langlands.AlgebraicGeometry.Modules
