import Langlands.AlgebraicGeometry.Modules.CechResolution.ScalarDerivedBaseChange
import Langlands.AlgebraicGeometry.Modules.CechResolution.AffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.NoetherianCechProjectiveRepresentativeProof

/-! # Scalar Čech cochain isomorphisms and bounded flat terms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.ModuleComplex
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

section ScalarMap

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ) [IsAffineHom g]
  (M : X.Modules) (𝒰 : X.OrderedAffineCover)

/-- The actual scalar Čech map on integer-extended alternating cochains. -/
def scalarCechIntegerCochainMap :
    (baseChange φ.hom).obj
        ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) ⟶
      (cechCochainComplex f' (inverseImageCover g 𝒰)
        ((Scheme.Modules.pullback g).obj M)).extend ComplexShape.embeddingUpNat :=
  (extendMapIso ComplexShape.embeddingUpNat (ModuleCat.extendScalars φ.hom)
      (cechCochainComplex f 𝒰 M)).hom ≫
    HomologicalComplex.extendMap
      (scalarCechCochainMap φ f f' g w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰)
      ComplexShape.embeddingUpNat

/-- The scalar cochain map is invertible for a separated Cartesian square. -/
lemma isIso_scalarCechCochainMap_of_isPullback
    [IsSeparated f] [M.IsQuasicoherent]
    (hp : IsPullback g f' f (Spec.map φ)) :
    IsIso (scalarCechCochainMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰) := by
  let := isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated g M φ f f' w 𝒰 hp
  dsimp only [scalarCechCochainMap]
  infer_instance

/-- The same actual map remains invertible after extension to integer degrees. -/
lemma isIso_scalarCechIntegerCochainMap_of_isPullback
    [IsSeparated f] [M.IsQuasicoherent]
    (hp : IsPullback g f' f (Spec.map φ)) :
    IsIso (scalarCechIntegerCochainMap φ f f' g w M 𝒰) := by
  let := isIso_scalarCechCochainMap_of_isPullback φ f f' g w M 𝒰 hp
  dsimp only [scalarCechIntegerCochainMap]
  have : IsIso (HomologicalComplex.extendMap
      (scalarCechCochainMap φ f f' g w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) 𝒰)
      ComplexShape.embeddingUpNat) := by
    change IsIso ((ComplexShape.embeddingUpNat.extendFunctor _).map _)
    infer_instance
  infer_instance

end ScalarMap

section Factorization

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  {φ : R ⟶ S} {f : X ⟶ Spec R} {f' : Y ⟶ Spec S} {g : Y ⟶ X}
  (hp : IsPullback g f' f (Spec.map φ)) (L : LineBundle X)
  (𝒰 : X.OrderedAffineCover) {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Base change of a map to Čech cochains factors through the scalar Čech map. -/
lemma cechBaseChangeCochainMap_eq
    (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat) :
    letI := isAffineHom_of_isPullback_spec hp
    cechBaseChangeCochainMap hp L 𝒰 v =
      (baseChange φ.hom).map v ≫ scalarCechIntegerCochainMap φ f f' g hp.w L.obj 𝒰 := by
  let := isAffineHom_of_isPullback_spec hp
  rfl

end Factorization

section BoundedFlat

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (f : X ⟶ Spec R) (𝒰 : X.OrderedAffineCover) (M : X.Modules)

/-- There are no alternating cochains above the cardinality of the finite cover. -/
lemma subsingleton_cechCochainComplex_X (i : ℕ) (hi : Fintype.card 𝒰.ι < i) :
    Subsingleton ((cechCochainComplex f 𝒰 M).X i) := by
  exact CechProjectiveTransport.subsingleton_cochain
    (OModulePresheaf.ofModules f M) 𝒰 (by omega)

/-- The integer extension of the Čech complex is strictly bounded above. -/
lemma isStrictlyLE_extend_cechCochainComplex :
    CochainComplex.IsStrictlyLE
      ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat)
      (Fintype.card 𝒰.ι : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro z hz
  obtain h | ⟨i, hi⟩ := (ComplexShape.embeddingUpNat.r z).eq_none_or_eq_some
  · exact (cechCochainComplex f 𝒰 M).isZero_extend_X' _ z h
  · have he : (i : ℤ) = z := ComplexShape.embeddingUpNat.f_eq_of_r_eq_some hi
    let := subsingleton_cechCochainComplex_X f 𝒰 M i (by omega)
    exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton ((cechCochainComplex f 𝒰 M).X i))
      ((cechCochainComplex f 𝒰 M).extendXIso _ he)

/-- Extension from natural cochain degrees is strictly bounded below by zero. -/
lemma isStrictlyGE_extend_cechCochainComplex :
    CochainComplex.IsStrictlyGE
      ((cechCochainComplex f 𝒰 M).extend ComplexShape.embeddingUpNat) 0 :=
  inferInstance

variable [Flat f] [IsSeparated f] (L : LineBundle X)

/-- Flatness of the family makes every line-bundle Čech cochain term flat. -/
lemma flat_cechCochainComplex_X (i : ℕ) :
    Module.Flat R ((cechCochainComplex f 𝒰 L.obj).X i) := by
  apply OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f L.obj
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.property x
  exact ⟨U, hx, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj).symm ≪≫ e⟩⟩

/-- The integer-extended line-bundle Čech complex is termwise flat. -/
lemma flat_extend_cechCochainComplex_X (z : ℤ) :
    Module.Flat R
      (((cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat).X z) := by
  obtain h | ⟨i, hi⟩ := (ComplexShape.embeddingUpNat.r z).eq_none_or_eq_some
  · let := ModuleCat.subsingleton_of_isZero
      ((cechCochainComplex f 𝒰 L.obj).isZero_extend_X' _ z h)
    infer_instance
  · let := flat_cechCochainComplex_X f 𝒰 L i
    exact Module.Flat.of_linearEquiv
      ((cechCochainComplex f 𝒰 L.obj).extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat.f_eq_of_r_eq_some hi)).toLinearEquiv

end BoundedFlat

end Langlands.AlgebraicGeometry.Modules.CechResolution
