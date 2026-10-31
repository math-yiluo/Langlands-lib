import Langlands.AlgebraicGeometry.Modules.CechResolution.ScalarCochainBaseChange

/-! # Detecting invertibility of base change of Čech perfect models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Langlands.Cohomology Langlands.Cohomology.ModuleComplex
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  {φ : R ⟶ S} {f : X ⟶ Spec R} {f' : Y ⟶ Spec S} {g : Y ⟶ X}
  (hp : IsPullback g f' f (Spec.map φ)) [IsSeparated f] (L : LineBundle X)
  (𝒰 : X.OrderedAffineCover) {K : CochainComplex (ModuleCat.{u} R) ℤ}
  (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat)

/-- The actual Čech base-change chain map is a quasi-isomorphism exactly when
the scalar extension of its input chain map is. -/
lemma quasiIso_cechBaseChangeCochainMap_iff :
    letI := isAffineHom_of_isPullback_spec hp
    QuasiIso (cechBaseChangeCochainMap hp L 𝒰 v) ↔
      QuasiIso ((baseChange φ.hom).map v) := by
  let := isAffineHom_of_isPullback_spec hp
  let := isIso_scalarCechIntegerCochainMap_of_isPullback φ f f' g hp.w L.obj 𝒰 hp
  rw [cechBaseChangeCochainMap_eq]
  exact quasiIso_iff_comp_right _ _

/-- Invertibility of the actual base change of a Čech perfect model is detected
by the scalar extension of its input chain map. -/
lemma isIso_perfectModelBaseChange_cechDerivedComparison_iff
    (hK : IsStrictlyPerfect K) :
    IsIso (perfectModelBaseChange hp L hK
        (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj)) ↔
      QuasiIso ((baseChange φ.hom).map v) := by
  let := isAffineHom_of_isPullback_spec hp
  let : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hp inferInstance
  let : ((Scheme.Modules.pullback g).obj L.obj).IsQuasicoherent :=
    L.property.isQuasicoherent_pullback g
  let := isIso_cechDerivedComparison f' (inverseImageCover g 𝒰)
    ((Scheme.Modules.pullback g).obj L.obj)
  rw [perfectModelBaseChange_cechDerivedComparison,
    isIso_comp_right_iff, DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact quasiIso_cechBaseChangeCochainMap_iff hp L 𝒰 v

/-- The isomorphism whose forward map is the specified perfect-model base
change, whenever scalar extension of the Čech representative is a quasi-isomorphism. -/
def cechPerfectModelBaseChangeIso (hK : IsStrictlyPerfect K)
    [QuasiIso ((baseChange φ.hom).map v)] :
    DerivedCategory.Q.obj ((baseChange φ.hom).obj K) ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback g).obj L.obj) := by
  letI := (isIso_perfectModelBaseChange_cechDerivedComparison_iff hp L 𝒰 v hK).2
    inferInstance
  exact asIso (perfectModelBaseChange hp L hK
    (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj))

@[simp]
lemma cechPerfectModelBaseChangeIso_hom (hK : IsStrictlyPerfect K)
    [QuasiIso ((baseChange φ.hom).map v)] :
    (cechPerfectModelBaseChangeIso hp L 𝒰 v hK).hom =
      perfectModelBaseChange hp L hK
        (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj) := rfl

end Langlands.AlgebraicGeometry.Modules.CechResolution
