import Langlands.AlgebraicGeometry.Modules.CechResolution.PerfectModelBaseChange
import Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange

/-! # Base change of Čech perfect models for flat separated families -/

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

section ScalarExtension

variable {X : Scheme.{u}} {R S : CommRingCat.{u}}
  (φ : R ⟶ S) (f : X ⟶ Spec R) [Flat f] [IsSeparated f]
  (L : LineBundle X) (𝒰 : X.OrderedAffineCover)
  {K : CochainComplex (ModuleCat.{u} R) ℤ}
  (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat)
  [QuasiIso v]

/-- Any scalar extension preserves a quasi-isomorphism from a strictly perfect
complex to the line-bundle Čech complex of a flat separated family. -/
lemma quasiIso_baseChange_cechRepresentative_of_flat (hK : IsStrictlyPerfect K) :
    QuasiIso ((baseChange φ.hom).map v) := by
  obtain ⟨_, b, _, hb⟩ := hK.1
  let := hb
  let := isStrictlyLE_extend_cechCochainComplex f 𝒰 L.obj
  let := K.isStrictlyLE_of_le b (max b (Fintype.card 𝒰.ι : ℤ)) (le_max_left _ _)
  let := CochainComplex.isStrictlyLE_of_le
    ((cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat)
    (Fintype.card 𝒰.ι : ℤ) (max b (Fintype.card 𝒰.ι : ℤ)) (le_max_right _ _)
  exact quasiIso_baseChange_map_of_flat φ.hom v (max b (Fintype.card 𝒰.ι : ℤ))
    (fun n ↦ by
      let := (hK.2 n).2
      infer_instance)
    (flat_extend_cechCochainComplex_X f 𝒰 L)

end ScalarExtension

section GeometricBaseChange

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  {φ : R ⟶ S} {f : X ⟶ Spec R} {f' : Y ⟶ Spec S} {g : Y ⟶ X}
  (hp : IsPullback g f' f (Spec.map φ)) [Flat f] [IsSeparated f]
  (L : LineBundle X) (𝒰 : X.OrderedAffineCover)
  {K : CochainComplex (ModuleCat.{u} R) ℤ}
  (v : K ⟶ (cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat)
  [QuasiIso v]

/-- The actual base-change Čech chain map is a quasi-isomorphism for a strictly
perfect representative of a line bundle on a flat separated family. -/
lemma quasiIso_cechBaseChangeCochainMap_of_flat (hK : IsStrictlyPerfect K) :
    letI := isAffineHom_of_isPullback_spec hp
    QuasiIso (cechBaseChangeCochainMap hp L 𝒰 v) := by
  exact (quasiIso_cechBaseChangeCochainMap_iff hp L 𝒰 v).2
    (quasiIso_baseChange_cechRepresentative_of_flat φ f L 𝒰 v hK)

/-- The specified perfect-model base-change morphism is invertible for a flat
separated family and any Cartesian change of affine base. -/
lemma isIso_perfectModelBaseChange_cechDerivedComparison_of_flat
    (hK : IsStrictlyPerfect K) :
    IsIso (perfectModelBaseChange hp L hK
      (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj)) := by
  exact (isIso_perfectModelBaseChange_cechDerivedComparison_iff hp L 𝒰 v hK).2
    (quasiIso_baseChange_cechRepresentative_of_flat φ f L 𝒰 v hK)

/-- The actual perfect-model base-change isomorphism for a flat separated family. -/
def cechPerfectModelBaseChangeIso_of_flat (hK : IsStrictlyPerfect K) :
    DerivedCategory.Q.obj ((baseChange φ.hom).obj K) ≅
      (DerivedPlus.derivedComplex (relativeGlobalSections f') ⋙
        DerivedCategory.Plus.ι).obj ((Scheme.Modules.pullback g).obj L.obj) := by
  let := quasiIso_baseChange_cechRepresentative_of_flat φ f L 𝒰 v hK
  exact cechPerfectModelBaseChangeIso hp L 𝒰 v hK

@[simp]
lemma cechPerfectModelBaseChangeIso_of_flat_hom (hK : IsStrictlyPerfect K) :
    (cechPerfectModelBaseChangeIso_of_flat hp L 𝒰 v hK).hom =
      perfectModelBaseChange hp L hK
        (DerivedCategory.Q.map v ≫ cechDerivedComparison f 𝒰 L.obj) := rfl

end GeometricBaseChange

end Langlands.AlgebraicGeometry.Modules.CechResolution
