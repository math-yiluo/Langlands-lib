import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAtlasReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.QuasiAffineChart
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionSurjective

/-! # Local representation of restricted étale surjective schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace WeilRestrictionAtlas

open PointTopology

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
  [Module.Projective R R'] {V : Over (Spec (CommRingCat.of R))}
  (Y : Over (Limits.pullback V.hom (Spec.algebraMap R R')))

/-- The restriction of `Y` along the base change of `Spec R' ⟶ Spec R` to `V.left`. -/
abbrev restrictedPresheaf : Presheaf V.left :=
  (Over.pullback (pullback.fst V.hom (Spec.algebraMap R R'))).op ⋙ (schemeYoneda _).obj Y

omit [Module.Finite R R'] [Module.Projective R R'] in
/-- The restricted presheaf is an fppf sheaf. -/
lemma restrictedPresheaf_isSheaf :
    Presheaf.IsSheaf (fppfTopology V.left) (restrictedPresheaf R R' Y) :=
  ((weilRestriction (pullback.fst V.hom (Spec.algebraMap R R'))).obj
    ((schemeSheaf _).obj Y)).property

/-- Over an affine chart `Spec A ⟶ V.left`, the restricted presheaf is represented by the
glued affine-chart Weil restriction of the base change of `Y` to `Spec (A ⊗[R] R')`, which is
étale and surjective over `Spec A`. -/
theorem exists_chart_representation [Etale Y.hom] [Surjective Y.hom] [QuasiCompact Y.hom]
    [_root_.AlgebraicGeometry.IsSeparated Y.hom] (A : Type u) [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ V.left) :
    ∃ H : Over (Spec (CommRingCat.of A)),
      Nonempty ((schemeYoneda _).obj H ≅ (Over.map j).op ⋙ restrictedPresheaf R R' Y) ∧
        Etale H.hom ∧ Surjective H.hom := by
  let : Algebra R A := (Spec.preimage (j ≫ V.hom)).hom.toAlgebra
  have hA : Spec.algebraMap R A = j ≫ V.hom := Spec.map_preimage _
  have outer := isPullback_weilRestrictionTensor R R' A (A ⊗[R] R') AlgEquiv.refl
    (fun _ => rfl)
  rw [hA] at outer
  obtain ⟨j', hj⟩ : ∃ j', IsPullback j' (Spec.algebraMap A (A ⊗[R] R'))
      (pullback.fst V.hom (Spec.algebraMap R R')) j :=
    ⟨_, IsPullback.of_right' outer (IsPullback.of_hasPullback V.hom _).flip⟩
  let Yj : Over (Spec (CommRingCat.of (A ⊗[R] R'))) := (Over.pullback j').obj Y
  have : Etale Yj.hom := MorphismProperty.pullback_snd _ _ ‹Etale Y.hom›
  have : Surjective Yj.hom := MorphismProperty.pullback_snd _ _ ‹Surjective Y.hom›
  have : QuasiCompact Yj.hom := MorphismProperty.pullback_snd _ _ ‹QuasiCompact Y.hom›
  have : _root_.AlgebraicGeometry.IsSeparated Yj.hom :=
    MorphismProperty.pullback_snd _ _ ‹_root_.AlgebraicGeometry.IsSeparated Y.hom›
  have : LocallyOfFiniteType Yj.hom := inferInstance
  have : LocallyQuasiFinite Yj.hom := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale _
  have : CompactSpace Yj.left := QuasiCompact.compactSpace_of_compactSpace Yj.hom
  have : Yj.left.IsQuasiAffine :=
    LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite Yj.hom
  refine ⟨affineChartWeilRestriction A (A ⊗[R] R') Yj, ⟨?_⟩, inferInstance,
    affineChartWeilRestriction_surjective A (A ⊗[R] R') Yj⟩
  exact quasiAffineWeilRestrictionPresheafIso A (A ⊗[R] R') Yj ≪≫
    Functor.isoWhiskerLeft (Over.pullback (Spec.algebraMap A (A ⊗[R] R'))).op
      (schemeYonedaBaseChangeIso j' Y) ≪≫
    (weilRestrictionBaseChangePresheafIso hj ((schemeYoneda _).obj Y)).symm

/-- The local representation input holds: the restriction of an étale surjective
quasi-compact separated scheme over `V ×_{Spec R} Spec R'` is represented by an étale
surjective scheme over `V`. -/
theorem representationInput : RepresentationInput.{u} := by
  intro R R' _ _ _ _ _ V Y hE hS hQ hP
  let 𝒰 := V.left.affineOpenCover
  choose H e hHE hHS using fun i : 𝒰.I₀ =>
    exists_chart_representation R R' Y (𝒰.X i) (𝒰.f i)
  obtain ⟨W, ⟨eW⟩⟩ := LocalRepresentation.exists_representation
    (restrictedPresheaf_isSheaf R R' Y) 𝒰.openCover H (fun i => (e i).some)
  exact ⟨W, ⟨eW⟩,
    LocalRepresentation.property_of_local_representations (@Etale) W eW 𝒰.openCover H
      (fun i => (e i).some) hHE,
    LocalRepresentation.property_of_local_representations (@Surjective) W eW 𝒰.openCover H
      (fun i => (e i).some) hHS⟩

end WeilRestrictionAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
