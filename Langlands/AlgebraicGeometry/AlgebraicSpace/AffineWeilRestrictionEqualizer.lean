import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionEqualizerRepresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionClosedEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorBaseChange

/-! # Weil equalizer representations over arbitrary affine test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

/-- Transport a full-slice representation across an isomorphism of its base. -/
def representedBaseIso {T U : Scheme.{u}} (e : U ≅ T) (W : Over U)
    {H : Presheaf T}
    (eW : (schemeYoneda U).obj W ≅ (Over.map e.hom).op ⋙ H) :
    (schemeYoneda T).obj ((Over.pullback e.inv).obj W) ≅ H := by
  let d : 𝟭 (Over T) ≅ Over.map e.inv ⋙ Over.map e.hom :=
    (Over.mapId T).symm ≪≫
      Over.mapCongr (𝟙 T) (e.inv ≫ e.hom) e.inv_hom_id.symm ≪≫
      Over.mapComp e.inv e.hom
  exact representedBaseChangeIso e.inv W eW ≪≫
    Functor.isoWhiskerRight (NatIso.op d) H

open PointTopology WeilRestrictionEqualizer WeilRestrictionDiagonalGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
  [Module.Finite R R'] [Module.Projective R R']
  (X' : AlgebraicSpace (Spec (CommRingCat.of R'))) (hX : IsQuasiSeparated X')
  (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left]
  (x y : ((ringWeilRestriction R R').obj X'.toSheaf).obj.obj (op T))

include hX in
/-- Over every affine test scheme, the equality presheaf of two points of the
full Weil restriction has a quasi-compact scheme representative. The same
representative is closed whenever the original space is separated. -/
theorem exists_affineTest_sectionEqualizer_weil :
    ∃ W : Over T.left,
      Nonempty ((schemeYoneda T.left).obj W ≅ sectionEqualizer x y) ∧
      QuasiCompact W.hom ∧
      (IsSeparated X' → _root_.AlgebraicGeometry.IsClosedImmersion W.hom) := by
  let A := AffineCoordinateRing R T
  let B := A ⊗[R] R'
  let eT := affineSchemeOverIso R T
  let e : Spec (CommRingCat.of A) ≅ T.left := (Over.forget _).mapIso eT.symm
  let f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := e.hom ≫ T.hom
  let f' : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R') := Spec.algebraMap R' B
  have h : IsPullback f' (Spec.algebraMap A B) (Spec.algebraMap R R') f := by
    have hf : f = Spec.algebraMap R A := Over.w eT.inv
    rw [hf]
    exact isPullback_weilRestrictionTensor R R' A B (AlgEquiv.refl : A ⊗[R] R' ≃ₐ[A] B)
      (fun _ ↦ rfl)
  let F := X'.presheaf
  let k : Over.mk f ⟶ T := Over.homMk e.hom
  let xA := ((Over.pullback (Spec.algebraMap R R')).op ⋙ F).map k.op x
  let yA := ((Over.pullback (Spec.algebraMap R R')).op ⋙ F).map k.op y
  let xB := F.map (baseTestIso h).hom.op xA
  let yB := F.map (baseTestIso h).hom.op yA
  let : IsAffine (Over.mk f').left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  obtain ⟨Z, j, hm, hj, hlft, _, hqa⟩ :=
    exists_quasiAffine_representsEqualizer X' hX xB yB
  let : Mono j.left := hm
  let Y : Over (Spec (CommRingCat.of B)) := Over.mk j.left
  let : Y.left.IsQuasiAffine := hqa
  let : LocallyOfFiniteType Y.hom := hlft
  let W := affineChartWeilRestriction A B Y
  let eW : (schemeYoneda _).obj W ≅ sectionEqualizer xA yA :=
    sectionEqualizerWeilRepresentationIso h F xA yA j hj W
      (quasiAffineWeilRestrictionPresheafIso A B Y)
  let eW' : (schemeYoneda _).obj W ≅ (Over.map e.hom).op ⋙ sectionEqualizer x y :=
    eW ≪≫ (sectionEqualizerRestrictIso x y e.hom).symm
  let W' := (Over.pullback e.inv).obj W
  let : QuasiCompact W.hom :=
    (quasiAffineWeilRestriction_schemeProperties A B Y).2.1
  refine ⟨W', ⟨representedBaseIso e W eW'⟩, ?_, ?_⟩
  · change QuasiCompact (pullback.snd W.hom e.inv)
    infer_instance
  · intro hsep
    let : _root_.AlgebraicGeometry.IsClosedImmersion Y.hom :=
      property_of_mono_representsEqualizer hsep hj
    let : _root_.AlgebraicGeometry.IsClosedImmersion W.hom :=
      quasiAffineWeilRestriction_hom_isClosedImmersion A B Y
    change _root_.AlgebraicGeometry.IsClosedImmersion (pullback.snd W.hom e.inv)
    infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
