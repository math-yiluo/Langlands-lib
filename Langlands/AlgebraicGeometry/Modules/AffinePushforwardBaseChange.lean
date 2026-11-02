import Langlands.AlgebraicGeometry.Modules.AffineCartesianSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange

/-! # Actual base change for affine pushforward of quasi-coherent modules -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The specified sheaf comparison is invertible on a cartesian square of affine schemes. -/
lemma isIso_pushforwardBaseChange_of_isPullback_affine
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X'] {R T : CommRingCat.{u}}
    (φ : R ⟶ T) (f : X ⟶ Spec R) (f' : X' ⟶ Spec T) (p : X' ⟶ X)
    (h : IsPullback p f' f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (pushforwardBaseChange (Spec.map φ) f f' p h.w M) := by
  have := QuasicoherentLocal.isQuasicoherent_pushforward f M
  have := QuasicoherentLocal.isQuasicoherent_pushforward f'
    ((Scheme.Modules.pullback p).obj M)
  have := isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ f f' p h.w h M
  exact isIso_pushforwardBaseChange_of_isIso_scalarSectionsBaseChangeMap φ f f' p h.w M

/-- Affine pushforward of a quasi-coherent module commutes with every cartesian base change,
via the actual adjunction-defined comparison. -/
lemma isIso_pushforwardBaseChange_of_isAffineHom
    {S S' X X' : Scheme.{u}} (b : S' ⟶ S) (f : X ⟶ S) [IsAffineHom f]
    (f' : X' ⟶ S') (p : X' ⟶ X) (h : IsPullback p f' f b)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (pushforwardBaseChange b f f' p h.w M) := by
  apply isIso_of_affineOpenPullbacks
  intro y
  obtain ⟨R, T, x, c, φ, hx, hc, ⟨t, hty⟩, w⟩ := exists_affineOpenFactorization b y
  have := hx
  have := hc
  let XR := pullback f x
  let pR : XR ⟶ X := pullback.fst f x
  let fR : XR ⟶ Spec R := pullback.snd f x
  have hR : IsPullback pR fR f x := IsPullback.of_hasPullback f x
  let XT := pullback f' c
  let pT : XT ⟶ X' := pullback.fst f' c
  let fT : XT ⟶ Spec T := pullback.snd f' c
  have hT : IsPullback pT fT f' c := IsPullback.of_hasPullback f' c
  have wq : (pT ≫ p) ≫ f = (fT ≫ Spec.map φ) ≫ x := by
    rw [Category.assoc, h.w, ← Category.assoc, hT.w, Category.assoc, w, Category.assoc]
  let q : XT ⟶ XR := pullback.lift (pT ≫ p) (fT ≫ Spec.map φ) wq
  have hqp : q ≫ pR = pT ≫ p := pullback.lift_fst _ _ _
  have hqf : q ≫ fR = fT ≫ Spec.map φ := pullback.lift_snd _ _ _
  have hout : IsPullback (q ≫ pR) fT f (Spec.map φ ≫ x) := by
    rw [hqp, ← w]
    exact hT.paste_horiz h
  have hq : IsPullback q fT fR (Spec.map φ) := hout.of_right hqf hR
  have : IsAffineHom fR := MorphismProperty.of_isPullback hR inferInstance
  have : IsAffineHom fT := MorphismProperty.of_isPullback hq inferInstance
  have : IsAffine XR := isAffine_of_isAffineHom fR
  have : IsAffine XT := isAffine_of_isAffineHom fT
  have := isIso_pushforwardBaseChange_of_isOpenImmersion x f fR pR hR M
  have := isIso_pushforwardBaseChange_of_isPullback_affine φ fR fT q hq
    ((Scheme.Modules.pullback pR).obj M)
  have hi : IsIso (iteratedPushforwardBaseChange x (Spec.map φ) f fR fT pR q hR.w hq.w M) := by
    unfold iteratedPushforwardBaseChange
    infer_instance
  rw [← pushforwardBaseChange_composition] at hi
  have hfull : IsIso (pushforwardBaseChange (Spec.map φ ≫ x) f fT (q ≫ pR)
      (compositeBaseChangeSquare x (Spec.map φ) f fR fT pR q hR.w hq.w) M) :=
    IsIso.of_isIso_comp_left
      ((Scheme.Modules.pullbackComp (Spec.map φ) x).hom.app
        ((Scheme.Modules.pushforward f).obj M)) _
  have hfull' := (isIso_pushforwardBaseChange_congr f fT M
    (compositeBaseChangeSquare x (Spec.map φ) f fR fT pR q hR.w hq.w)
    (hT.paste_horiz h).w w.symm hqp).mp hfull
  have ht : IsIso (iteratedPushforwardBaseChange b c f f' fT p pT h.w hT.w M) := by
    rw [← pushforwardBaseChange_composition]
    infer_instance
  have := isIso_pushforwardBaseChange_of_isOpenImmersion c f' fT pT hT
    ((Scheme.Modules.pullback p).obj M)
  have hi' : IsIso ((Scheme.Modules.pullback c).map
      (pushforwardBaseChange b f f' p h.w M)) := by
    unfold iteratedPushforwardBaseChange at ht
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p h.w M))
      (pushforwardBaseChange c f' fT pT hT.w ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pushforward fT).map ((Scheme.Modules.pullbackComp pT p).hom.app M))
  exact ⟨T, c, hc, t, hty, hi'⟩

/-- Package the actual affine pushforward base-change map as an isomorphism. -/
def affinePushforwardBaseChangeIso
    {S S' X X' : Scheme.{u}} (b : S' ⟶ S) (f : X ⟶ S) [IsAffineHom f]
    (f' : X' ⟶ S') (p : X' ⟶ X) (h : IsPullback p f' f b)
    (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback p).obj M) := by
  have := isIso_pushforwardBaseChange_of_isAffineHom b f f' p h M
  exact asIso (pushforwardBaseChange b f f' p h.w M)

@[simp]
lemma affinePushforwardBaseChangeIso_hom
    {S S' X X' : Scheme.{u}} (b : S' ⟶ S) (f : X ⟶ S) [IsAffineHom f]
    (f' : X' ⟶ S') (p : X' ⟶ X) (h : IsPullback p f' f b)
    (M : X.Modules) [M.IsQuasicoherent] :
    (affinePushforwardBaseChangeIso b f f' p h M).hom =
      pushforwardBaseChange b f f' p h.w M := rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
