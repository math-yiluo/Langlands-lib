/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardAcyclic
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Acyclicity after pullback of an affine-open direct image

Source: Stacks Project, Tag 02KG, and the affine intersection paragraphs of
`lem-pc-s3-affine-alternating-cech-resolution-core`.
(blueprint: lem-pc-s3-affine-open-pushforward-pullback-acyclic).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Arbitrary base change of an affine-open direct image is acyclic over the new affine base.
Source: Stacks Project, Tag 02KG; parent resolution node, affine intersection paragraph.
(blueprint: lem-pc-s3-affine-open-pushforward-pullback-acyclic).

Proof: Write p:X times Spec B -> X and f' for the other projection. Since f is
separated and Spec A is affine, X is separated, so the inclusion j:W->X of an affine
open is affine. Its base change j':W'->X' is the inclusion of the affine open W',
since W' is the fibre product of the affine schemes W and Spec B over Spec A.
The restriction G|W is quasi-coherent. Affine pushforward base change (02KG) identifies
p*(j_* G|W) with j'_* (p_W*(G|W)). Restriction and pullback commute, and pullback
preserves quasi-coherence, so the latter coefficient is (p*G)|W'. The affine-open
pushforward acyclicity theorem applied to the separated morphism f':X'->Spec B and
W' gives rightAcyclic of that direct image. Transport along the base change
isomorphism. The empty open gives a zero module and is included in the argument.
No flatness of g is needed, because base change here is along the affine j. -/
theorem affine_open_pushforward_pullback_rightAcyclic
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    (W : X.Opens) (hW : IsAffineOpen W)
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).rightAcyclic
      ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj
        ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι))) := by
  let p := pullback.fst f g
  let W' := p ⁻¹ᵁ W
  let pW := p ∣_ W
  have : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ f) := inferInstance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  have : IsAffineHom g := inferInstance
  have : IsAffineHom p := MorphismProperty.pullback_fst _ _ ‹IsAffineHom g›
  have hW' : IsAffineOpen W' := hW.preimage p
  let eP (Y Z : Scheme.{u}) (h : Y ⟶ Z) :
      Scheme.Modules.tensorPullback h ≅ Scheme.Modules.pullback h :=
    Adjunction.leftAdjointUniq (Scheme.Modules.nonempty_tensorPullbackAdjunction h).some
      (Scheme.Modules.pullbackPushforwardAdjunction h)
  have hPG : ((Scheme.Modules.tensorPullback p).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf).prop_of_iso
      ((eP _ _ p).app G).symm (Scheme.Modules.isQuasicoherent_pullback p G)
  let eR : ((Scheme.Modules.tensorPullback p).obj G).restrict W'.ι ≅
      (Scheme.Modules.tensorPullback pW).obj (G.restrict W.ι) :=
    (Scheme.Modules.restrictFunctor W'.ι).mapIso ((eP _ _ p).app G) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W'.ι).app
        ((Scheme.Modules.pullback p).obj G) ≪≫
      (Scheme.Modules.pullbackComp W'.ι p).app G ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι p W).symm).app G ≪≫
      (Scheme.Modules.pullbackComp pW W.ι).symm.app G ≪≫
      (Scheme.Modules.pullback pW).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app G).symm ≪≫
      ((eP _ _ pW).app (G.restrict W.ι)).symm
  have hbase := (Scheme.Modules.affinePushforward_baseChange W.ι W'.ι p pW
    (isPullback_morphismRestrict p W) (G.restrict W.ι)).2
  let eB := asIso (Scheme.Modules.moduleBaseChangeMap W.ι W'.ι p pW
    (isPullback_morphismRestrict p W).w (G.restrict W.ι))
  apply (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).rightAcyclic.prop_of_iso
    (eB ≪≫ (Scheme.Modules.pushforward W'.ι).mapIso eR.symm).symm
  exact affine_open_pushforward_rightAcyclic (pullback.snd f g) W' hW'
    ((Scheme.Modules.tensorPullback p).obj G)

end AlgebraicGeometry
