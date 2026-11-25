/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleOver
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Transfer of weak contractibility to the scheme's own site -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u a b v w t
open CategoryTheory CategoryTheory.Limits Opposite

private theorem weaklyContractible_transfer
    {C : Type a} [Category.{v} C] {D : Type b} [Category.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.inverse.IsDenseSubsite K J]
    [HasSheafify J (Type t)] [HasSheafify K (Type t)] (U : C) (hU : J.IsWeaklyContractible.{t} U) :
    K.IsWeaklyContractible.{t} (e.functor.obj U) := by
  intro F G f hf
  let S := e.sheafCongr J K (Type t)
  have : Epi f := (Sheaf.isLocallySurjective_iff_epi f).1 hf
  have : Epi (S.inverse.map f) := inferInstance
  exact hU (S.inverse.map f)
    ((Sheaf.isLocallySurjective_iff_epi (S.inverse.map f)).2 inferInstance)

namespace AlgebraicGeometry.Scheme.ProEt

/-- A weakly contractible pro-etale object has weakly contractible final object on
its own small site. Source: Stacks Tags 090M, 00Y1 and 094T.
(blueprint: lem-pe-proetale-weakly-contractible-self).

Proof: transport the site to its coefficient-sized model. Localizing at the given
object preserves weak contractibility, by the fibre description of the slice topos.
Transport back along the equivalence of over categories, then identify this slice
with the small pro-etale site of the underlying scheme. The identity arrow becomes
the final object of that site. All transports preserve epimorphisms and their
section maps. -/
theorem isWeaklyContractible_self_of_object (X : Scheme.{u}) (W : X.ProEt)
    (hW : (topology X).IsWeaklyContractible.{u + 1} W) :
    (topology W.left).IsWeaklyContractible.{u + 1} (ProEt.mk (𝟙 W.left)) := by
  let C := coefficientProEtaleSiteModel.{u, u} X
  let J := coefficientProEtaleModelTopology.{u, u} X
  let e : X.ProEt ≌ C := AsSmall.equiv
  have : (AsSmall.down : C ⥤ X.ProEt).IsEquivalence := e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite J (topology X) := by
    change (AsSmall.down : C ⥤ X.ProEt).IsDenseSubsite
      ((AsSmall.down : C ⥤ X.ProEt).inducedTopology (topology X)) (topology X)
    infer_instance
  have hsmall : J.IsWeaklyContractible.{u + 1} (e.functor.obj W) :=
    weaklyContractible_transfer (topology X) J e W hW
  have hover := J.isWeaklyContractible_over (e.functor.obj W) hsmall
  have : e.inverse.IsCocontinuous J (topology X) := inferInstance
  have : e.functor.IsCocontinuous (topology X) J := inferInstance
  let q : Over (e.functor.obj W) ≌ Over W := Over.postEquiv (e.functor.obj W) e.symm
  have : q.functor.IsCocontinuous (J.over (e.functor.obj W)) ((topology X).over W) := by
    change (Over.post (X := e.functor.obj W) e.inverse).IsCocontinuous _ _
    exact inferInstanceAs ((Over.post (X := e.functor.obj W) e.inverse).IsCocontinuous
      (J.over (e.functor.obj W)) ((topology X).over (e.inverse.obj (e.functor.obj W))))
  have : q.inverse.IsCocontinuous ((topology X).over W) (J.over (e.functor.obj W)) := by
    change (Over.post e.functor ⋙ Over.map _).IsCocontinuous _ _
    exact CategoryTheory.isCocontinuous_comp (Over.post e.functor) (Over.map _)
      ((topology X).over W) (J.over (e.functor.obj W))
  have : q.inverse.IsDenseSubsite ((topology X).over W) (J.over (e.functor.obj W)) :=
    q.isDenseSubsite_inverse_of_isCocontinuous _ _
  have hslice := weaklyContractible_transfer (J.over (e.functor.obj W))
    ((topology X).over W) q (Over.mk (𝟙 (e.functor.obj W))) hover
  change ((topology X).over W).IsWeaklyContractible.{u + 1} (Over.mk (𝟙 W)) at hslice
  have : (sliceEquiv X W).inverse.IsDenseSubsite (topology W.left) ((topology X).over W) :=
    sliceDense X W
  exact weaklyContractible_transfer ((topology X).over W) (topology W.left)
    (sliceEquiv X W) (Over.mk (𝟙 W)) hslice

end AlgebraicGeometry.Scheme.ProEt
