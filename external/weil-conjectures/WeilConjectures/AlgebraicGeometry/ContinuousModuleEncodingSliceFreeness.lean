/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-! # Finite freeness on pro-etale slices
Source: Stacks Project, Tags 03DM and 03DO.
(auxiliary; not a blueprint node)
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Finite freeness on the localized site is detected by raw internal inverse image.
Source: Stacks Project, Tags 03DM and 03DO.
(auxiliary; not a blueprint node)

Proof. The equivalence of the pro-etale slice with the source site induces an
equivalence of module sheaves, preserving the unit and finite free modules.
The continuous-chart restriction comparison identifies its value on the
restricted encoding with the encoding of canonical inverse image. The latter
is finite free exactly when raw inverse image is finite free, since the
canonical coefficient comparison is invertible. -/
theorem continuousRing_slice_free_iff
    (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (W : X.ProEt) :
    (∃ n : ℕ, Nonempty (((continuousRingModuleEquivalence X T).functor.obj P).over W ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
      (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P) := by
  let R := continuousMapRingSheaf X T
  let S := continuousMapRingSheaf W.left T
  let e := Scheme.ProEt.sliceEquiv X W
  let : e.inverse.IsDenseSubsite (Scheme.ProEt.topology W.left)
      ((Scheme.ProEt.topology X).over W) := Scheme.ProEt.sliceDense X W
  let c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology W.left) ((Scheme.ProEt.topology X).over W)).obj (R.over W) :=
    Iso.refl _
  obtain ⟨q, hq⟩ := Scheme.ProEt.module_transport
    ((Scheme.ProEt.topology X).over W) (Scheme.ProEt.topology W.left)
    e (R.over W) S c
  have hforget (N : SheafOfModules.{u + 1} (R.over W)) :
      (q.functor.obj N).val = (PresheafOfModules.pushforward c.hom.hom).obj N.val :=
    congrArg (fun F ↦ F.obj N) hq
  let η : SheafOfModules.unit S ≅ q.functor.obj (SheafOfModules.unit (R.over W)) := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    change (SheafOfModules.unit S).val ≅
      (q.functor.obj (SheafOfModules.unit (R.over W))).val
    rw [hforget]
    refine PresheafOfModules.isoMk (fun Z ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext m
      rfl
    · intro Z Z' a
      ext
      rfl
  let M := (continuousRingModuleEquivalence X T).functor.obj P
  let Q := (upperStar (X := W.left) (Y := X)
    (Profinite.continuousMapRingObj T) W.hom).obj P
  let F := continuousRingModuleEquivalence W.left T
  obtain ⟨er⟩ := continuousRing_module_restriction X W.left W.hom T P
  let es : (q.functor.obj (M.over W)).val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap W.hom T)).obj M.val := by
    rw [hforget]
    refine PresheafOfModules.isoMk (fun Z ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext m
      rfl
    · intro Z Z' a
      ext m
      rfl
  let em : q.functor.obj (M.over W) ≅ F.functor.obj Q :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso (es ≪≫ er.symm)
  have he :
      (∃ n : ℕ, Nonempty (M.over W ≅ SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
      Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj T) W.left) Q := by
    constructor
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨F.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em.symm ≪≫ q.functor.mapIso en ≪≫
        (SheafOfModules.mapFreeIso q.functor _ η).symm ≪≫
          (continuousRingFreeIso W.left T n).symm
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨q.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em ≪≫ F.functor.mapIso en ≪≫ continuousRingFreeIso W.left T n ≪≫
        SheafOfModules.mapFreeIso q.functor _ η
  rw [he]
  let φ := condensedPullbackHom (X := W.left) (Y := X)
    (Profinite.continuousMapRingObj T) W.hom
  let Qraw := ((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P
  let ec := (Mod.extendScalarsIsoComapInv φ).app Qraw
  let E := Mod.comapEquivalenceOfIsIso (inv φ)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let ef (n : ℕ) : E.functor.obj (Mod.finiteFree _ n) ≅ Mod.finiteFree _ n :=
    E.functor.mapBiproduct (fun _ : Fin n ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.regularIsoOfIsIso φ)
  constructor
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨E.fullyFaithfulFunctor.preimageIso (ec.symm ≪≫ en ≪≫ (ef n).symm)⟩⟩
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨ec ≪≫ E.functor.mapIso en ≪≫ ef n⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
