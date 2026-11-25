/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeFiniteCoefficientTransport

import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement

/-! # Slice equivalence for the explicit relative coefficient transport

## References

* Stacks Project, Sites, Tag 03A0
* Stacks Project, Modules on Sites, Tag 03CY
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem isoRestriction_isEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [S.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : S ⟶ S ↦ (f.hom.app V).hom x) c.inv_hom_id.symm)
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [R.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R ⟶ R ↦ (f.hom.app V).hom x) c.hom_inv_id)
  exact inferInstanceAs e.functor.IsEquivalence

/-- The explicit coefficient transport carries isomorphisms on the corresponding
small and pro-étale slices in both directions. -/
theorem relativeFiniteModelSliceEquivalence {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (F G : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
    (V : proEtaleSiteModel Y) :
    Nonempty (F.over (AsSmall.down.obj V) ≅ G.over (AsSmall.down.obj V)) ↔
      Nonempty (((relativeFiniteModelModules g B).obj F).over V ≅
        ((relativeFiniteModelModules g B).obj G).over V) := by
  let R := (adicTowerInverseImage g).obj (adicLisseConstantRing X B)
  let d : proEtaleSiteModel Y ⥤ Y.ProEt := AsSmall.down
  have : d.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : d.IsDenseSubsite (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have := CategoryTheory.NativeRestriction.sliceDense
    (K := proEtaleModelTopology Y) (J := ProEt.topology Y) d V
  let T := SheafOfModules.pushforward.{u + 1}
    (F := Over.post (X := V) d)
    (J := (proEtaleModelTopology Y).over V)
    (K := (ProEt.topology Y).over (d.obj V))
    (R := ((adicLisseForget Y).obj R).over (d.obj V)) (𝟙 _)
  have := CategoryTheory.NativeRestriction.sliceModulesEquivalence.{u + 1, u + 1,
      u + 1, u, u + 1} (K := proEtaleModelTopology Y) d R V
  have : T.IsEquivalence := Functor.isEquivalence_of_iso
    (CategoryTheory.NativeRestriction.restrictModules_standardIso.{u + 1, u + 1,
      u + 1, u, u + 1} (K := (proEtaleModelTopology Y).over V)
      (Over.post d) (R.over (d.obj V)))
  let c := ((proEtaleModelTopology Y).overPullback RingCat.{u + 1} V).mapIso
    ((sheafCompose (proEtaleModelTopology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (relativeFiniteModelCoefficient g B))
  let S := SheafOfModules.restrictScalars.{u + 1} c.hom
  have : S.IsEquivalence := isoRestriction_isEquivalence c
  let E := T ⋙ S
  change Nonempty (F.over (d.obj V) ≅ G.over (d.obj V)) ↔
    Nonempty (E.obj (F.over (d.obj V)) ≅ E.obj (G.over (d.obj V)))
  constructor
  · rintro ⟨e⟩
    exact ⟨E.mapIso e⟩
  · rintro ⟨e⟩
    exact ⟨E.preimageIso e⟩

end AlgebraicGeometry.Scheme
