/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.CoefficientSquareCoordinateChange

/-! Canonical coefficient coherence for a nested open square.
Source: Stacks Project, Tag 0D5S.
(blueprint: new-canonical-relative-mv-open-square-coefficient-coherence)

The identity follows by applying the coordinate-change theorem to the two
pullback squares and expanding the canonical comparison components. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem comparison_inv_map_id
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (e : F ⋙ G ≅ H) (N : C) :
    e.inv.app N ≫ G.map (𝟙 (F.obj N)) = e.inv.app N := by
  rw [CategoryTheory.Functor.map_id]
  exact CategoryTheory.Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical coefficient coherence with all comparison maps expanded.
Source: Stacks Project, Tag 0D5S.
(blueprint: new-canonical-relative-mv-open-square-coefficient-coherence)

Proof: instantiate `coefficient_square_coordinate_change` with the two open
immersions and the relative Mayer--Vietoris lift, then expand the components
of the three comparison isomorphisms. Naturality and proof irrelevance identify
all equality transports. -/
theorem canonical_relativeMV_open_square_coefficient_coherence
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (W U : X.Opens) (i : W ≤ U)
    (N : schemeDerivedCategory X) :
    (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp (X.homOfLE i) U.ι ≪≫
          eqToIso (congrArg (fun k ↦ derivedPullback k)
            (Scheme.homOfLE_ι X i))).hom.app N) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app N ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app N =
    (relativeMVComp (pullback.snd g' W.ι) (X.homOfLE i) ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (pullback.lift_snd _ _ _).symm) ≪≫
      (relativeMVComp (relativeMVOpenLift g' i)
        (pullback.snd g' U.ι)).symm).hom.app
      ((derivedPullback U.ι).obj N) ≫
      (derivedPullback (relativeMVOpenLift g' i)).map
        ((relativeMVComp (pullback.snd g' U.ι) U.ι).hom.app N ≫
          eqToHom (congrArg (fun k ↦ (derivedPullback k).obj N)
            (pullback.condition (f := g') (g := U.ι)).symm) ≫
          (relativeMVComp (pullback.fst g' U.ι) g').inv.app N) ≫
      (relativeMVComp (relativeMVOpenLift g' i)
        (pullback.fst g' U.ι) ≪≫
        eqToIso (congrArg (fun k ↦ derivedPullback k)
          (pullback.lift_fst _ _ _))).hom.app ((derivedPullback g').obj N) := by
  classical
  have h := coefficient_square_coordinate_change g' W.ι U.ι
    (pullback.snd g' W.ι) (pullback.fst g' W.ι)
    (pullback.snd g' U.ι) (pullback.fst g' U.ι)
    (X.homOfLE i) (relativeMVOpenLift g' i)
    (Scheme.homOfLE_ι X i) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    (pullback.condition (f := g') (g := U.ι)).symm
    (pullback.condition (f := g') (g := W.ι)).symm
    N ((derivedPullback g').obj N) (𝟙 _)
  generalize hc : @Classical.choose _ _ (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition))) = c at h
  dsimp only at h
  simp only [comparison_inv_map_id] at h
  simpa only [relativeMVComp, hc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, CategoryTheory.Category.assoc] using h

end AlgebraicGeometry
