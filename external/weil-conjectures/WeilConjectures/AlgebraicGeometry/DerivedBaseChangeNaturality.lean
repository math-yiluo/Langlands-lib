/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

/-! # Naturality in the coefficient of derived base change

Source: Stacks Project, Tags 08HY, 08BV and 0DJ9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Naturality of the canonical derived base-change map in its coefficient object.
Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-derived-base-change-coefficient-naturality).
Proof: The map is the mate of the natural pullback-composition comparison followed
by the pulled-back counit. Naturality of the adjunction Hom equivalence moves a
coefficient map to the two ends of the transpose. Naturality of the comparison
moves it into the pulled-back counit, and naturality of the counit equates the
resulting transposes. -/
theorem schemeDerivedBaseChangeMap_naturality
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {K L : schemeDerivedCategory X} (k : K ⟶ L) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map k ≫
        schemeDerivedBaseChangeMap f f' g g' h L =
      schemeDerivedBaseChangeMap f f' g g' h K ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map k) := by
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  let e := c f' g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (c g' f).symm
  have hn : (derivedPullback g).map ((schemeDerivedDirectImage f).map k) ≫
        (canonicalPullbackAdjunction f').homEquiv _ _
          (e.hom.app ((schemeDerivedDirectImage f).obj L) ≫
            (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app L)) =
      (canonicalPullbackAdjunction f').homEquiv _ _
          (e.hom.app ((schemeDerivedDirectImage f).obj K) ≫
            (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app K)) ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map k) := by
    simpa [Adjunction.homEquiv_unit, mateEquiv] using
      (mateEquiv (canonicalPullbackAdjunction f) (canonicalPullbackAdjunction f')
        e.hom).naturality k
  change (derivedPullback g).map ((schemeDerivedDirectImage f).map k) ≫
      (canonicalPullbackAdjunction f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj L) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj L)) h.symm) ≫
          (c g' f).inv.app ((schemeDerivedDirectImage f).obj L) ≫
          (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app L)) =
      (canonicalPullbackAdjunction f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
          (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app K)) ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map k)
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Category.assoc] using hn


end AlgebraicGeometry
