/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.Modules.AffineDescent

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry
noncomputable section
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.pullbackComp
  pullbackCompOfEq Scheme.Modules.pullbackCongr
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The abstract module pullback formula for base change of a pair morphism.
Source: Stacks Project, Tag 0097, functoriality of inverse images.
(blueprint: lem-pc-overlap-base-change-formula).

Proof: The two projection equations identify l with the canonical universal
lift by the pullback universal property. Substitute that equality and expand
overlapPairBaseChangeHom. Its exterior mapComp components are
inverse pullback composition and pullback composition, respectively. The
pullHom in the middle is inverse pullbackCompOfEq, pullback of φ, and
pullbackCompOfEq, by modulesPseudofunctor_pullHom_eq_pullbackCompOfEq.
Regroup these four exterior comparisons as the two displayed isomorphisms. -/
theorem overlap_base_change_formula
    {S T A B A' B' : Scheme.{u}} (f : A ⟶ S) (g : B ⟶ S) (p : T ⟶ S)
    (v : A' ⟶ A) (w : B' ⟶ B) (f' : A' ⟶ T) (g' : B' ⟶ T)
    (hv : v ≫ f = f' ≫ p) (hw : w ≫ g = g' ≫ p)
    (N : A.Modules) (M : B.Modules)
    (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj N ⟶
      (Scheme.Modules.pullback (pullback.snd f g)).obj M)
    (l : pullback f' g' ⟶ pullback f g)
    (hlf : l ≫ pullback.fst f g = pullback.fst f' g' ≫ v)
    (hls : l ≫ pullback.snd f g = pullback.snd f' g' ≫ w) :
    let βa := pullbackCompOfEq l (pullback.fst f g) (pullback.fst f' g' ≫ v)
        hlf N ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f' g') v).app N).symm
    let βb := pullbackCompOfEq l (pullback.snd f g) (pullback.snd f' g' ≫ w)
        hls M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f' g') w).app M).symm
    modulesPseudofunctor.overlapPairBaseChangeHom f g p v w f' g' hv hw N M φ =
      βa.inv ≫ (Scheme.Modules.pullback l).map φ ≫ βb.hom := by
  dsimp only
  have hl : l = pullback.lift (pullback.fst f' g' ≫ v) (pullback.snd f' g' ≫ w) (by
      rw [Category.assoc, Category.assoc, hv, hw, ← Category.assoc,
        ← Category.assoc, pullback.condition]) := by
    apply pullback.hom_ext
    · rw [hlf, pullback.lift_fst]
    · rw [hls, pullback.lift_snd]
  subst l
  dsimp only [CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom]
  rw [modulesPseudofunctor_mapComp_inv_app, modulesPseudofunctor_mapComp_hom_app,
    Scheme.Modules.modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]

end
end AlgebraicGeometry
