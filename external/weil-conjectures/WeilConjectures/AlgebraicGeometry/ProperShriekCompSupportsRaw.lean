/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-! Raw proper compositor compatibility after canonicalizing the composite.
Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

omit [Finite A] in
private theorem proper_forget_eq {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsProper q] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom =
      compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q) := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

private theorem comparison_forget {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsProper q]
    (c : Compactification q) (E : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekIso A c).hom.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification q)).app E =
      (compactificationForgetSupports (ModuleCat.{u + 1} A) c).app E := by
  exact rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar A
    c (HasCompactification.compactification q) E

private theorem comparison_inv_forget {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsProper q]
    (c : Compactification q) (E : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekIso A c).inv.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) c).app E =
      (compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q)).app E := by
  rw [← comparison_forget A q c E, Iso.inv_hom_id_app_assoc]

/--
The compact-support composition isomorphism for `p` and `f`, followed by the
canonical proper comparison for `p ≫ f`, equals the ordinary composition path.
This is the compositor calculation after the equality-congruence part has been
removed.  It is strictly simpler than the route statement because the target
map is the definitional composite `p ≫ f` and no extra morphism-equality
transport is present.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first supported coordinate extraction before a trace.
-/
theorem properShriekComp_comp_forgetSupports_raw {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S)
    [IsProper p] [IsProper f] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIso A p f).inv.app E ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) (p ≫ f)).hom.app E =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar
            (ModuleCat.{u + 1} A) p).hom.app E) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) f).hom.app
            ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  rw [proper_forget_eq A p, proper_forget_eq A f, proper_forget_eq A (p ≫ f)]
  let d := HasCompactification.compactification f
  let e := (HasCompactification.compactification (p ≫ f)).ofComp d
  have hcomp := properShriekComp_compactificationForgetSupports A p f d e E
  have hα := comparison_forget A (p ≫ f) (d.comp e) E
  have hβ := comparison_inv_forget A p e.restrict E
  simp only [rightDerivedLowerShriekCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [hα, hcomp, ← Functor.map_comp_assoc, hβ]
  rfl

end AlgebraicGeometry.Etale
