/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenCounitSectionLifting

/-!
# Open counit diagrams after localization

## References

* Stacks Project, Tag 09AE
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale
open Scheme

private theorem adjunction_counit_factor
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {G H K : D} (c : K ⟶ H) [IsIso (R.map c)] (b : G ⟶ H) :
    ∃ a : L.obj (R.obj G) ⟶ K, a ≫ c = adj.counit.app G ≫ b := by
  refine ⟨L.map (R.map b ≫ inv (R.map c)) ≫ adj.counit.app K, ?_⟩
  have hc : L.map (R.map c) ≫ adj.counit.app H = adj.counit.app K ≫ c :=
    adj.counit.naturality c
  rw [Category.assoc, ← hc, ← Category.assoc, ← L.map_comp]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact adj.counit.naturality b

/-- A map into a localized sheaf induces a commuting diagram of open counits
whenever the smaller open maps into the larger one. -/
theorem openCounit_localization_diagram (R : Type (u + 1)) [Ring R]
    {W T : Scheme.{u}} (i : W ⟶ T) [IsOpenImmersion i]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R)) (Q : T.ProEt)
    (O : Q.left.Opens) (hO : (O : Set Q.left) ⊆ Q.hom ⁻¹' Set.range i)
    (G : Sheaf (ProEt.topology Q.left) (ModuleCat.{u + 1} R))
    (b : G ⟶ (localizationRestriction (ModuleCat.{u + 1} R) Q.hom Q.prop).obj F) :
    ∃ a : (openImmersionLowerShriek (ModuleCat.{u + 1} R) O.ι).obj
      ((openImmersionRestriction (ModuleCat.{u + 1} R) O.ι).obj G) ⟶
        (localizationRestriction (ModuleCat.{u + 1} R) Q.hom Q.prop).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) i).obj
            ((openImmersionRestriction (ModuleCat.{u + 1} R) i).obj F)),
      a ≫ (localizationRestriction (ModuleCat.{u + 1} R) Q.hom Q.prop).map
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) i).counit.app F) =
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) O.ι).counit.app G ≫ b := by
  let c := (localizationRestriction (ModuleCat.{u + 1} R) Q.hom Q.prop).map
    ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) i).counit.app F)
  have hc : IsIso ((openImmersionRestriction (ModuleCat.{u + 1} R) O.ι).map c) := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
    intro Z
    let Z' : T.ProEt := ProEt.mk ((Z.unop.hom ≫ O.ι) ≫ Q.hom)
    change IsIso
      (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) i).counit.app F).hom.app
        (op Z'))
    apply isIso_openCounit_app_of_factors R i F Z'
    refine ⟨IsOpenImmersion.lift i Z'.hom ?_, IsOpenImmersion.lift_fac i Z'.hom _⟩
    rintro _ ⟨z, rfl⟩
    exact hO (Subtype.mem ((Z.unop.hom) z))
  exact adjunction_counit_factor
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) O.ι) c b

end AlgebraicGeometry.ProEtale
