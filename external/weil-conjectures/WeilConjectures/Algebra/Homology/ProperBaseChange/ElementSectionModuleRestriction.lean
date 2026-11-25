/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom

/-! Restriction of modules along one generalized section. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

-- The module comparisons involve several nested element sites.
set_option maxRecDepth 4000 in
/-- Restriction along a generalized section preserves colimits and the rank-one module.

Source: Stacks Project, Modules on Sites, Tags 04IE and 04IF; Sites, Tag 0791.
(blueprint: lem-weil-pbc-element-section-module-restriction).

Proof: The sheafification adjunction and Yoneda turn t into a map b:H to A,
where H is the sheafified representable at V. Restrict along its element-site
map. The flattening equivalence identifies this restriction followed by a
module equivalence with localization at the fibre sheaf of b. Localization
has the module direct image as right adjoint, so it preserves colimits.
Transfer this property through the comparison and reflect it through the
module equivalence. Then compose with the inverse module equivalence between
the element site of H and C/V. Its unit comparison identifies the rank-one
modules. Relocalization identifies the restriction of elementModulePullback
R A Q with elementModulePullback R H Q; the represented-slice comparison and
the equivalence unit identify this last module with Q.over V. At W to V all
these comparisons evaluate Q at W with the same scalar action. Empty fibres,
empty covers and zero rings satisfy the same formulas. -/
theorem elementSectionModuleRestriction_exists
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (V : C) (t : A.obj.obj (op V)) :
    ∃ G : ringedSiteModules.{u}
        (elementRing ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A) ⥤
      ringedSiteModules.{u} (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V),
      PreservesColimitsOfSize.{u, u} G ∧
      Nonempty (unit (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V) ≅
        G.obj (unit (elementRing
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A))) ∧
      ∀ Q : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        Nonempty (G.obj ((elementModulePullback
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A).obj Q) ≅ Q.over V) := by
  let H := (presheafToSheaf J (Type u)).obj (yoneda.obj V)
  let b : H ⟶ A := ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj V) A).symm
    (yonedaEquiv.symm t)
  obtain ⟨E₀, ⟨k⟩⟩ := CategoryTheory.ordinarySliceComparison R V
  let L := elementModulePullbackOver (localCoefficientRings R) b
    (presentationElementRestriction_continuous b)
  obtain ⟨E, ⟨q⟩⟩ := CategoryTheory.flattenRestrictionEquivalence R b
  obtain ⟨s⟩ := ringed_sheaf_slice_adjunction
    (localCoefficientRings (presentationElementRing R A)) (CategoryTheory.fibreSheaf b)
  have : PreservesColimitsOfSize.{u, u}
      (elementModulePullback (localCoefficientRings (presentationElementRing R A))
        (CategoryTheory.fibreSheaf b)) := by
    rw [← s.pullback_eq]
    exact s.localization_modules.leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{u, u} (L ⋙ E.functor) :=
    preservesColimits_of_natIso q.symm
  let : PreservesColimitsOfSize.{u, u} L :=
    preservesColimits_of_reflects_of_preserves L E.functor
  let G := L ⋙ E₀.modules.inverse
  refine ⟨G, inferInstance,
    ⟨(E₀.modules.inverse.mapIso E₀.forwardUnit.symm ≪≫
      E₀.modules.unitIso.symm.app _).symm⟩, ?_⟩
  intro Q
  obtain ⟨p⟩ := presentationElementRestriction_relocalization R b
    (presentationElementRestriction_continuous b)
  exact ⟨E₀.modules.inverse.mapIso (p.app Q) ≪≫
    E₀.modules.inverse.mapIso (k.app Q).symm ≪≫ E₀.modules.unitIso.symm.app _⟩

end SheafOfModules
