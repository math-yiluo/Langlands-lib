/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN
import WeilConjectures.AlgebraicGeometry.TensorPowerOpenRestrictionAddition
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem numerator_inv_tmul {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (F L : X.Modules) (n : ℕ) (V : Y.Opens)
    (z : Γ(F.restrict j, V)) (w : Γ((L.restrict j).tensorPow n, V)) :
    ((F ⊗ L.tensorPow n).restrictAppIso j V).hom
        ((openRestrictionNumeratorIso j F L n).inv.app V (tmulSection z w)) =
      tmulSection ((F.restrictAppIso j V).hom z)
        (((L.tensorPow n).restrictAppIso j V).hom
          ((openRestrictionTensorPowIso j L n).inv.app V w)) := by
  rw [openRestrictionNumeratorIso, Iso.trans_inv, Hom.comp_app,
    ConcreteCategory.comp_apply, tensorIso_inv, tensorHom_app_tmulSection,
    Iso.refl_inv, Hom.id_app, ConcreteCategory.id_apply, openRestrictionTensorIso]
  exact Classical.choose_spec (exists_restriction_tensor_comparison j F (L.tensorPow n))
    V z ((openRestrictionTensorPowIso j L n).inv.app V w)

/-- The canonical numerator comparisons intertwine the transition morphisms as sheaf maps.
Source: Stacks Project, Modules, Tag 01CD; Properties, Tag 01PW, restriction paragraph.
(blueprint: lem-sc-tensor-power-section-open-restriction-T).

Proof: The inverse tensor comparison is uniquely characterized on all pure tensor
sections. Apply the sheaf tensor universal property to prove its naturality, associator
and unitor coherence: both composites carry a pure tensor to the same ambient tensor,
by tensorHom_app_tmulSection, associator_hom_app_tmulSection and the unitor formulas.
Induct on the first exponent in tensorPowAddIso. The zero case uses the unit comparison
and left unitor; the successor uses the recursive tensor comparison and associator.
This proves compatibility of the recursive power comparisons with tensorPowAddIso.
The section-power compatibility is openRestrictionTensorPowIso_inv_section. Expand
mulTensorPowSection into the inverse right unitor, tensoring with tensorPowSection,
the associator, and the inverse tensorPowAddIso. The previous compatibilities give the
displayed equality. The section-power comparison determines the section morphism since
homOfGlobalSection is determined by its value on 1. Equality is of sheaf morphisms;
there is no assumption that arbitrary sections are pure tensors. -/
theorem openRestrictionNumeratorIso_mul (X : Scheme.{u}) (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) (n b : ℕ) :
    let sU : Γ(L.restrict U.ι, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    (restrictFunctor U.ι).map (mulTensorPowSection (homOfGlobalSection L s) F n b) ≫
        (openRestrictionNumeratorIso U.ι F L (n + b)).hom =
      (openRestrictionNumeratorIso U.ι F L n).hom ≫
        mulTensorPowSection (homOfGlobalSection (L.restrict U.ι) sU)
          (F.restrict U.ι) n b := by
  dsimp only
  let sU : Γ(L.restrict U.ι, ⊤) :=
    (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
  apply (cancel_epi (openRestrictionNumeratorIso U.ι F L n).inv).mp
  apply (cancel_mono (openRestrictionNumeratorIso U.ι F L (n + b)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  -- Use the public adjunction and sectionwise tensor extensionality directly.
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification
    (F.restrict U.ι) ((L.restrict U.ι).tensorPow n)).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction
    (𝟙 U.toScheme.ringCatSheaf.obj)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro Vop
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro z w
  let V : U.toScheme.Opens := Vop.unop
  change ((openRestrictionNumeratorIso U.ι F L n).inv ≫
    (restrictFunctor U.ι).map (mulTensorPowSection (homOfGlobalSection L s) F n b)).app V
      (tmulSection z w) =
    (mulTensorPowSection (homOfGlobalSection (L.restrict U.ι) sU)
      (F.restrict U.ι) n b ≫
      (openRestrictionNumeratorIso U.ι F L (n + b)).inv).app V (tmulSection z w)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  change (mulTensorPowSection (homOfGlobalSection L s) F n b).app (U.ι ''ᵁ V)
      (((F ⊗ L.tensorPow n).restrictAppIso U.ι V).hom
        ((openRestrictionNumeratorIso U.ι F L n).inv.app V (tmulSection z w))) = _
  rw [numerator_inv_tmul, mulTensorPowSection_app, associator_hom_app_tmulSection,
    whiskerLeft_app_tmulSection]
  rw [mulTensorPowSection_app, associator_hom_app_tmulSection,
    whiskerLeft_app_tmulSection]
  rw [show (openRestrictionNumeratorIso U.ι F L (n + b)).inv.app V
      (tmulSection z
        (((L.restrict U.ι).tensorPowAddIso n b).inv.app V
          (tmulSection w (tensorPowSectionOne
            (homOfGlobalSection (L.restrict U.ι) sU) b V)))) = _
    from numerator_inv_tmul U.ι F L (n + b) V z _]
  rw [openRestrictionTensorPowIso_inv_add, openRestrictionTensorPowIso_inv_section]

end AlgebraicGeometry.Scheme.Modules
