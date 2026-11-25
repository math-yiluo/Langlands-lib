/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation

/-! # Fixed scalar comparisons commute with constant and slice units -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
attribute [local irreducible] AlgebraicGeometry.Scheme.directCoefficientMap
  AlgebraicGeometry.Scheme.overDirectMap
  AlgebraicGeometry.Scheme.directCoefficientIso AlgebraicGeometry.Scheme.overDirectIso
  AlgebraicGeometry.Scheme.constantAssociatedIso

namespace AlgebraicGeometry.Scheme
section
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
  {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B D : Type (t + 1)} [CommRing B] [CommRing D]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} D)]
  {R S : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  (β : (Functor.const Cᵒᵖ).obj (RingCat.of D) ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  (q : B →+* D) (p : R ⟶ S)
  (h : ∀ Z, α.app Z ≫ p.hom.app Z = RingCat.ofHom q ≫ β.app Z)

private lemma constantAssociatedIso_coefficient (N : ModuleCat.{t + 1} D) :
    (directCoefficientIso α β q p h).hom.app N ≫
      (SheafOfModules.restrictScalars p).map ((constantAssociatedIso β).hom.app N) =
    (constantAssociatedIso α).hom.app ((ModuleCat.restrictScalars q).obj N) ≫
      (finitePerfectAdicAssociated α).map
        ((constantCommuteCompose J (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
      (finitePerfectAdicAssociatedCoherence α β q p h).hom.app
        ((constantSheaf J (ModuleCat.{t + 1} D)).obj N) := by
  let U := ModuleCat.restrictScalars.{t + 1} q
  let γ := constantCommuteCompose J U
  have hunit : toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) ≫ (γ.inv.app N).hom =
      whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N)) U := by
    have hh : whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N)) U ≫
        (γ.hom.app N).hom = toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)) := by
      rw [constantCommuteCompose_hom_app_hom]
      change whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N)) U ≫
        ((sheafifyComposeIso J U ((Functor.const Cᵒᵖ).obj N)).inv ≫
          sheafifyMap J (𝟙 _)) = _
      erw [sheafComposeIso_inv_fac_assoc, sheafifyMap_id, Category.comp_id]
      rfl
    rw [← hh, Category.assoc]
    have hi := congrArg (fun f ↦ f.hom) (γ.hom_inv_id_app N)
    change (γ.hom.app N).hom ≫ (γ.inv.app N).hom = 𝟙 _ at hi
    erw [hi, Category.comp_id]
  erw [directCoefficientIso_hom_app]
  apply (SheafOfModules.toSheaf R).map_injective
  simp only [Functor.map_comp]
  change (SheafOfModules.toSheaf R).map (directCoefficientMap α β q p h N) ≫
      (SheafOfModules.toSheaf S).map ((constantAssociatedIso β).hom.app N) =
    (SheafOfModules.toSheaf R).map ((constantAssociatedIso α).hom.app (U.obj N)) ≫
      (SheafOfModules.toSheaf R).map ((finitePerfectAdicAssociated α).map (γ.inv.app N)) ≫
      (SheafOfModules.toSheaf R).map
        ((finitePerfectAdicAssociatedCoherence α β q p h).hom.app
          ((constantSheaf J (ModuleCat.{t + 1} D)).obj N))
  erw [directCoefficientMap_underlying α β q p h N, Category.id_comp,
    associatedCoefficient_underlying α β q p h
      ((constantSheaf J (ModuleCat.{t + 1} D)).obj N), Category.comp_id,
    constantAssociatedIso_underlying β N, constantAssociatedIso_underlying α (U.obj N)]
  change (presheafToSheaf J AddCommGrpCat.{t + 1}).map
      (whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj N))
        (forget₂ (ModuleCat.{t + 1} D) AddCommGrpCat.{t + 1})) =
    (presheafToSheaf J AddCommGrpCat.{t + 1}).map
      (whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj N)))
        (forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1})) ≫
      (presheafToSheaf J AddCommGrpCat.{t + 1}).map
        (whiskerRight (γ.inv.app N).hom
          (forget₂ (ModuleCat.{t + 1} B) AddCommGrpCat.{t + 1}))
  erw [← Functor.map_comp, ← Functor.whiskerRight_comp, hunit]
  rfl

end
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
