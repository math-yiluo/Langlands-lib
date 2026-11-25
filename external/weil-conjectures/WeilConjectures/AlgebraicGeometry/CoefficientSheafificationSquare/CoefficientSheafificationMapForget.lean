/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationForget

/-! # The forgetful formula after a module-presheaf map

(blueprint: lem-weil-pbc-coefficient-sheafification-map-forget).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
section
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (r : R →+* S)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)

theorem rawIso_map_forget
    {P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of R))}
    {Q : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))}
    (p : P ⟶ (rawRestriction r).obj Q) :
    (SheafOfModules.toSheaf T).map
        ((PresheafOfModules.sheafification α).map p ≫ (rawIso J r a α β ha).hom.app Q) =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).map
        ((PresheafOfModules.toPresheaf _).map p) := by
  rw [Functor.map_comp, rawIso_forget]
  erw [Category.comp_id]
  rfl

end
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
