/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationSeed

/-! # Scalar restriction commutes with module sheafification

Forgetting the extended unit gives an identity, hence reflects its invertibility.
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

theorem rawMap_isIso
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))) :
    IsIso (rawMap J r a α β ha P) := by
  have : IsIso ((SheafOfModules.toSheaf T).map (rawMap J r a α β ha P)) := by
    rw [rawMap_forget]
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf T)

theorem rawMap_naturality
    {P Q : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))}
    (f : P ⟶ Q) :
    (PresheafOfModules.sheafification α).map ((rawRestriction r).map f) ≫
        rawMap J r a α β ha Q =
      rawMap J r a α β ha P ≫ (SheafOfModules.restrictScalars a).map
        ((PresheafOfModules.sheafification β).map f) := by
  apply (SheafOfModules.toSheaf T).map_injective
  simp only [Functor.map_comp, rawMap_forget]
  rfl

include ha in
@[irreducible] def rawIso :
    rawRestriction r ⋙ PresheafOfModules.sheafification α ≅
      PresheafOfModules.sheafification β ⋙ SheafOfModules.restrictScalars a :=
  NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (rawMap J r a α β ha P)
    (rawMap_isIso J r a α β ha P)) (fun f ↦ rawMap_naturality J r a α β ha f)

end
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
