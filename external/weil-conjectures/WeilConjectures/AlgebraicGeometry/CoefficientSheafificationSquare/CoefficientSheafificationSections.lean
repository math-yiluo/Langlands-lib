/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationSectionData
public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationScalarSquare

/-! # Section normalization for the constructed coefficient square

(blueprint: lem-weil-pbc-coefficient-sheafification-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare

section CoefficientSquare
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B B' R S : Type (u + 1)} [CommRing B] [CommRing B'] [CommRing R] [CommRing S]
    (q : B →+* B') (b : R →+* B) (b' : S →+* B') (r : R →+* S)
    (h : b'.comp r = q.comp b)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)

private theorem forgetIso_quotient (F : Sheaf J (ModuleCat.{u + 1} B')) :
    (forgetIso J B' S b' U β).hom.app F =
      (forgetIso J B R b T α).hom.app
        ((sheafCompose J
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).obj F) := by
  unfold forgetIso
  rfl

theorem coefficientScalarIso_normalized :
    normalized
      (coefficientScalarIso (J := J) (q := q) (b := b) (b' := b')
        (r := r) (h := h) (a := a) (α := α) (β := β) (ha := ha))
      (restrictForgetIso a) (forgetIso J B' S b' U β) (forgetIso J B R b T α)
      (fixedRestrictForgetIso J q) := by
  apply normalized_of_app
  intro F
  erw [coefficientScalarIso_forget]
  simp only [restrictForgetIso, fixedRestrictForgetIso, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  exact forgetIso_quotient J q b b' α β F

end CoefficientSquare
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
