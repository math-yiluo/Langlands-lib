/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Tensor products of free sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. Tensoring with a sheaf of modules is
additive in each variable, being a left adjoint (`SheafOfModules.tensorHomAdjunction`). Hence the
tensor product of the free sheaves of modules on finite types `I` and `I'` is the free sheaf of
modules on `Σ _ : I, I'` (`SheafOfModules.freeTensorFreeIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

section Additive

variable (A : SheafOfModules.{u} 𝓡)

instance : (tensorLeft A).Additive := by
  have := (tensorHomAdjunction R A).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
    (tensorHomAdjunction R A).leftAdjoint_preservesColimits
  have : HasBinaryBiproducts (SheafOfModules.{u} 𝓡) := HasBinaryBiproducts.of_hasBinaryProducts
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance : (tensorRight A).Additive :=
  Functor.additive_of_iso (F := tensorLeft A)
    (NatIso.ofComponents (fun X ↦ β_ A X) fun f ↦ BraidedCategory.braiding_naturality_right A f)

instance hasFiniteBiproducts : HasFiniteBiproducts (SheafOfModules.{u} 𝓡) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The tensor product of finite free modules.** The tensor product of the free sheaves of
modules on finite types `I` and `I'` is the free sheaf of modules on `Σ _ : I, I'`: tensoring is
additive in each variable, so it distributes over the finite biproducts `free I ≅ ⨁_I R`. -/
noncomputable def freeTensorFreeIso (I I' : Type u) [Finite I] [Finite I'] :
    free (R := 𝓡) I ⊗ free I' ≅ free (Σ _ : I, I') :=
  ((biproduct.isoCoproduct fun _ : I ↦ unit 𝓡).symm ⊗ᵢ Iso.refl _) ≪≫
    (tensorRight (free I')).mapBiproduct (fun _ : I ↦ unit 𝓡) ≪≫
    biproduct.mapIso (fun _ ↦ λ_ (free I') ≪≫ (biproduct.isoCoproduct _).symm) ≪≫
    biproductBiproductIso (fun _ : I ↦ I') (fun _ _ ↦ unit 𝓡) ≪≫
    biproduct.isoCoproduct _

end Additive

end SheafOfModules
