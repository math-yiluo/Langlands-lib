/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.CokernelBiproduct
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct

/-!
# Cokernels of morphisms between finite sums of the unit are dualizable

Let `C` be a monoidal preadditive category with finite biproducts and cokernels, whose tensor
product is additive in each variable. A finite biproduct of copies of the unit `𝟙_ C` has a right
dual (`CategoryTheory.IsFiniteBiproductOf.nonempty_hasRightDual`). If moreover the nonzero
endomorphisms of `𝟙_ C` are isomorphisms (the endomorphisms of the unit form a division ring, as
for the module objects over a field), then the cokernel of any morphism
`⨁_κ 𝟙_ C ⟶ ⨁_ι 𝟙_ C` is again a finite biproduct of copies of `𝟙_ C`, hence has a right dual
(`CategoryTheory.nonempty_hasRightDual_cokernel_of_isIso`): finitely presented modules over a
field are free of finite rank, hence dualizable.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- A finite biproduct of copies of the unit has a right dual, the biproduct of the duals. -/
lemma Limits.IsFiniteBiproductOf.nonempty_hasRightDual {M : C}
    (h : IsFiniteBiproductOf (𝟙_ C) M) : Nonempty (HasRightDual M) := by
  obtain ⟨ι, _, ⟨e⟩⟩ := h
  obtain ⟨d⟩ := Bicone.nonempty_hasRightDual_pt (biproduct.isBilimit fun _ : ι ↦ 𝟙_ C)
    fun _ ↦ ⟨inferInstance⟩
  exact ⟨{ rightDual := (⨁ fun _ : ι ↦ 𝟙_ C)ᘁ, exact := exactPairingCongrLeft e }⟩

/-- If the nonzero endomorphisms of the unit are isomorphisms, the cokernel of a morphism
`⨁_κ 𝟙_ C ⟶ ⨁_ι 𝟙_ C` between finite biproducts of copies of the unit has a right dual: it is
itself a finite biproduct of copies of the unit (`Limits.isFiniteBiproductOf_cokernel`). -/
theorem nonempty_hasRightDual_cokernel_of_isIso [HasCokernels C]
    (h : ∀ g : 𝟙_ C ⟶ 𝟙_ C, g ≠ 0 → IsIso g) {κ ι : Type} [Finite κ] [Finite ι]
    (f : (⨁ fun _ : κ ↦ 𝟙_ C) ⟶ ⨁ fun _ : ι ↦ 𝟙_ C) : Nonempty (HasRightDual (cokernel f)) :=
  (isFiniteBiproductOf_cokernel h f).nonempty_hasRightDual

end CategoryTheory
