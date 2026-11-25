/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveDevissage
public import WeilConjectures.CategoryTheory.Triangulated.FullyFaithfulGenerator

/-!
# Full faithfulness on shifted sums

Let `F : D(C) ⥤ D(D)` be an additive functor commuting with the shifts. The property that `F` is
bijective on the morphisms `M ⟶ N` (`CategoryTheory.Functor.HomBijective`) is stable under
isomorphisms, binary biproducts and shifts in both variables, and holds when `M` or `N` is zero.
Hence, if `F` is bijective on the morphisms `X[0] ⟶ Y[0]⟦b⟧` for all objects `X`, `Y` satisfying a
property `R`, it is bijective on the morphisms between shifted sums of objects satisfying `R`
(`DerivedCategory.homBijective_of_isShiftSum`).
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D] [Abelian D]
  [HasDerivedCategory D] {F : DerivedCategory C ⥤ DerivedCategory D} [F.Additive] [F.CommShift ℤ]
  {R : ObjectProperty C}

/-- If `F` is bijective on the morphisms `X[0] ⟶ Y[0]⟦b⟧` for all objects `X`, `Y` satisfying
`R`, then it is bijective on the morphisms between shifted sums of objects satisfying `R`. -/
theorem homBijective_of_isShiftSum
    (hbase : ∀ X Y, R X → R Y → ∀ b : ℤ,
      F.HomBijective ((singleFunctor C 0).obj X)
        ((shiftFunctor _ b).obj ((singleFunctor C 0).obj Y)))
    {M N : DerivedCategory C} (hM : IsShiftSum R M) (hN : IsShiftSum R N) :
    F.HomBijective M N := by
  let Q₂ : ObjectProperty (DerivedCategory C) := fun N' ↦
    ∀ M', IsShiftSum R M' → F.HomBijective M' N'
  have : Q₂.IsClosedUnderIsomorphisms := ⟨fun e h M' hM' ↦ (h M' hM').of_iso_right e⟩
  refine hN.prop Q₂ (fun N' hN' M' _ ↦ .of_isZero_right hN')
    (fun N₁ N₂ h₁ h₂ M' hM' ↦ (h₁ M' hM').biprod_right (h₂ M' hM')) (fun N' n h M' hM' ↦ ?_)
    (fun Y hY M' hM' ↦ ?_) M hM
  · exact ((h _ (hM'.shift (-n))).shift n).of_iso_left
      ((shiftFunctorCompIsoId _ (-n) n (by lia)).app M')
  · let Q₁ : ObjectProperty (DerivedCategory C) := fun M'' ↦
      ∀ b : ℤ, F.HomBijective M'' ((shiftFunctor _ b).obj ((singleFunctor C 0).obj Y))
    have : Q₁.IsClosedUnderIsomorphisms := ⟨fun e h b ↦ (h b).of_iso_left e⟩
    have h := hM'.prop Q₁ (fun _ hM'' _ ↦ .of_isZero_left hM'')
      (fun _ _ h₁ h₂ b ↦ (h₁ b).biprod_left (h₂ b))
      (fun M'' n h b ↦ ((h (b - n)).shift n).of_iso_right
        ((shiftFunctorAdd' _ (b - n) n b (by lia)).app _).symm)
      (fun X hX b ↦ hbase X Y hX hY b)
    exact (h 0).of_iso_right ((shiftFunctorZero _ ℤ).app _)

end DerivedCategory
