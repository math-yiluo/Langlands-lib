/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration

/-!
# Right adjoints on a localizing closure and representing objects in `P`

Let `P` be a property of objects of a pretriangulated category `C`, stable under shifts, and
`Loc(P)` its localizing closure. The objects of `P` detect isomorphisms of `Loc(P)`
(`CategoryTheory.ObjectProperty.isIso_of_bijective_localizingClosure`): a morphism `g` of
`Loc(P)` such that composition with `g` is bijective on morphisms out of the objects of `P` is an
isomorphism.

Consequently, if `F : Loc(P) ⥤ D` has a right adjoint `G`, the value `G N` is determined by the
functor `A ↦ Hom(F A, N)` on the objects `A` of `P` alone: if a morphism `ε : F T ⟶ N` induces
bijections `Hom(A, T) ≃ Hom(F A, N)` for all `A` in `P`, then its adjunct `T ⟶ G N` is an
isomorphism (`CategoryTheory.ObjectProperty.isIso_homEquiv_of_bijective_localizingClosure`). This
is how one shows that a right adjoint on `Loc(P)` restricts to a right adjoint on `P`: if the
restriction of `F` to `P` has a right adjoint `G'`, then `G N ≅ G' N` for `N` in the image.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {P : ObjectProperty C}
  [P.IsStableUnderShift ℤ]

/-- The objects of `P` detect isomorphisms of `Loc(P)`: if composition with a morphism
`g : X ⟶ Y` of `Loc(P)` is bijective on morphisms out of each object of `P`, then `g` is an
isomorphism. -/
lemma isIso_of_bijective_localizingClosure {X Y : P.localizingClosure.FullSubcategory}
    (g : X ⟶ Y)
    (hg : ∀ A : P.localizingClosure.FullSubcategory, P A.obj →
      Function.Bijective (fun f : A ⟶ X ↦ f ≫ g)) :
    IsIso g := by
  obtain ⟨Z, p, δ, hT⟩ := distinguished_cocone_triangle g
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_forall_eq_zero_localizingClosure _ fun A hA f ↦ ?_)
  let A' : P.localizingClosure.FullSubcategory :=
    ⟨A.obj⟦(-1 : ℤ)⟧, P.localizingClosure.le_shift (-1) _ A.2⟩
  let e : A' ≅ A⟦(-1 : ℤ)⟧ := (fullyFaithfulι _).preimageIso
    ((P.localizingClosure.ι.commShiftIso (-1 : ℤ)).app A).symm
  have h₁ : f ≫ δ = 0 := by
    refine BrownRepresentability.eq_zero_of_comp_shift_eq_zero e g
      (fun f' hf' ↦ (hg A' (P.le_shift (-1) _ hA)).1 ?_) _ ?_
    · simpa using hf'
    · have : δ ≫ g⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      exact (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) this).trans comp_zero)
  obtain ⟨f', rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
  obtain ⟨f'', rfl⟩ := (hg _ hA).2 f'
  have : g ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  exact (Category.assoc _ _ _).trans ((congrArg (f'' ≫ ·) this).trans comp_zero)

/-- Let `F : Loc(P) ⥤ D` be left adjoint to `G`. If a morphism `ε : F T ⟶ N` induces bijections
`Hom(A, T) ≃ Hom(F A, N)`, `f ↦ F f ≫ ε`, for all objects `A` of `P`, then its adjunct
`T ⟶ G N` is an isomorphism.

For `f : A ⟶ T` the two composites
```
F A --F f--> F T --ε--> N        A --f--> T --adj.homEquiv ε--> G N
```
correspond under `adj.homEquiv A N`: the adjunct of `F f ≫ ε` is `f ≫ adj.homEquiv ε`, so
composition with `adj.homEquiv ε` is bijective on `Hom(A, T)` and
`isIso_of_bijective_localizingClosure` applies. -/
lemma isIso_homEquiv_of_bijective_localizingClosure {D : Type u'} [Category* D]
    {F : P.localizingClosure.FullSubcategory ⥤ D} {G : D ⥤ P.localizingClosure.FullSubcategory}
    (adj : F ⊣ G) {T : P.localizingClosure.FullSubcategory} {N : D} (ε : F.obj T ⟶ N)
    (h : ∀ A : P.localizingClosure.FullSubcategory, P A.obj →
      Function.Bijective (fun f : A ⟶ T ↦ F.map f ≫ ε)) :
    IsIso (adj.homEquiv T N ε) := by
  refine isIso_of_bijective_localizingClosure _ fun A hA ↦ ?_
  have : (fun f : A ⟶ T ↦ f ≫ adj.homEquiv T N ε) =
      adj.homEquiv A N ∘ fun f : A ⟶ T ↦ F.map f ≫ ε := by
    ext f
    simp [Adjunction.homEquiv_naturality_left]
  rw [this]
  exact (adj.homEquiv A N).bijective.comp (h A hA)

end CategoryTheory.ObjectProperty
