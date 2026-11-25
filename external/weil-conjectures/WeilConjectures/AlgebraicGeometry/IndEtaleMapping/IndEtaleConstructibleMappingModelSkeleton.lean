/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleConstructibleMappingContinuityData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Skeletons for compatible ind-etale model maps

Source: Bhatt--Scholze 6.3.16, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-model-skeleton).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.IndEtaleMapping
variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)
variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)
variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)
variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

/-- The simultaneous strict representative construction, with the geometric cone
square omitted. The omitted field is exactly the separately supplied equation
`hv`; all chain-level normalization fields remain part of the skeleton.
Source: Bhatt--Scholze 6.3.16, proof Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-model-skeleton).
-/
theorem compatible_model_map_skeleton_exists [Finite A] [IsAffine X] [IsNoetherian X]
    [IsCofiltered I] [IsCofiltered J]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (hd : IsLimit ((Over.forget X).mapCone d))
    (haffineD : ∀ i : I, IsAffine (D.obj i).left)
    (haffineE : ∀ j : J, IsAffine (E.obj j).left)
    (hetaleD : ∀ i : I, Etale (D.obj i).hom)
    (hetaleE : ∀ j : J, Etale (E.obj j).hom)
    (hfpD : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (hfpE : ∀ j : J, LocallyOfFinitePresentation (E.obj j).hom)
    (htransitionD : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (htransitionE : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (E.map f).left)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hK' : DerivedCategory.isBoundedConstructible A X K')
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (hTor' : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K')
    (hM : ∃ a : ℤ, M.IsGE a) (hM' : ∃ a : ℤ, M'.IsGE a)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt)
    (hv : ∀ j : J, v ≫ c.π.app (r.obj j) = d.π.app j ≫ η.app j) :
    ∃ (P : Model A K M D c) (Q : Model A K' M' E d),
      Nonempty (ModelMapSkeleton A K M D c E d r K' M' α β P Q η v) := by
  sorry

end AlgebraicGeometry.Etale.IndEtaleMapping
