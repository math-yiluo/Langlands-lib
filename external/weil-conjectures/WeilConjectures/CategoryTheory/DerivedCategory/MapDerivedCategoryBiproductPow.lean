/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Biproduct powers on derived categories

For an abelian category `C` and `d : ℕ`, the exact functor `Functor.finBiproductPow C d`,
`M ↦ Mᵈ`, induces on the derived category the biproduct power `K ↦ Kᵈ`
(`CategoryTheory.Functor.mapDerivedCategoryBiproductPowIso`). This follows from two facts:

* the biproduct power is additive (`CategoryTheory.Functor.additive_biproductPow`), and an
  additive functor commutes with biproduct powers (`CategoryTheory.Functor.biproductPowCompIso`);
* on complexes, the levelwise biproduct power is the biproduct power of complexes
  (`CategoryTheory.Functor.mapHomologicalComplexBiproductPowIso`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Additive

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [HasFiniteBiproducts A] [HasFiniteBiproducts B]

/-- The biproduct power functor `X ↦ Xᵈ` is additive. It is not an instance, the functor
`Functor.finBiproductPow` being defined elsewhere. -/
lemma additive_biproductPow (d : ℕ) : (finBiproductPow A d).Additive where
  map_add {_ _ f g} := biproduct.hom_ext _ _ fun j ↦ by simp

/-- An additive functor `G` commutes with biproduct powers: `G (Xᵈ) ≅ (G X)ᵈ`, naturally in
`X`. -/
noncomputable def biproductPowCompIso (G : A ⥤ B) [G.Additive] (d : ℕ) :
    finBiproductPow A d ⋙ G ≅ G ⋙ finBiproductPow B d :=
  NatIso.ofComponents (fun X ↦ G.mapBiproduct fun _ : Fin d ↦ X) fun f ↦ by
    refine biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [Functor.comp_map, finBiproductPow_map, Functor.mapBiproduct_hom, Category.assoc,
      biproduct.lift_π, biproduct.lift_π_assoc, biproduct.map_π, ← Functor.map_comp]

end Additive

section HomologicalComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
  {ι : Type*} (c : ComplexShape ι) [HasFiniteBiproducts (HomologicalComplex C c)] (d : ℕ)
  [(finBiproductPow C d).Additive]

/-- The levelwise biproduct power `(K.X n)ᵈ` of a complex `K` is the biproduct power `Kᵈ` of
complexes. -/
noncomputable def mapHomologicalComplexBiproductPowIso :
    (finBiproductPow C d).mapHomologicalComplex c ≅ finBiproductPow (HomologicalComplex C c) d :=
  NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((HomologicalComplex.eval C c n).mapBiproduct fun _ : Fin d ↦ K).symm) (by
      intro i j _
      refine biproduct.hom_ext' _ _ fun k ↦ ?_
      simp only [Functor.mapHomologicalComplex_obj_d, finBiproductPow_map, Iso.symm_hom,
        Functor.mapBiproduct_inv, biproduct.ι_map_assoc, biproduct.ι_desc,
        biproduct.ι_desc_assoc, HomologicalComplex.eval_map]
      exact (biproduct.ι (fun _ : Fin d ↦ K) k).comm i j)) (by
    intro K L f
    ext n : 1
    refine biproduct.hom_ext' _ _ fun k ↦ ?_
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, finBiproductPow_map,
      HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom, Functor.mapBiproduct_inv,
      biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc, HomologicalComplex.eval_map]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, biproduct.ι_map])

end HomologicalComplex

section Derived

variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C] [HasDerivedCategory C]
  (d : ℕ)
  [(finBiproductPow C d).Additive] [PreservesFiniteLimits (finBiproductPow C d)]
  [PreservesFiniteColimits (finBiproductPow C d)]

/-- The functor induced on the derived category by the exact functor `M ↦ Mᵈ` is the biproduct
power `K ↦ Kᵈ`. -/
noncomputable def mapDerivedCategoryBiproductPowIso :
    (finBiproductPow C d).mapDerivedCategory ≅ finBiproductPow (DerivedCategory C) d :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((finBiproductPow C d).mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    (DerivedCategory.Q ⋙ finBiproductPow _ d) _ _ <|
    haveI : HasFiniteBiproducts (CochainComplex C ℤ) := .of_hasFiniteProducts
    (isoWhiskerRight (mapHomologicalComplexBiproductPowIso C _ d) _ ≪≫
      biproductPowCompIso DerivedCategory.Q d)

end Derived

end CategoryTheory.Functor
