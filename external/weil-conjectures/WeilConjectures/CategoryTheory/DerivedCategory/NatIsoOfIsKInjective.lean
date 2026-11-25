/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Natural isomorphisms out of a derived category, from K-injective complexes

Let `C` be an abelian category with K-injective resolutions. Every object of the derived category
`D(C)` is the image of a K-injective complex, and every morphism between images of K-injective
complexes is the image of a morphism of complexes. Hence a natural isomorphism between two
functors `F G : D(C) ⥤ E` is given by isomorphisms `F (Q I) ≅ G (Q I)` for the K-injective
complexes `I`, natural with respect to the morphisms of complexes between them
(`DerivedCategory.natIsoOfIsKInjective`).
-/

@[expose] public section

open CategoryTheory Abelian

namespace DerivedCategory

variable {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] [Category E]

/-- A natural isomorphism between functors out of the derived category `D(C)`, from isomorphisms
`F (Q I) ≅ G (Q I)` for the K-injective complexes `I` which are natural with respect to the
morphisms of complexes. The component at an object `Z` is transported along the K-injective
representative `Z ≅ Q (kInjectiveRep Z)`. -/
noncomputable def natIsoOfIsKInjective (F G : DerivedCategory C ⥤ E)
    (e : ∀ (I : CochainComplex C ℤ) [I.IsKInjective], F.obj (Q.obj I) ≅ G.obj (Q.obj I))
    (he : ∀ (I I' : CochainComplex C ℤ) [I.IsKInjective] [I'.IsKInjective] (g : I ⟶ I'),
      F.map (Q.map g) ≫ (e I').hom = (e I).hom ≫ G.map (Q.map g)) :
    F ≅ G :=
  NatIso.ofComponents
    (fun Z ↦ F.mapIso (kInjectiveRepIso Z) ≪≫ e (kInjectiveRep Z) ≪≫
      G.mapIso (kInjectiveRepIso Z).symm)
    (fun {Z Z'} φ ↦ by
      obtain ⟨g, hg⟩ := CochainComplex.IsKInjective.exists_Q_map_eq _ _
        ((kInjectiveRepIso Z).inv ≫ φ ≫ (kInjectiveRepIso Z').hom)
      have hφ : φ = (kInjectiveRepIso Z).hom ≫ Q.map g ≫ (kInjectiveRepIso Z').inv := by
        rw [hg]
        simp
      subst hφ
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Category.assoc]
      rw [← F.map_comp_assoc (kInjectiveRepIso Z').inv, Iso.inv_hom_id, F.map_id,
        Category.id_comp, reassoc_of% (he _ _ g), ← G.map_comp_assoc (kInjectiveRepIso Z).inv,
        Iso.inv_hom_id, G.map_id, Category.id_comp])

lemma natIsoOfIsKInjective_hom_app (F G : DerivedCategory C ⥤ E)
    (e : ∀ (I : CochainComplex C ℤ) [I.IsKInjective], F.obj (Q.obj I) ≅ G.obj (Q.obj I))
    (he : ∀ (I I' : CochainComplex C ℤ) [I.IsKInjective] [I'.IsKInjective] (g : I ⟶ I'),
      F.map (Q.map g) ≫ (e I').hom = (e I).hom ≫ G.map (Q.map g)) (Z : DerivedCategory C) :
    (natIsoOfIsKInjective F G e he).hom.app Z =
      F.map (kInjectiveRepIso Z).hom ≫ (e (kInjectiveRep Z)).hom ≫
        G.map (kInjectiveRepIso Z).inv :=
  rfl

end DerivedCategory
