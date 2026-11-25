/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses

/-!
# Hypercohomology of the sheaf Hom complex and the homotopy category

Source: Stacks Project, Tags 0A8Z and 08JA.
(blueprint: lem-pur-hom-complex-hypercohomology)

This is the independent-universe comparison used by the global-sections theorem.  Its
proof applies zeroth homology to the recorded full derived-sections comparison and
composes with the ordinary global Hom-complex calculation.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

-- The comparison expands several derived-functor and full-subcategory composites.
set_option backward.isDefEq.respectTransparency false in
/-- Zeroth hypercohomology of the Hom complex is the homotopy-category Hom bifunctor.

Proof: lift the target functor I to the full subcategory of K-injective complexes.
The first two comparisons of derived_internalHom_sections_model identify derived
sections of the sheaf Hom complex with its ordinary sections complex after localization.
Apply zeroth derived homology and homologyFunctorFactors, then compose with the ordinary
global Hom-complex calculation. Whiskering retains naturality in both variables.
No K-flatness of the source is required; zero complexes and the empty site are included.

Source: Stacks Project, Equation 0A8Z and Lemma 08JA.
(blueprint: lem-pur-hom-complex-hypercohomology). -/
theorem rhom_hypercohomology_bridgeOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max c v r})
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hI : ∀ M, (I.obj M).IsKInjective) :
    Nonempty (((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q ⋙ ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R) ≅
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).op).prod
          (I ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda) := by
  classical
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v r}
  let Γ : A ⥤ AddCommGrpCat.{max c v r} := preadditiveCoyoneda.obj
    (op (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  let P := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod
    (ObjectProperty.lift (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R) I hI)
  obtain ⟨a⟩ := (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{c, v, r, w, _}
    (R := R)).1
  obtain ⟨b⟩ := (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{c, v, r, w, _}
    (R := R)).2.1
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let T := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod I
  let F := T ⋙ H
  let L := DerivedInternalHomSectionsModel.representativeHom.{c, v, r} R
  let Gs := Γ.mapHomologicalComplex (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := A)
  let Qg := DerivedCategory.Q (C := AddCommGrpCat.{max c v r})
  let S := DerivedInternalHomSectionsModel.derivedSections.{c, v, r, w, _} R
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{max c v r} 0
  let H₀ := HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r}
    (ComplexShape.up ℤ) 0
  -- Reassociate before applying homology, while the intermediate functors are explicit.
  let d : L ⋙ Q ⋙ S ≅ L ⋙ Gs ⋙ Qg :=
    (Functor.associator L Q S).symm ≪≫ Functor.isoWhiskerRight a.symm S ≪≫ b ≪≫
      Functor.associator L Gs Qg
  let d₀ : L ⋙ Q ⋙ S ⋙ Hd ≅ L ⋙ Gs ⋙ H₀ :=
    Functor.isoWhiskerLeft L (Functor.associator Q S Hd).symm ≪≫
      (Functor.associator L (Q ⋙ S) Hd).symm ≪≫
      Functor.isoWhiskerRight d Hd ≪≫ Functor.associator L (Gs ⋙ Qg) Hd ≪≫
      Functor.isoWhiskerLeft L (Functor.associator Gs Qg Hd ≪≫
        Functor.isoWhiskerLeft Gs
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v r} 0))
  -- Cancel the lift and inclusion before composing with the Hom and derived functors.
  let G := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod
    (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι
  let p : P ⋙ G ≅ T := Iso.refl _
  let f : P ⋙ L ≅ F :=
    (Functor.associator P G H).symm ≪≫ Functor.isoWhiskerRight p H
  let z : F ⋙ DerivedCategory.Q ⋙
      ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R ≅
      F ⋙ Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (ComplexShape.up ℤ) 0 :=
    Functor.isoWhiskerRight f.symm (Q ⋙ S ⋙ Hd) ≪≫
      Functor.associator P L (Q ⋙ S ⋙ Hd) ≪≫ Functor.isoWhiskerLeft P d₀ ≪≫
      (Functor.associator P L (Gs ⋙ H₀)).symm ≪≫ Functor.isoWhiskerRight f (Gs ⋙ H₀)
  obtain ⟨e⟩ := homComplex_global_homotopyOfUniverses.{c, v, r} J R
  exact ⟨z ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((𝟭 (CochainComplex A ℤ)ᵒᵖ).prod I) e⟩

end CategoryTheory
