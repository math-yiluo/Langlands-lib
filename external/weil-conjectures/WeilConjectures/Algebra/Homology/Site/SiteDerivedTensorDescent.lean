/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-!
# Derived tensor descent on a ringed site

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
Categories, Tags 04VI, 04VJ and 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).
-/

@[expose] public section

universe u w e z

open CategoryTheory

namespace SheafOfModules

-- Resolve the new vertices in Ore squares, roofs, and common refinements.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem restriction_localization
    {A : Type u} [Category.{e} A] {D : Type w} [Category.{z} D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  have : V.HasRightCalculusOfFractions :=
    { exists_rightFraction := by
        intro X Y φ
        obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk φ.f.hom φ.s.hom φ.hs
          : W.LeftFraction X.obj Y.obj).exists_rightFraction
        obtain ⟨Z, r, hr⟩ := res ψ.X'
        refine ⟨MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (r ≫ ψ.s)) (W.comp_mem _ _ hr ψ.hs)
          (ObjectProperty.homMk (r ≫ ψ.f)), ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hψ).trans
          (Category.assoc _ _ _).symm)
      ext := by
        intro X Y Y' f g s hs h
        obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
          f.hom g.hom s.hom hs (congrArg (fun k ↦ k.hom) h)
        obtain ⟨T, r, hr⟩ := res Z
        refine ⟨T, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) heq).trans
          (Category.assoc _ _ _).symm) }
  let h : V.IsInvertedBy (P.ι ⋙ L) := fun _ _ s hs ↦ Localization.inverts L W s.hom hs
  let F := Localization.Construction.lift (P.ι ⋙ L) h
  have fac : V.Q ⋙ F = P.ι ⋙ L := Localization.Construction.fac _ _
  have fmap {X Y : P.FullSubcategory} (f : X ⟶ Y) :
      F.map (V.Q.map f) = L.map f.hom := by
    simpa using (eqToIso fac).hom.naturality f
  have hf : F.Full := by
    refine ⟨?_⟩
    intro X Y f
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W
      (show L.obj X₀.obj ⟶ L.obj Y₀.obj from f)
    obtain ⟨Z, r, hr⟩ := res φ.X'
    let ψ : V.RightFraction X₀ Y₀ := MorphismProperty.RightFraction.mk
      (ObjectProperty.homMk (r ≫ φ.s)) (W.comp_mem _ _ hr φ.hs)
      (ObjectProperty.homMk (r ≫ φ.f))
    refine ⟨ψ.map V.Q (Localization.inverts _ _), ?_⟩
    have : IsIso (L.map r) := Localization.inverts L W r hr
    have : IsIso (L.map φ.s) := Localization.inverts L W φ.s φ.hs
    have : IsIso (L.map (r ≫ φ.s)) :=
      Localization.inverts L W _ (W.comp_mem _ _ hr φ.hs)
    simp only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv, fmap]
    change inv (L.map (r ≫ φ.s)) ≫ L.map (r ≫ φ.f) = f
    rw [hφ]
    simp [MorphismProperty.RightFraction.map]
  have hfaith : F.Faithful := by
    refine ⟨?_⟩
    intro X Y f g heq
    let X₀ : P.FullSubcategory := X.as.obj
    let Y₀ : P.FullSubcategory := Y.as.obj
    obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from f)
    obtain ⟨ψ, rfl⟩ := Localization.exists_rightFraction V.Q V
      (show V.Q.obj X₀ ⟶ V.Q.obj Y₀ from g)
    let φ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk φ.s.hom φ.hs φ.f.hom
    let ψ' : W.RightFraction X₀.obj Y₀.obj :=
      MorphismProperty.RightFraction.mk ψ.s.hom ψ.hs ψ.f.hom
    have heq' : φ'.map L (Localization.inverts _ _) =
        ψ'.map L (Localization.inverts _ _) := by
      simpa only [MorphismProperty.RightFraction.map, Functor.map_comp, Functor.map_inv,
        fmap] using heq
    obtain ⟨Z, a, b, hs, hf, hw⟩ :=
      (MorphismProperty.RightFraction.map_eq_iff L W φ' ψ').1 heq'
    obtain ⟨T, r, hr⟩ := res Z
    apply (MorphismProperty.RightFraction.map_eq_iff V.Q V φ ψ).2
    refine ⟨T, ObjectProperty.homMk (r ≫ a), ObjectProperty.homMk (r ≫ b), ?_, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans
        (Category.assoc _ _ _).symm)
    · apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hf).trans
        (Category.assoc _ _ _).symm)
    · change W ((r ≫ a) ≫ φ.s.hom)
      rw [Category.assoc]
      exact W.comp_mem _ _ hr hw
  have hess : F.EssSurj := by
    refine ⟨?_⟩
    intro X
    have := Localization.essSurj L W
    let Y := L.objPreimage X
    let e := L.objObjPreimageIso X
    obtain ⟨Z, r, hr⟩ := res Y
    exact ⟨V.Q.obj Z, ⟨Localization.isoOfHom L W r hr ≪≫ e⟩⟩
  have : F.IsEquivalence := { }
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V (eqToIso fac)

-- K-flatness kills the tensor of an acyclic mapping cone.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_right_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {E E' K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsAcyclicTensorKFlat) :
    let := monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K)
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  let := monoidalCategory R
  let := (tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K (MonoidalCategory.curriedTensor _))

-- The module braiding and signed total-complex flip give the other tensor order.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_left_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {K E E' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsAcyclicTensorKFlat) :
    let := monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  let := monoidalCategory R
  let := symmetricCategory R
  let := (tensorClosed R).1.some
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- K-flat complexes with flat terms present the derived category and its tensor bifunctor.
The existential predicate `P` specifies the full subcategory by its precise membership
condition; `B` is total tensor on homotopy categories, specified by a natural comparison
with total tensor on complexes. The comparison for `T` is natural in both homotopy variables.
Naturality also gives the inverse-denominator equations by multiplying the naturality square
by the inverses of the denominator images. The final bijection includes arbitrary natural
transformations, without an invertibility assumption.

Source: Stacks Project, Tags 06YS, 0G7D, 06YT, 06YU and Categories 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

Proof plan:
1. Resolve the vertex of each Ore square and cancellation witness by a K-flat flat-term
   resolution (`lem-pc-kflat-resolution`). The right calculus of fractions for the ambient
   homotopy category (`lem-pc-quasi-isomorphisms-multiplicative-system`) restricts to `P`.
2. The localization universal property induces the comparison functor. Refine every roof
   by a K-flat flat-term resolution to prove fullness (`lem-pc-right-fraction-representation`).
   Resolve common refinement vertices to prove faithfulness
   (`lem-pc-right-fraction-common-refinement`). Resolutions give essential surjectivity.
3. Total tensor descends through homotopy: a homotopy in the first variable is `h ⊗ 1`;
   in the second variable its component in bidegree `(p,q)` is `(-1)^p 1 ⊗ k`.
   The cross differential terms cancel, giving the natural comparison defining `B`.
4. Tensoring a quasi-isomorphism with a K-flat complex preserves quasi-isomorphisms:
   its cone is acyclic (`lem-pur-quasi-iso-cone-acyclic`), tensor preserves its acyclicity
   (`def-pc-kflat-complex`), and total tensor commutes with the cone differential.
   The symmetry with sign `(-1)^(pq)` gives the other variable.
5. Localize the tensor bifunctor twice (`lem-weil-pbc-localization-universal-property`),
   first into a functor category, then in the other variable. This gives `T` and its natural
   representative comparison. Inverting the naturality equations gives compatibility with
   inverse denominators.
6. Extend a transformation uniquely in the first variable by the same localization property.
   Uniqueness implies naturality in the second variable. Localize that variable to get the
   extension on the product derived category. Two applications of uniqueness prove bijectivity.
-/
theorem site_derived_tensor_descent
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∃ P : ObjectProperty (HomotopyCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)),
      (∀ X, P X ↔ CochainComplex.IsAcyclicTensorKFlat X.as ∧
        ∀ n : ℤ, SheafOfModules.IsFlat (X.as.X n)) ∧
      (∃ F : ((HomotopyCategory.quasiIso (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Localization ⥤ (DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))),
        F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Q ⋙ F ≅ (P.ι ⋙ DerivedCategory.Qh))) ∧
      (∃ B : (HomotopyCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)) ×
          (HomotopyCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)) ⥤
          (HomotopyCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)),
        Nonempty (((HomotopyCategory.quotient (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)).prod
          (HomotopyCategory.quotient (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ))) ⋙ B ≅
          Functor.uncurry.obj
            ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
                (HomotopyCategory.quotient (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ))) ∧
        ∃ T : (DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
          (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ (DerivedCategory
          (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))),
          Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
            ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
          (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦
          Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ)) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let P : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦
    CochainComplex.IsAcyclicTensorKFlat X.as ∧ ∀ n : ℤ, SheafOfModules.IsFlat (X.as.X n)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let V := W.inverseImage P.ι
  let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory A)
  have hL : L.IsLocalization V := by
    apply restriction_localization W DerivedCategory.Qh P
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ := CochainComplex.exists_isKFlatResolution X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK, hflat⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  let F := (Localization.equivalenceFromModel L V).functor
  refine ⟨P, (fun _ ↦ Iff.rfl), ⟨F, inferInstance,
    ⟨Localization.qCompEquivalenceFromModelFunctorIso L V⟩⟩, ?_, ?_⟩
  · let := monoidalCategory R
    let := (tensorClosed R).1.some
    let B := Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor A).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))
    refine ⟨B, ⟨Iso.refl _⟩, ?_⟩
    let H := (P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh
    have hH : (V.prod V).IsInvertedBy H := by
      intro X Y f hf
      let Q := HomotopyCategory.quotient A (.up ℤ)
      obtain ⟨f₁, hf₁⟩ := Q.map_surjective f.1.hom
      obtain ⟨f₂, hf₂⟩ := Q.map_surjective f.2.hom
      have hq₁ : QuasiIso f₁ :=
        (HomotopyCategory.quotient_map_mem_quasiIso_iff f₁).1 (hf₁ ▸ hf.1)
      have hq₂ : QuasiIso f₂ :=
        (HomotopyCategory.quotient_map_mem_quasiIso_iff f₂).1 (hf₂ ▸ hf.2)
      have ht₁ := tensor_right_quasiIso f₁ hq₁ X.2.property.1
      have ht₂ := tensor_left_quasiIso f₂ hq₂ Y.1.property.1
      change IsIso (DerivedCategory.Qh.map
        (B.map (X := (X.1.obj, X.2.obj)) (Y := (Y.1.obj, Y.2.obj)) (f.1.hom, f.2.hom)))
      apply Localization.inverts DerivedCategory.Qh W _
      rw [← hf₁, ← hf₂]
      change W (Q.map (HomologicalComplex.mapBifunctorMap f₁ (𝟙 _)
        (MonoidalCategory.curriedTensor A) (.up ℤ)) ≫
        Q.map (HomologicalComplex.mapBifunctorMap (𝟙 _) f₂
          (MonoidalCategory.curriedTensor A) (.up ℤ)))
      rw [← Q.map_comp]
      apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      change QuasiIso _
      infer_instance
    refine ⟨Localization.lift H hH (L.prod L), ?_⟩
    exact ⟨(Localization.fac H hH (L.prod L)).symm⟩
  · intro E hE U V'
    exact (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (V.prod V) E).map_bijective U V'

end SheafOfModules
