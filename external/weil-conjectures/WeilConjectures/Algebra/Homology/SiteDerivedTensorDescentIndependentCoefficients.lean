/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor descent on a ringed site

Site object, morphism, and coefficient universes are independent. The site is essentially
small relative to the coefficient universe, as required by the source. The statement retains
every localization, representative-comparison, and transformation-extension clause.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
Categories, Tags 04VI, 04VJ and 04VK
(auxiliary; not a blueprint node).

## Main statements

- `site_derived_tensor_descent_independentCoefficients`: localization, representative comparison,
  and unique extension of arbitrary natural transformations.
-/

@[expose] public section

universe u v r w e z

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
-- Resolve the new vertices in Ore squares, roofs, and common refinements.
set_option synthInstance.maxSize 2048 in
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

open MonoidalCategory in
-- Additivity is the only part of closed tensor structure needed for descent.
private theorem tensorPreadditive
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r}) :
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have (M : A) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

-- K-flatness kills the tensor of an acyclic mapping cone.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_right_quasiIso
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [Limits.HasColimitsOfSize.{0, 0} A]
    {E E' K : CochainComplex A ℤ} (α : E ⟶ E') (hα : QuasiIso α)
    (hK : ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F K (MonoidalCategory.curriedTensor A)).Acyclic) :
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K)
      (MonoidalCategory.curriedTensor A) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K (MonoidalCategory.curriedTensor A))

-- The module braiding and signed total-complex flip give the other tensor order.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_left_quasiIso
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [Limits.HasColimitsOfSize.{0, 0} A]
    {K E E' : CochainComplex A ℤ} (α : E ⟶ E') (hα : QuasiIso α)
    (hK : ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F K (MonoidalCategory.curriedTensor A)).Acyclic) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor A) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor A
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_homotopy_map
    {A : Type*} [Category* A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [Limits.HasColimitsOfSize.{0, 0} A]
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    let H := HomotopyCategory.quotient A (.up ℤ)
    let B := Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor A).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))
    B.map (X := (H.obj P, H.obj Q)) (Y := (H.obj P', H.obj Q'))
        (H.map f, H.map g) =
      H.map (HomologicalComplex.mapBifunctorMap f (𝟙 Q)
        (MonoidalCategory.curriedTensor A) (.up ℤ)) ≫
        H.map (HomologicalComplex.mapBifunctorMap (𝟙 P') g
          (MonoidalCategory.curriedTensor A) (.up ℤ)) := by
  rfl

section TensorDescentPredicates

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{w} (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

set_option hygiene false in
local notation "𝓜" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The derived-comparison predicate used in the recorded descent witness.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
noncomputable def SiteDerivedTensorDescentDerivedSpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ)))
    (B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ))
    (T : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ DerivedCategory 𝓜) : Prop :=
  Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
    ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)

/-- The homotopy-comparison predicate, with its derived witness named separately.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
noncomputable def SiteDerivedTensorDescentHomotopySpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ)))
    (B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ)) : Prop :=
  letI := monoidalCategory R
  Nonempty (((HomotopyCategory.quotient 𝓜 (.up ℤ)).prod
    (HomotopyCategory.quotient 𝓜 (.up ℤ))) ⋙ B ≅
    Functor.uncurry.obj ((MonoidalCategory.curriedTensor 𝓜).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ HomotopyCategory.quotient 𝓜 (.up ℤ)) ∧
  ∃ T : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ DerivedCategory 𝓜,
    SiteDerivedTensorDescentDerivedSpec J R P B T

/-- The full descent predicate, transparently identical to the expanded statement.
Naming its nested predicates keeps selected witnesses small during kernel checking.
Source: Stacks, Tags 06YS, 06YU, 04VK
(auxiliary; not a blueprint node). -/
noncomputable def SiteDerivedTensorDescentSpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ))) : Prop :=
  (∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X.as ∧
    ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (X.as.X n)) ∧
  (∃ F : ((HomotopyCategory.quasiIso 𝓜 (.up ℤ)).inverseImage P.ι).Localization ⥤
      DerivedCategory 𝓜,
    F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso 𝓜 (.up ℤ)).inverseImage P.ι).Q ⋙
      F ≅ P.ι ⋙ DerivedCategory.Qh)) ∧
  (∃ B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ), SiteDerivedTensorDescentHomotopySpec J R P B) ∧
  (∀ (E : Type e) (_ : Category.{z} E)
    (U V : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ E),
    Function.Bijective (fun τ : U ⟶ V ↦
      Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))

end TensorDescentPredicates

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false in
/-- K-flat complexes with flat terms present the derived category and its tensor bifunctor.
The existential predicate `P` specifies the full subcategory by its precise membership
condition; `B` is total tensor on homotopy categories, specified by a natural comparison
with total tensor on complexes. The comparison for `T` is natural in both homotopy variables.
Naturality also gives the inverse-denominator equations by multiplying the naturality square
by the inverses of the denominator images. The final bijection includes arbitrary natural
transformations, without an invertibility assumption.

Source: Stacks Project, Tags 06YS, 0G7D, 06YT, 06YU and Categories 04VK
(auxiliary; not a blueprint node).

Proof plan:
The recorded site flatness predicate is exactness of sheafified sectionwise tensor,
which is the canonical monoidal sheaf tensor used in the comparisons below.
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
theorem site_derived_tensor_descent_independentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ P : ObjectProperty (HomotopyCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ)),
      SiteDerivedTensorDescentSpec.{u, v, r, w, e, z} J R P := by
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let P : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦
    CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let V := W.inverseImage P.ι
  let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory A)
  have hL : L.IsLocalization V := by
    apply restriction_localization W DerivedCategory.Qh P
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hs : ∀ n, IsFlatOnSite (J := J) (R := R) (K.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (K.X n)).symm (hflat n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK, hs⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  let F := (Localization.equivalenceFromModel L V).functor
  refine ⟨P, (fun _ ↦ Iff.rfl), ⟨F, inferInstance,
    ⟨Localization.qCompEquivalenceFromModelFunctorIso L V⟩⟩, ?_, ?_⟩
  · let := monoidalCategory R
    let := symmetricCategory R
    let := tensorPreadditive R
    let B := Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor A).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))
    refine ⟨B, ⟨Functor.uncurry.mapIso
      ((MonoidalCategory.curriedTensor A).whiskeringLeft₂BifunctorMapHomotopyCategoryIso
        (.up ℤ) (.up ℤ) (.up ℤ))⟩, ?_⟩
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
      rw [← hf₁, ← hf₂, tensor_homotopy_map]
      rw [← Q.map_comp]
      apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      change QuasiIso _
      infer_instance
    refine ⟨Localization.lift H hH (L.prod L), ?_⟩
    exact ⟨(Localization.fac H hH (L.prod L)).symm⟩
  · intro E hE U V'
    exact (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (V.prod V) E).map_bijective U V'

/-- The original homotopy-tensor existence proof, with its predicate kept named.
The quotient comparison determines this bifunctor up to compatible natural isomorphism.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
theorem siteHomotopyTensorExistsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ B : HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ×
        HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ⥤
        HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ),
      SiteDerivedTensorDescentHomotopySpec J R
        (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose B :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1

/-- The original derived-tensor existence proof, with its predicate kept named.
This separates the proof from the selected data and retains the original witnesses.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
theorem siteDerivedTensorExistsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ T : DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
        DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)),
      SiteDerivedTensorDescentDerivedSpec J R
        (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose
        (siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose T :=
  (siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose_spec.2

/-- The derived tensor supplied by the resolving-class localization, in independent universes.
The natural representative comparison and unique-extension property of
`site_derived_tensor_descent_independentCoefficients` determine this functor up to the
unique compatible natural isomorphism. No functorial resolutions are chosen.
Source: Stacks, Tags 06YS, 0G7D, 06YT, 06YU
(auxiliary; not a blueprint node). -/
noncomputable def siteDerivedTensorIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  (siteDerivedTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose

end SheafOfModules
