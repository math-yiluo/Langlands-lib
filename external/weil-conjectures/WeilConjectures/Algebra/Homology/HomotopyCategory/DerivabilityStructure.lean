/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.CategoryTheory.GuitartExact.Quotient
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfLocalizedEquivalences
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.FromJoel.CategoryTheory.Localization.Composition
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.Localization

/-!
# Left derivability structures on the homotopy category given by functorial resolutions

Let `A` be an abelian category and `P` a triangulated property of objects of the homotopy
category `K(A)` which is closed under isomorphisms. Suppose that there is a functorial
resolution `p : ρ ⟶ 𝟭` on cochain complexes, whose components are quasi-isomorphisms and
such that `P` holds for the image of `ρ K` in `K(A)` for every `K`. Then the inclusion of
the full subcategory of `K(A)` given by `P`, with the quasi-isomorphisms, is a left
derivability structure (`HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`).

The statement is first obtained on the category of cochain complexes, and then transferred to
`K(A)`, the quotient functor being a localized equivalence on both sides. The K-flat left
derivability structure of `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` is the
case where `P` is the property of being K-flat.

## Main definitions and results

- `HomotopyCategory.quasiIsoLocalizerMorphism P`: the localizer morphism given by the inclusion
  of the full subcategory of `K(A)` defined by `P`, with the quasi-isomorphisms.
- `HomotopyCategory.prop_quotient_obj_cylinder`: a triangulated property of `K(A)` holding
  for the image of a complex `K` holds for the image of its cylinder.
- `HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism`: it is a left
  derivability structure as soon as `P` contains functorial resolutions.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra

namespace HomotopyCategory

variable {A : Type*} [Category A] [Abelian A]
  (P : ObjectProperty (HomotopyCategory A (.up ℤ)))

/-- The localizer morphism given by the inclusion of the full subcategory of the homotopy
category defined by `P`, with the quasi-isomorphisms on both sides. -/
@[simps]
def quasiIsoLocalizerMorphism :
    LocalizerMorphism ((quasiIso A (.up ℤ)).inverseImage P.ι) (quasiIso A (.up ℤ)) where
  functor := P.ι
  map := by rfl

instance : (quasiIsoLocalizerMorphism P).functor.Full := inferInstanceAs P.ι.Full

instance : (quasiIsoLocalizerMorphism P).functor.Faithful := inferInstanceAs P.ι.Faithful

namespace quasiIsoLocalizerMorphism

/-! The auxiliary commutative square of localizer morphisms used to transfer the left
derivability structure from cochain complexes to the homotopy category, where
`Q = P.inverseImage (quotient A (.up ℤ))`:
```
 Q.FullSubcategory --(cochainComplexLocalizerMorphism P)--> CochainComplex A ℤ
        |                                                           |
 (quotientRestrictLocalizerMorphism P)             (quotientLocalizerMorphism A (.up ℤ))
        v                                                           v
 P.FullSubcategory ------(quasiIsoLocalizerMorphism P)-----------> K(A)
```
-/

/-- The inclusion of the complexes whose image in `K(A)` satisfies `P`, with the
quasi-isomorphisms. -/
@[simps]
def cochainComplexLocalizerMorphism : LocalizerMorphism
    ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage
      (P.inverseImage (quotient A (.up ℤ))).ι)
    (HomologicalComplex.quasiIso A (.up ℤ)) where
  functor := (P.inverseImage (quotient A (.up ℤ))).ι
  map := by rfl

instance : (cochainComplexLocalizerMorphism P).functor.Full :=
  inferInstanceAs (P.inverseImage (quotient A (.up ℤ))).ι.Full

instance : (cochainComplexLocalizerMorphism P).functor.Faithful :=
  inferInstanceAs (P.inverseImage (quotient A (.up ℤ))).ι.Faithful

/-- The quotient functor, restricted to the complexes whose image in `K(A)` satisfies `P`. -/
def quotientRestrictLocalizerMorphism : LocalizerMorphism
    ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage
      (P.inverseImage (quotient A (.up ℤ))).ι)
    ((quasiIso A (.up ℤ)).inverseImage P.ι) where
  functor := ObjectProperty.lift _
    ((P.inverseImage (quotient A (.up ℤ))).ι ⋙ quotient _ _) (fun K ↦ K.2)
  map := by
    rintro ⟨K, hK⟩ ⟨L, hL⟩ ⟨f : K ⟶ L⟩ hf
    simpa [quotient_map_mem_quasiIso_iff] using hf

/-- The auxiliary square of localizer morphisms commutes (definitionally):
```
 Q.FullSubcategory --(cochainComplexLocalizerMorphism P)--> CochainComplex A ℤ
        |                                                           |
 (quotientRestrictLocalizerMorphism P)             (quotientLocalizerMorphism A (.up ℤ))
        v                                                           v
 P.FullSubcategory ------(quasiIsoLocalizerMorphism P)-----------> K(A)
```
where `Q = P.inverseImage (quotient A (.up ℤ))`. -/
def quotientSquareIso :
    (cochainComplexLocalizerMorphism P).functor ⋙ (quotientLocalizerMorphism A (.up ℤ)).functor ≅
      (quotientRestrictLocalizerMorphism P).functor ⋙ (quasiIsoLocalizerMorphism P).functor :=
  Iso.refl _

/-- The homotopy equivalences between complexes whose image in `K(A)` satisfies `P`. -/
def homotopyEquivalencesRestrict :
    MorphismProperty (P.inverseImage (quotient A (.up ℤ))).FullSubcategory :=
  (homotopyEquivalences A (.up ℤ)).inverseImage (cochainComplexLocalizerMorphism P).functor

instance : (quotientRestrictLocalizerMorphism P).functor.EssSurj where
  mem_essImage := by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    exact ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩

instance : (quotientRestrictLocalizerMorphism P).functor.Full where
  map_surjective {K L} f := by
    obtain ⟨g, hg⟩ := (quotient _ _).map_surjective f.hom
    exact ⟨ObjectProperty.homMk g, by cat_disch⟩

end quasiIsoLocalizerMorphism

variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

variable {P} in
/-- A triangulated property of objects of `K(A)`, closed under isomorphisms, which holds for
the image of a cochain complex `K` also holds for the image of its cylinder: the cylinder is
the mapping cone of a morphism `K ⟶ K ⊞ K`. -/
lemma prop_quotient_obj_cylinder {K : CochainComplex A ℤ} (hK : P ((quotient A (.up ℤ)).obj K)) :
    P ((quotient A (.up ℤ)).obj K.cylinder) := by
  apply ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ (mappingCone_triangleh_distinguished _)
  · exact hK
  · have := preservesBinaryBiproducts_of_preservesBiproducts (quotient A (.up ℤ))
    refine P.prop_of_iso ((biprod.isoProd _ _).symm ≪≫ ((quotient _ _).mapBiprod K K).symm) ?_
    exact P.prop_prod _ _ hK hK

namespace quasiIsoLocalizerMorphism

instance : (quotientRestrictLocalizerMorphism P).functor.IsLocalization
    (homotopyEquivalencesRestrict P) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      have := (NatIso.isIso_map_iff (quotientSquareIso P) f).1
        (quotient_inverts_homotopyEquivalences _ _ _ hf)
      dsimp only [Functor.comp_map] at this
      exact isIso_of_reflects_iso _ (quasiIsoLocalizerMorphism P).functor) (by
      rintro ⟨K₁, hK₁⟩ ⟨K₂, hK₂⟩ (f₀ f₁) hf
      refine ⟨K₁.precylinder.toFullSubcategory
        (by exact prop_quotient_obj_cylinder hK₁), ?_, ?_⟩
      · exact Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
          { h := cylinder.desc _ _
                (homotopyOfEq _ _ ((ObjectProperty.ι _).congr_map hf)) }
      · exact ⟨cylinder.homotopyEquiv K₁ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩)

instance : (quotientRestrictLocalizerMorphism P).IsLocalizedEquivalence :=
  (quotientRestrictLocalizerMorphism P).isLocalizedEquivalence_of_isLocalization
    (homotopyEquivalencesRestrict P)
    (fun _ _ _ hf ↦ homotopyEquivalences_le_quasiIso _ _ _ hf) (by
      rintro ⟨K, hK⟩ ⟨L, hL⟩ f hf
      obtain ⟨K, rfl⟩ := quotient_obj_surjective K
      obtain ⟨L, rfl⟩ := quotient_obj_surjective L
      obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
      obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
      refine ⟨⟨K, hK⟩, ⟨L, hL⟩, ObjectProperty.homMk f, ?_, ⟨Iso.refl _⟩⟩
      simpa [quotient_map_mem_quasiIso_iff] using hf)

-- Without this option, `cat_disch` fails on the default fields `h₀` and `h₁` of
-- `Precylinder.LeftHomotopy` below.
set_option backward.defeqAttrib.useBackward true in
instance : TwoSquare.GuitartExact (quotientSquareIso P).inv :=
  TwoSquare.GuitartExact.quotient_of_nonempty_leftHomotopy (quotientSquareIso P).symm (by
    rintro ⟨K₁, hK₁⟩ K₂ (f₀ f₁ : K₁ ⟶ K₂) hf
    refine ⟨K₁.precylinder.toFullSubcategory
        (by exact prop_quotient_obj_cylinder hK₁), ?_, ⟨?_⟩⟩
    · ext : 1
      exact eq_of_homotopy _ _
        (cylinder.homotopy₀₁ _ (fun n ↦ ⟨n - 1, by simp⟩))
    · exact { h := cylinder.desc _ _ (homotopyOfEq _ _ hf) })

end quasiIsoLocalizerMorphism

open quasiIsoLocalizerMorphism in
/-- Let `P` be a triangulated property of objects of `K(A)`, closed under isomorphisms. Given
a functorial resolution of cochain complexes by quasi-isomorphisms whose resolutions lie in `P`
```
 ρ K --(p.app K, a quasi-isomorphism)--> K        P ((quotient A (.up ℤ)).obj (ρ K))
```
the inclusion of the full subcategory of `K(A)` defined by `P`
```
 P.FullSubcategory --(quasiIsoLocalizerMorphism P = P.ι)--> K(A)
```
with the quasi-isomorphisms on both sides, is a left derivability structure. -/
lemma isLeftDerivabilityStructure_quasiIsoLocalizerMorphism
    {ρ : CochainComplex A ℤ ⥤ CochainComplex A ℤ} (p : ρ ⟶ 𝟭 _)
    (hp : ∀ K, QuasiIso (p.app K)) (hρ : ∀ K, P ((quotient A (.up ℤ)).obj (ρ.obj K))) :
    (quasiIsoLocalizerMorphism P).IsLeftDerivabilityStructure := by
  have : (cochainComplexLocalizerMorphism P).IsInduced := ⟨rfl⟩
  have : (cochainComplexLocalizerMorphism P).IsLeftDerivabilityStructure :=
    (cochainComplexLocalizerMorphism P).isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift _ ρ hρ) p
      (fun K ↦ by rw [HomologicalComplex.mem_quasiIso_iff]; exact hp K) rfl
  exact LocalizerMorphism.isLeftDerivabilityStructure_of_isLocalizedEquivalence
    (quotientSquareIso P)

end HomotopyCategory
