/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
public import WeilConjectures.AlgebraicGeometry.RingTensorCechCoordinates
import WeilConjectures.AlgebraicGeometry.GlobalSectionComplexMonoidal
import WeilConjectures.AlgebraicGeometry.GlobalSectionLocalizationFactor

/-! # Base change of the actual tensor localization construction

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E, final paragraph;
algebra.tex, Tag 00DK (localization commutes with base change).
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive
attribute [local instance] SheafOfModules.isGrothendieckAbelian
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private noncomputable instance globalTensorSmallColimits
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{u}) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0} (SheafOfModules.{u} R) :=
  CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u} _

private noncomputable instance pointTensorMonoidal (A : Type u) [CommRing A] :
    MonoidalCategory (RingSiteModules A) :=
  SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)

private noncomputable instance pointTensorSymmetric (A : Type u) [CommRing A] :
    SymmetricCategory (RingSiteModules A) :=
  SheafOfModules.symmetricCategory (CochainComplex.onePointRingSheaf A)

private noncomputable instance pointTensorPreadditive (A : Type u) [CommRing A] :
    MonoidalPreadditive (RingSiteModules A) :=
  Classical.choice (SheafOfModules.tensorClosed (CochainComplex.onePointRingSheaf A)).1

private noncomputable instance pointTensorClosed (A : Type u) [CommRing A] :
    MonoidalClosed (RingSiteModules A) :=
  Classical.choice (SheafOfModules.tensorClosed (CochainComplex.onePointRingSheaf A)).2.1

private noncomputable instance globalTensorPreadditive
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K CommRingCat.{u}) :
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).1

private noncomputable instance globalTensorClosed
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K CommRingCat.{u}) :
    MonoidalClosed (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :=
  Classical.choice (SheafOfModules.tensorClosed R).2.1

private noncomputable instance pointTensorCochain (A : Type u) [CommRing A] :
    MonoidalCategory (CochainComplex (RingSiteModules A) ℤ) := by
  let : CategoryTheory.Limits.HasZeroObject (RingSiteModules A) := inferInstance
  exact smallClosedCochainMonoidal (RingSiteModules A)

private noncomputable instance globalTensorCochain
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K CommRingCat.{u}) :
    MonoidalCategory (CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ) := by
  let : CategoryTheory.Limits.HasZeroObject (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) := inferInstance
  exact smallClosedCochainMonoidal (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))

private theorem augmented_tensor_map
    {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (T : A ⥤ B) [T.Monoidal] {P Q : A} (a : P ⟶ 𝟙_ A) (b : Q ⟶ 𝟙_ A) :
    Functor.LaxMonoidal.μ T P Q ≫ T.map ((a ⊗ₘ b) ≫ (λ_ (𝟙_ A)).hom) ≫
        Functor.OplaxMonoidal.η T =
      ((T.map a ≫ Functor.OplaxMonoidal.η T) ⊗ₘ
        (T.map b ≫ Functor.OplaxMonoidal.η T)) ≫ (λ_ (𝟙_ B)).hom := by
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  simp only [Functor.Monoidal.map_leftUnitor, Category.assoc,
    Functor.Monoidal.μ_δ_assoc]
  rw [← leftUnitor_naturality]
  simp only [← Category.assoc, ← tensorHom_def,
    ← tensorHom_comp_tensorHom_assoc]

-- The canonical tensor units and scalar-extension functor require several conversions.
/-- Global-section scalar extension commutes with the ordered tensor construction.
This assertion involves only the actual tensor complexes, not an arbitrary complex
or any ordered coordinate identifications.
Source: Stacks Project, algebraization.tex, Tags 0996, 099E, final paragraph;
algebra.tex, Tag 00DK.
(auxiliary; not a blueprint node).

Proof: use the normalized strong monoidal structure on module scalar extension and
its preservation of the small coproducts defining total tensors. The existing additive
monoidal lift gives the tensorator on complexes. Its inverse unit is the single-complex
comparison followed by the single of the fixed module multiplication map, hence the
specified scalar-extended augmentation on the identity. For one localization factor,
use the scalar-multiplication sequential colimit: the fixed unit intertwines the
scalar transitions, and scalar extension preserves this colimit. The colimit comparison
commutes with the localization unit by the first fraction-leg identity. The existing
generic two-term comparison gives an isomorphism compatible with the projections.
Induct on the actual recursive tensor list. The empty case is the unit inverse identity.
For a successor tensor the first-factor and tail isomorphisms, then compose with the
complex tensorator. Tensorator naturality for the two augmentations and left-unitor
coherence give the tensor of their scalar extensions. Composition of tensor morphisms
and the two induction equations give the specified target augmentation. The colimit
argument and induction include zero or repeated sections, zero rings and empty lists. -/
theorem ringFamilyGlobalExtension_tensor_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : (ringedExtendedCech O r f).1 ≅ ringFamilyGlobalExtensionComplex O
        (ringTensorCech (ringFamilyGlobalRing O) r (ringFamilyGlobalList O r f)).1,
      e.hom ≫ ringFamilyGlobalExtensionAugmentation O
        (ringTensorCech (ringFamilyGlobalRing O) r (ringFamilyGlobalList O r f)).2 =
          (ringedExtendedCech O r f).2 := by
  let T := (ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)
  obtain ⟨mon, hmon⟩ := ringFamilyGlobalExtension_complex_monoidal O
  let := mon
  have haug {P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ}
      (a : P ⟶ ringComplexSingle (ringFamilyGlobalRing O)) :
      ringFamilyGlobalExtensionAugmentation O a =
        T.map a ≫ Functor.OplaxMonoidal.η T := by
    rw [hmon]
    simp only [ringFamilyGlobalExtensionAugmentation, Functor.map_id]
    erw [Category.id_comp]
  have htensor {P Q : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ}
      (a : P ⟶ ringComplexSingle (ringFamilyGlobalRing O))
      (b : Q ⟶ ringComplexSingle (ringFamilyGlobalRing O)) :
      Functor.LaxMonoidal.μ T P Q ≫
          ringFamilyGlobalExtensionAugmentation O ((a ⊗ₘ b) ≫ (λ_ _).hom) =
        (ringFamilyGlobalExtensionAugmentation O a ⊗ₘ
          ringFamilyGlobalExtensionAugmentation O b) ≫ (λ_ (ringedSiteRingComplex O)).hom := by
    simp only [haug]
    exact augmented_tensor_map T a b
  induction r with
  | zero =>
      refine ⟨Functor.Monoidal.εIso T, ?_⟩
      change (Functor.Monoidal.εIso T).hom ≫
        ringFamilyGlobalExtensionAugmentation O
          (𝟙 (ringComplexSingle (ringFamilyGlobalRing O))) = 𝟙 _
      erw [← hmon]
      exact Functor.Monoidal.ε_η T
  | succ r ih =>
      obtain ⟨e, he⟩ := ih (fun i ↦ f i.succ)
      obtain ⟨d, hd⟩ := ringFamilyGlobalExtension_localization_factor O (f 0)
      let P := ringedLocalizationTwoTerm
        (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
        (ringTensorCechSection (ringFamilyGlobalRing O) (f 0))
      let Q := (ringTensorCech (ringFamilyGlobalRing O) r
        (ringFamilyGlobalList O r (fun i ↦ f i.succ))).1
      let a : P ⟶ ringComplexSingle (ringFamilyGlobalRing O) :=
        ringedLocalizationTwoTermAugmentation
          (CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O))
          (ringTensorCechSection (ringFamilyGlobalRing O) (f 0))
      let b : Q ⟶ ringComplexSingle (ringFamilyGlobalRing O) :=
        (ringTensorCech (ringFamilyGlobalRing O) r
          (ringFamilyGlobalList O r (fun i ↦ f i.succ))).2
      refine ⟨(d ⊗ᵢ e) ≪≫ Functor.Monoidal.μIso T P Q, ?_⟩
      change ((d.hom ⊗ₘ e.hom) ≫ Functor.LaxMonoidal.μ T P Q) ≫
        ringFamilyGlobalExtensionAugmentation O ((a ⊗ₘ b) ≫ (λ_ _).hom) =
          (ringedLocalizationTwoTermAugmentation O (f 0) ⊗ₘ
            (ringedExtendedCech O r (fun i ↦ f i.succ)).2) ≫ (λ_ _).hom
      rw [Category.assoc, htensor]
      rw [tensorHom_comp_tensorHom_assoc]
      rw [hd, he]

end CategoryTheory
