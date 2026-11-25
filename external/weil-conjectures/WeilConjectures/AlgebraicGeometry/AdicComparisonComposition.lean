/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import WeilConjectures.AlgebraicGeometry.AdicOrdinaryComparisonComposition
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore

/-! # Scalar composition and geometric comparison

Source: Stacks Project, Tags 06YY, 0G7E and 09AL, normalized tensor balancing.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard derivedExtension derivedPull
  DerivedCategory.Q CategoryTheory.constantSheaf CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CochainComplex.IsKFlatTensor CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 10000] change_additive pull_additive SheafOfModules.instAbelian
attribute [local irreducible] adicFiniteComparisonData adicFinitePullbackData
attribute [local instance 10000] adicFiniteSectionModule

private theorem paste_comparisons
    {C₀ C₁ C₂ D₀ D₁ D₂ E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Category E₀] [Category E₁] [Category E₂]
    [Category F₀] [Category F₁] [Category F₂]
    (q₀ : C₀ ⥤ E₀) (q₁ : C₁ ⥤ E₁) (q₂ : C₂ ⥤ E₂)
    (r₀ : D₀ ⥤ F₀) (r₁ : D₁ ⥤ F₁) (r₂ : D₂ ⥤ F₂)
    (a : C₀ ⥤ C₁) (b : C₁ ⥤ C₂) (c : C₀ ⥤ C₂)
    (d : D₀ ⥤ D₁) (e : D₁ ⥤ D₂) (f : D₀ ⥤ D₂)
    (p₀ : C₀ ⥤ D₀) (p₁ : C₁ ⥤ D₁) (p₂ : C₂ ⥤ D₂)
    (A : E₀ ⥤ E₁) (B : E₁ ⥤ E₂) (C : E₀ ⥤ E₂)
    (D : F₀ ⥤ F₁) (E : F₁ ⥤ F₂) (F : F₀ ⥤ F₂)
    (P₀ : E₀ ⥤ F₀) (P₁ : E₁ ⥤ F₁) (P₂ : E₂ ⥤ F₂)
    (εa : q₀ ⋙ A ⟶ a ⋙ q₁) (εb : q₁ ⋙ B ⟶ b ⋙ q₂)
    (εc : q₀ ⋙ C ⟶ c ⋙ q₂)
    (εd : r₀ ⋙ D ⟶ d ⋙ r₁) (εe : r₁ ⋙ E ⟶ e ⋙ r₂)
    (εf : r₀ ⋙ F ⟶ f ⋙ r₂)
    (π₀ : q₀ ⋙ P₀ ⟶ p₀ ⋙ r₀) (π₁ : q₁ ⋙ P₁ ⟶ p₁ ⋙ r₁)
    (π₂ : q₂ ⋙ P₂ ⟶ p₂ ⋙ r₂)
    (α : a ⋙ b ≅ c) (β : d ⋙ e ≅ f)
    (t₁ : p₀ ⋙ d ≅ a ⋙ p₁) (t₂ : p₁ ⋙ e ≅ b ⋙ p₂)
    (t₃ : p₀ ⋙ f ≅ c ⋙ p₂)
    (s : A ⋙ B ≅ C) (t : D ⋙ E ≅ F)
    (T₁ : P₀ ⋙ D ≅ A ⋙ P₁) (T₂ : P₁ ⋙ E ≅ B ⋙ P₂)
    (T₃ : P₀ ⋙ F ≅ C ⋙ P₂)
    (X : C₀)
    (hs : s.hom.app (q₀.obj X) ≫ εc.app X =
      B.map (εa.app X) ≫ εb.app (a.obj X) ≫ q₂.map (α.hom.app X))
    (ht : t.hom.app (r₀.obj (p₀.obj X)) ≫ εf.app (p₀.obj X) =
      E.map (εd.app (p₀.obj X)) ≫ εe.app (d.obj (p₀.obj X)) ≫
        r₂.map (β.hom.app (p₀.obj X)))
    (h₁ : T₁.hom.app (q₀.obj X) ≫ P₁.map (εa.app X) ≫ π₁.app (a.obj X) =
      D.map (π₀.app X) ≫ εd.app (p₀.obj X) ≫ r₁.map (t₁.hom.app X))
    (h₂ : T₂.hom.app (q₁.obj (a.obj X)) ≫
        P₂.map (εb.app (a.obj X)) ≫ π₂.app (b.obj (a.obj X)) =
      E.map (π₁.app (a.obj X)) ≫ εe.app (p₁.obj (a.obj X)) ≫
        r₂.map (t₂.hom.app (a.obj X)))
    (h₃ : T₃.hom.app (q₀.obj X) ≫ P₂.map (εc.app X) ≫ π₂.app (c.obj X) =
      F.map (π₀.app X) ≫ εf.app (p₀.obj X) ≫ r₂.map (t₃.hom.app X))
    (ho : β.hom.app (p₀.obj X) ≫ t₃.hom.app X =
      e.map (t₁.hom.app X) ≫ t₂.hom.app (a.obj X) ≫ p₂.map (α.hom.app X))
    [IsIso (εc.app X)] [IsIso (π₂.app (c.obj X))] :
    t.hom.app (P₀.obj (q₀.obj X)) ≫ T₃.hom.app (q₀.obj X) =
      E.map (T₁.hom.app (q₀.obj X)) ≫ T₂.hom.app (A.obj (q₀.obj X)) ≫
        P₂.map (s.hom.app (q₀.obj X)) := by
  apply (cancel_mono (P₂.map (εc.app X) ≫ π₂.app (c.obj X))).mp
  calc
    _ = E.map (D.map (π₀.app X)) ≫ E.map (εd.app (p₀.obj X)) ≫
        εe.app (d.obj (p₀.obj X)) ≫ r₂.map (β.hom.app (p₀.obj X)) ≫
          r₂.map (t₃.hom.app X) := by
      rw [Category.assoc, h₃, ← t.hom.naturality_assoc]
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [reassoc_of% ht]
    _ = E.map (D.map (π₀.app X)) ≫ E.map (εd.app (p₀.obj X)) ≫
        εe.app (d.obj (p₀.obj X)) ≫ r₂.map (e.map (t₁.hom.app X)) ≫
          r₂.map (t₂.hom.app (a.obj X)) ≫ r₂.map (p₂.map (α.hom.app X)) := by
      rw [← r₂.map_comp, ho]
      simp only [Functor.map_comp]
    _ = E.map (T₁.hom.app (q₀.obj X)) ≫ E.map (P₁.map (εa.app X)) ≫
        E.map (π₁.app (a.obj X)) ≫ εe.app (p₁.obj (a.obj X)) ≫
          r₂.map (t₂.hom.app (a.obj X)) ≫ r₂.map (p₂.map (α.hom.app X)) := by
      have hn := εe.naturality (t₁.hom.app X)
      dsimp only [Functor.comp_map] at hn
      rw [← reassoc_of% hn]
      rw [← E.map_comp_assoc, ← E.map_comp_assoc, Category.assoc, ← h₁]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [← reassoc_of% h₂]
      simp only [Category.assoc]
      have hn := T₂.hom.naturality (εa.app X)
      dsimp only [Functor.comp_map] at hn
      rw [reassoc_of% hn]
      have hn' := π₂.naturality (α.hom.app X)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn'
      rw [← hn']
      rw [← P₂.map_comp_assoc, ← P₂.map_comp_assoc, Category.assoc, ← hs]
      simp only [Functor.map_comp, Category.assoc]

attribute [local irreducible] change pull

section

attribute [local irreducible] Functor.mapHomologicalComplex

private theorem specified_extend_formula
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (e : h = f ≫ g)
    (P : Cx R) (hp : P.IsKFlatIndependentCoefficients) :
    (adicFiniteExtendComp f g h e).hom.app ((Q R).obj P) ≫
        (extendComparison h).app P =
      (extend g).map ((extendComparison f).app P) ≫
        (extendComparison g).app (((change f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Q V).map ((Functor.mapHomologicalComplexCompIso
          (adicOrdinaryChangeComp f g h e) (.up ℤ)).hom.app P) := by
  cases e
  simpa only [adicFiniteExtendComp, adicOrdinaryChangeComp, eqToIso_refl, Iso.trans_refl]
    using (adicFiniteExtendComp_existsUnique f g).exists.choose_spec P hp

end

private theorem complex_composition (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f)
    (P : Cx (constant (smallModelComparisonEtaleTopology.{u, v} X) A)) :
    (Functor.mapHomologicalComplexCompIso
      (adicOrdinaryChangeComp
        (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantComp _ f g h e)) (.up ℤ)).hom.app
          (((adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X h)).hom.app P =
      ((change (adicFiniteConstantMap g
          (coefficientProEtaleModelTopology.{u, v} X))).mapHomologicalComplex (.up ℤ)).map
        ((adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X f)).hom.app P) ≫
      (adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X g)).hom.app
        (((change (adicFiniteConstantMap f
          (smallModelComparisonEtaleTopology.{u, v} X))).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((adicFiniteOrdinaryPullback.{u, v} X C).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (adicOrdinaryChangeComp
            (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantMap g (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantComp _ f g h e)) (.up ℤ)).hom.app P) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact adicOrdinaryComparison_composition X f g h e (P.X q)

attribute [local irreducible] Functor.mapHomologicalComplex

private theorem comparison_on_good (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f)
    (P : Cx (constant (smallModelComparisonEtaleTopology.{u, v} X) A))
    (hp : AdicFiniteGood _ P) :
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
        f g h e).hom.app ((adicFinitePullback.{u, v} X A).obj ((Q _).obj P)) ≫
      (adicFiniteComparison.{u, v} X h).hom.app ((Q _).obj P) =
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) g).map
        ((adicFiniteComparison.{u, v} X f).hom.app ((Q _).obj P)) ≫
      (adicFiniteComparison.{u, v} X g).hom.app
        ((adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) f).obj
          ((Q _).obj P)) ≫
      (adicFinitePullback.{u, v} X C).map
        ((adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
          f g h e).hom.app ((Q _).obj P)) := by
  let fe := adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)
  let ge := adicFiniteConstantMap g (smallModelComparisonEtaleTopology.{u, v} X)
  let he := adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X)
  let fp := adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)
  let gp := adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X)
  let hh := adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X)
  have hk : P.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.kflat
  have hfe := adicFiniteGood_change fe P hp
  have hkfe := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr hfe.kflat
  let : PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) :=
    smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  have hpa := adicFiniteGood_pull (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A) P hp
  have hkpa := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr hpa.kflat
  let := adicFiniteExtension_isIso he P hp.kflat
  let : IsIso ((adicFinitePullbackComparison.{u, v} X C).app
      (((change he).mapHomologicalComplex (.up ℤ)).obj P)) :=
    adicFinitePull_isIso (adicFinitePullbackData.{u, v} X C) _
      (adicFiniteGood_change he P hp)
  exact paste_comparisons
    (Q (constant (smallModelComparisonEtaleTopology.{u, v} X) A))
    (Q (constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (Q (constant (smallModelComparisonEtaleTopology.{u, v} X) C))
    (Q (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (Q (constant (coefficientProEtaleModelTopology.{u, v} X) B))
    (Q (constant (coefficientProEtaleModelTopology.{u, v} X) C))
    ((change fe).mapHomologicalComplex (.up ℤ))
    ((change ge).mapHomologicalComplex (.up ℤ))
    ((change he).mapHomologicalComplex (.up ℤ))
    ((change fp).mapHomologicalComplex (.up ℤ))
    ((change gp).mapHomologicalComplex (.up ℤ))
    ((change hh).mapHomologicalComplex (.up ℤ))
    ((adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (.up ℤ))
    ((adicFiniteOrdinaryPullback.{u, v} X B).mapHomologicalComplex (.up ℤ))
    ((adicFiniteOrdinaryPullback.{u, v} X C).mapHomologicalComplex (.up ℤ))
    (extend fe) (extend ge) (extend he) (extend fp) (extend gp) (extend hh)
    (adicFinitePullback.{u, v} X A) (adicFinitePullback.{u, v} X B)
    (adicFinitePullback.{u, v} X C)
    (extendComparison fe) (extendComparison ge) (extendComparison he)
    (extendComparison fp) (extendComparison gp) (extendComparison hh)
    (adicFinitePullbackComparison.{u, v} X A) (adicFinitePullbackComparison.{u, v} X B)
    (adicFinitePullbackComparison.{u, v} X C)
    (Functor.mapHomologicalComplexCompIso
      (adicOrdinaryChangeComp fe ge he (adicFiniteConstantComp _ f g h e)) (.up ℤ))
    (Functor.mapHomologicalComplexCompIso
      (adicOrdinaryChangeComp fp gp hh (adicFiniteConstantComp _ f g h e)) (.up ℤ))
    (adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X f))
    (adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X g))
    (adicFiniteComplexSquare (adicFiniteOrdinaryComparison.{u, v} X h))
    (adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X) f g h e)
    (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X) f g h e)
    (adicFiniteComparison.{u, v} X f) (adicFiniteComparison.{u, v} X g)
    (adicFiniteComparison.{u, v} X h) P
    (specified_extend_formula fe ge he (adicFiniteConstantComp _ f g h e) P hk)
    (specified_extend_formula fp gp hh (adicFiniteConstantComp _ f g h e) _ hkpa)
    ((adicFiniteComparison_existsUnique.{u, v} X f).exists.choose_spec P hk hp.flat)
    ((adicFiniteComparison_existsUnique.{u, v} X g).exists.choose_spec _ hkfe hfe.flat)
    ((adicFiniteComparison_existsUnique.{u, v} X h).exists.choose_spec P hk hp.flat)
    (complex_composition X f g h e P)

private theorem comparison_hom (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    Functor.whiskerLeft (adicFinitePullback.{u, v} X A)
        (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
          f g h e).hom ≫ (adicFiniteComparison.{u, v} X h).hom =
      Functor.whiskerRight (adicFiniteComparison.{u, v} X f).hom
          (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) g) ≫
        Functor.whiskerLeft
          (adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) f)
          (adicFiniteComparison.{u, v} X g).hom ≫
        Functor.whiskerRight
          (adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
            f g h e).hom (adicFinitePullback.{u, v} X C) := by
  let R := constant (smallModelComparisonEtaleTopology.{u, v} X) A
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  apply resolving_nat_ext (AdicFiniteGood R) adicFiniteGood_resolution
  intro P hp
  exact comparison_on_good X f g h e P hp

private theorem inverse_paste {C : Type*} [Category C]
    {V W U S T : C} (a : V ≅ W) (b : W ≅ T) (c : V ≅ U)
    (d : U ≅ S) (e : S ≅ T)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    e.hom ≫ b.inv = d.inv ≫ c.inv ≫ a.hom := by
  apply (cancel_epi d.hom).mp
  apply (cancel_epi c.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  calc
    _ = (a.hom ≫ b.hom) ≫ b.inv := by
      simpa only [Category.assoc] using congrArg (· ≫ b.inv) h.symm
    _ = _ := by simp

/-- Comparison with geometric inverse image respects a composite scalar extension.
Source: Stacks Project, Tags 06YY, 0G7E and 09AL; the normalized comparison
calculation in parent proof steps 3 and 4.
(auxiliary; not a blueprint node).

Proof: take a flat-term K-flat representative P of K. Its scalar extensions
and geometric pullbacks are again flat-term K-flat, so all computation maps
in adicFiniteComparisonFormula and adicFiniteExtendCompFormula are invertible.
Substitute those formulas into both sides and cancel the computation maps.
The remaining ordinary comparison commutes with scalar composition: both
maps are the unique module inverse-image/scalar-extension map carrying
successive tensor insertions to the same insertion. Equivalently, on local
pure tensors both send ((p tensor x) tensor y) to the inverse image of p
tensor g(x)*y. The specified ring-map equality identifies the final scalar
action. Equality after sheafification and localization gives the formula on
P. Every K has such a representative, so naturality proves the assertion.
This applies to arbitrary rings and maps, including identity maps. -/
theorem adicComparison_composition (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f)
    (K : ConstantCompletion.D (constant (smallModelComparisonEtaleTopology.{u, v} X) A)) :
    (adicFinitePullback.{u, v} X C).map
        ((adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
          f g h e).hom.app K) ≫ (adicFiniteComparison.{u, v} X h).inv.app K =
      (adicFiniteComparison.{u, v} X g).inv.app
          ((adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) f).obj K) ≫
        (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) g).map
          ((adicFiniteComparison.{u, v} X f).inv.app K) ≫
        (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
          f g h e).hom.app ((adicFinitePullback.{u, v} X A).obj K) := by
  have hh := congr_app (comparison_hom X f g h e) K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
  exact inverse_paste
    ((adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
      f g h e).app ((adicFinitePullback.{u, v} X A).obj K))
    ((adicFiniteComparison.{u, v} X h).app K)
    ((adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X) g).mapIso
      ((adicFiniteComparison.{u, v} X f).app K))
    ((adicFiniteComparison.{u, v} X g).app
      ((adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) f).obj K))
    ((adicFinitePullback.{u, v} X C).mapIso
      ((adicFiniteExtensionComp (smallModelComparisonEtaleTopology.{u, v} X)
        f g h e).app K)) hh

end AlgebraicGeometry.Scheme
