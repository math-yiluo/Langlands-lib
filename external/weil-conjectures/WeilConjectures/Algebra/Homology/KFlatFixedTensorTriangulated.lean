/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization

/-!
# Exact descent of tensoring with a fixed K-flat complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP and 06YU;
derived.tex, definition-cone and definition-distinguished-triangle;
more-algebra.tex, Tag 0FNH, item-shift-tensor.
(auxiliary; not a blueprint node)

The derived bifunctor and its resolving comparison are the ones already supplied
by site-derived-tensor descent. The presentation packages the existing choices once,
so its dependent comparisons share the same checked data. `derivedTensor_eq_published`
records their equality. All site and coefficient universes remain independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules.KFlatFixedTensor

section Generic

section CanonicalShift

attribute [local instance 2000] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj

private theorem canonicalLocalizedShift_obj_eq
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : A ⥤ B) (W : MorphismProperty A) [W.ContainsIdentities]
    [L.IsLocalization W] [L.CommShift ℤ]
    (F : A ⥤ A ⥤ E) [F.CommShift₂Int] (G : B ⥤ B ⥤ E)
    [Localization.Lifting₂ L L W W F G] (hsurj : Function.Surjective L.obj)
    (SO : ∀ X, (G.obj X).CommShift ℤ)
    (hO : ∀ X, letI := SO (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.obj (L.obj X) ≅ F.obj X from
          (Localization.Lifting₂.iso L L W W F G).app X).hom ℤ)
    (X : B) :
    (Functor.commShift₂OfLocalization L L W W F G .int).commShiftObj X = SO X := by
  obtain ⟨Y, rfl⟩ := hsurj X
  apply Functor.CommShift.eq_of_natTransCommShift L W _ _
    (show L ⋙ G.obj (L.obj Y) ≅ F.obj Y from
      (Localization.Lifting₂.iso L L W W F G).app Y)
  · exact Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L W W F G Y
  · exact hO Y

private theorem canonicalLocalizedShift_flip_eq
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : A ⥤ B) (W : MorphismProperty A) [W.ContainsIdentities]
    [L.IsLocalization W] [L.CommShift ℤ]
    (F : A ⥤ A ⥤ E) [F.CommShift₂Int] (G : B ⥤ B ⥤ E)
    [Localization.Lifting₂ L L W W F G] (hsurj : Function.Surjective L.obj)
    (SF : ∀ X, (G.flip.obj X).CommShift ℤ)
    (hF : ∀ X, letI := SF (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.flip.obj (L.obj X) ≅ F.flip.obj X from
          (Localization.Lifting₂.iso L L W W F.flip G.flip).app X).hom ℤ)
    (X : B) :
    (Functor.commShift₂OfLocalization L L W W F G .int).commShiftFlipObj X = SF X := by
  obtain ⟨Y, rfl⟩ := hsurj X
  apply Functor.CommShift.eq_of_natTransCommShift L W _ _
    (show L ⋙ G.flip.obj (L.obj Y) ≅ F.flip.obj Y from
      (Localization.Lifting₂.iso L L W W F.flip G.flip).app Y)
  · exact Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L W W F.flip G.flip Y
  · exact hF Y

@[instance_reducible] private def replaceBifunctorShift
    {B E : Type*} [Category* B] [Category* E] [HasShift B ℤ] [HasShift E ℤ]
    [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive]
    (G : B ⥤ B ⥤ E) (s : G.CommShift₂Int)
    (SO : ∀ X, (G.obj X).CommShift ℤ) (SF : ∀ X, (G.flip.obj X).CommShift ℤ)
    (eO : ∀ X, s.commShiftObj X = SO X) (eF : ∀ X, s.commShiftFlipObj X = SF X) :
    G.CommShift₂Int where
  commShiftObj := SO
  commShiftFlipObj := SF
  commShift_map := by
    intro X Y f
    have h := s.commShift_map f
    rw [eO X, eO Y] at h
    exact h
  commShift_flip_map := by
    intro X Y f
    have h := s.commShift_flip_map f
    rw [eF X, eF Y] at h
    exact h
  comm := by
    intro X Y m n
    have h := s.comm X Y m n
    rw [eO, eF, eO, eF] at h
    exact h

@[instance_reducible] private def canonicalLocalizedShift
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    (L : A ⥤ B) (W : MorphismProperty A) [W.ContainsIdentities]
    [L.IsLocalization W] [L.CommShift ℤ]
    (F : A ⥤ A ⥤ E) [F.CommShift₂Int] (G : B ⥤ B ⥤ E)
    [Localization.Lifting₂ L L W W F G] (hsurj : Function.Surjective L.obj)
    (SO : ∀ X, (G.obj X).CommShift ℤ) (SF : ∀ X, (G.flip.obj X).CommShift ℤ)
    (hO : ∀ X, letI := SO (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.obj (L.obj X) ≅ F.obj X from
          (Localization.Lifting₂.iso L L W W F G).app X).hom ℤ)
    (hF : ∀ X, letI := SF (L.obj X)
      NatTrans.CommShift
        (show L ⋙ G.flip.obj (L.obj X) ≅ F.flip.obj X from
          (Localization.Lifting₂.iso L L W W F.flip G.flip).app X).hom ℤ) :
    G.CommShift₂Int :=
  replaceBifunctorShift G (Functor.commShift₂OfLocalization L L W W F G .int) SO SF
    (canonicalLocalizedShift_obj_eq L W F G hsurj SO hO)
    (canonicalLocalizedShift_flip_eq L W F G hsurj SF hF)

section HomotopyShift
variable {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

private abbrev homotopyBifunctor := T.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)
private abbrev chainHomotopyBifunctor := T.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj
  (HomotopyCategory.quotient M (.up ℤ))

@[instance_reducible] private def chainHomotopyBifunctorShift :
    (chainHomotopyBifunctor T).CommShift₂Int :=
  Functor.CommShift₂.postcompInt T.map₂CochainComplex (HomotopyCategory.quotient M (.up ℤ))

@[instance_reducible] private def bifunctorHomotopyLifting :
    Localization.Lifting₂ (HomotopyCategory.quotient M (.up ℤ))
      (HomotopyCategory.quotient M (.up ℤ))
      (HomologicalComplex.homotopyEquivalences M (.up ℤ))
      (HomologicalComplex.homotopyEquivalences M (.up ℤ))
      (chainHomotopyBifunctor T) (homotopyBifunctor T) :=
  ⟨T.whiskeringLeft₂BifunctorMapHomotopyCategoryIso (.up ℤ) (.up ℤ) (.up ℤ)⟩

@[instance_reducible] private def bifunctorHomotopyShift : (homotopyBifunctor T).CommShift₂Int := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let W := HomologicalComplex.homotopyEquivalences M (.up ℤ)
  let : (chainHomotopyBifunctor T).CommShift₂Int := chainHomotopyBifunctorShift T
  let : Localization.Lifting₂ q q W W (chainHomotopyBifunctor T) (homotopyBifunctor T) :=
    bifunctorHomotopyLifting T
  apply canonicalLocalizedShift q W (chainHomotopyBifunctor T) (homotopyBifunctor T)
    (fun X ↦ X.quotient_obj_surjective) (fun X ↦ inferInstance) (fun X ↦ inferInstance)
  · intro A
    exact inferInstanceAs (NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)
  · intro A
    exact inferInstanceAs (NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ)

private theorem bifunctorHomotopyShift_triangulated [HasZeroObject M]
    (X : HomotopyCategory M (.up ℤ)) :
    letI := bifunctorHomotopyShift T
    ((homotopyBifunctor T).obj X).IsTriangulated ∧
      ((homotopyBifunctor T).flip.obj X).IsTriangulated := by
  constructor <;> infer_instance

private theorem bifunctorHomotopyShift_compatR (A : CochainComplex M ℤ) :
    letI := bifunctorHomotopyShift T
    NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ := by
  infer_instance
private theorem bifunctorHomotopyShift_compatL (A : CochainComplex M ℤ) :
    letI := bifunctorHomotopyShift T
    NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ := by
  infer_instance

end HomotopyShift

end CanonicalShift

private def homotopyComparisonGeneric
    {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M] [HasZeroObject M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (B : HomotopyCategory M (.up ℤ) × HomotopyCategory M (.up ℤ) ⥤
      HomotopyCategory M (.up ℤ))
    (c : ((HomotopyCategory.quotient M (.up ℤ)).prod
        (HomotopyCategory.quotient M (.up ℤ))) ⋙ B ≅
      Functor.uncurry.obj T.map₂CochainComplex ⋙ HomotopyCategory.quotient M (.up ℤ)) :
    Functor.uncurry.obj (T.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)) ≅ B := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  refine NatIso.ofComponents (fun X ↦ c.symm.app (X.1.as, X.2.as)) ?_
  rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
  obtain ⟨g₁, rfl⟩ := q.map_surjective
    (show q.obj X₁.as ⟶ q.obj Y₁.as from f₁)
  obtain ⟨g₂, rfl⟩ := q.map_surjective
    (show q.obj X₂.as ⟶ q.obj Y₂.as from f₂)
  exact c.inv.naturality (CategoryTheory.Prod.mkHom g₁ g₂)

private theorem extendComparison
    {H P D E : Type*} [Category* H] [Category* P] [Category* D] [Category* E]
    (I : P ⥤ H) (Q : H ⥤ D) (W : MorphismProperty H)
    [Q.IsLocalization W] [(I ⋙ Q).IsLocalization (W.inverseImage I)]
    (F : H ⥤ E) (G : D ⥤ E) (hF : W.IsInvertedBy F)
    (e : I ⋙ F ≅ (I ⋙ Q) ⋙ G) :
    ∃ c : F ≅ Q ⋙ G, ∀ X : P, c.app (I.obj X) = e.app X := by
  let K := Localization.lift F hF Q
  let k := Localization.fac F hF Q
  let t : (I ⋙ Q) ⋙ K ≅ (I ⋙ Q) ⋙ G :=
    Functor.associator I Q K ≪≫ Functor.isoWhiskerLeft I k ≪≫ e
  let d : K ≅ G := Localization.liftNatIso (I ⋙ Q) (W.inverseImage I) _ _ K G t
  refine ⟨k.symm ≪≫ Functor.isoWhiskerLeft Q d, ?_⟩
  intro X
  apply Iso.ext
  have hd : d.hom.app (Q.obj (I.obj X)) = t.hom.app X := by
    change (Localization.liftNatTrans (I ⋙ Q) (W.inverseImage I)
      ((I ⋙ Q) ⋙ K) ((I ⋙ Q) ⋙ G) K G t.hom).app ((I ⋙ Q).obj X) = _
    rw [Localization.liftNatTrans_app]
    simp
  change k.inv.app (I.obj X) ≫ d.hom.app (Q.obj (I.obj X)) = e.hom.app X
  rw [hd]
  simp [t]

private theorem extendComparison_commShift
    {H P D E : Type*} [Category* H] [Category* P] [Category* D] [Category* E]
    [HasShift H ℤ] [HasShift P ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (I : P ⥤ H) (Q : H ⥤ D) (W : MorphismProperty H)
    [Q.IsLocalization W] [(I ⋙ Q).IsLocalization (W.inverseImage I)]
    [I.CommShift ℤ] [Q.CommShift ℤ]
    (F : H ⥤ E) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    (c : F ≅ Q ⋙ G) (e : I ⋙ F ≅ (I ⋙ Q) ⋙ G)
    (hc : ∀ X, c.app (I.obj X) = e.app X) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift c.hom ℤ := by
  let S₁ : G.CommShift ℤ := inferInstance
  have h₁ : NatTrans.CommShift e.symm.hom ℤ := by infer_instance
  let : Localization.Lifting Q W F G := ⟨c.symm⟩
  let S := Functor.commShiftOfLocalization Q W ℤ F G
  have he : e = Functor.isoWhiskerLeft I c ≪≫ (Functor.associator I Q G).symm := by
    ext X
    simpa using congrArg Iso.hom (hc X).symm
  have hS : letI := S; NatTrans.CommShift e.symm.hom ℤ := by
    let := S
    have hs : NatTrans.CommShift c.symm.hom ℤ :=
      NatTrans.commShift_iso_hom_of_localization Q W ℤ F G
    have : NatTrans.CommShift c.inv ℤ := hs
    have hi : NatTrans.CommShift (Functor.whiskerLeft I c.inv) ℤ := by infer_instance
    have ha : NatTrans.CommShift (Functor.associator I Q G).hom ℤ := by infer_instance
    rw [he]
    change NatTrans.CommShift ((Functor.associator I Q G).hom ≫
      Functor.whiskerLeft I c.inv) ℤ
    exact NatTrans.CommShift.comp _ _ ℤ
  have heq : S₁ = S :=
    Functor.CommShift.eq_of_natTransCommShift (I ⋙ Q) (W.inverseImage I)
      S₁ S e.symm h₁ hS
  have h : letI := S; NatTrans.CommShift c.hom ℤ := by
    let := S
    have hs : NatTrans.CommShift c.symm.hom ℤ :=
      NatTrans.commShift_iso_hom_of_localization Q W ℤ F G
    have : NatTrans.CommShift c.inv ℤ := hs
    exact NatTrans.CommShift.of_iso_inv c.symm ℤ
  rw [← heq] at h
  exact h

private theorem descendBifunctor
    {H D : Type*} [Category* H] [Category* D]
    [Preadditive H] [Preadditive D] [HasShift H ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor H n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [HasZeroObject H] [HasZeroObject D] [Pretriangulated H] [Pretriangulated D]
    (Q : H ⥤ D) (W : MorphismProperty H) [W.ContainsIdentities]
    [Q.IsLocalization W] [Q.CommShift ℤ] [Q.IsTriangulated] [Q.mapArrow.EssSurj]
    (P : ObjectProperty H) [P.IsStableUnderShift ℤ]
    [(P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι)]
    (T : H ⥤ H ⥤ H) [T.CommShift₂Int] (G : D ⥤ D ⥤ D)
    (e : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj T ⋙ Q ≅
      ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ Functor.uncurry.obj G)
    (hinv : ∀ a : P.FullSubcategory, W.IsInvertedBy (T.obj a.obj ⋙ Q) ∧
      W.IsInvertedBy (T.flip.obj a.obj ⋙ Q))
    (htri : ∀ X : H, (T.obj X).IsTriangulated ∧ (T.flip.obj X).IsTriangulated) :
    ∃ _s : G.CommShift₂Int, ∀ a : P.FullSubcategory,
      ((G.obj (Q.obj a.obj)).IsTriangulated ∧
        (G.flip.obj (Q.obj a.obj)).IsTriangulated) ∧
      (∃ cL : T.obj a.obj ⋙ Q ≅ Q ⋙ G.obj (Q.obj a.obj),
        NatTrans.CommShift cL.hom ℤ ∧ ∀ b : P.FullSubcategory, cL.app b.obj = e.app (a, b)) ∧
      (∃ cR : T.flip.obj a.obj ⋙ Q ≅ Q ⋙ G.flip.obj (Q.obj a.obj),
        NatTrans.CommShift cR.hom ℤ ∧ ∀ b : P.FullSubcategory, cR.app b.obj = e.app (b, a)) := by
  let I := P.ι
  let L := I ⋙ Q
  let V := W.inverseImage I
  let F := I ⋙ T ⋙ (Functor.whiskeringLeft _ _ _).obj I ⋙
    (Functor.whiskeringRight _ _ _).obj Q
  let : F.CommShift₂Int := Functor.CommShift₂.postcompInt
    (I ⋙ T ⋙ (Functor.whiskeringLeft _ _ _).obj I) Q
  let : Localization.Lifting₂ L L V V F G :=
    ⟨NatIso.ofComponents (fun a ↦ NatIso.ofComponents
      (fun b ↦ e.symm.app (a, b)) (fun f ↦ by
        simpa [F, L, I] using e.inv.naturality (CategoryTheory.Prod.mkHom (𝟙 a) f))) (fun f ↦ by
          ext b
          simpa [F, L, I] using e.inv.naturality (CategoryTheory.Prod.mkHom f (𝟙 b)))⟩
  let s : G.CommShift₂Int := Functor.commShift₂OfLocalization L L V V F G .int
  refine ⟨s, fun a ↦ ?_⟩
  let GL := G.obj (Q.obj a.obj)
  let GR := G.flip.obj (Q.obj a.obj)
  let eL0 : (I ⋙ T.obj a.obj) ⋙ Q ≅ L ⋙ GL :=
    ((Localization.Lifting₂.iso L L V V F G).app a).symm
  let eR0 : (I ⋙ T.flip.obj a.obj) ⋙ Q ≅ L ⋙ GR :=
    ((Localization.Lifting₂.iso L L V V F.flip G.flip).app a).symm
  let eL : I ⋙ (T.obj a.obj ⋙ Q) ≅ L ⋙ GL :=
    (Functor.associator I (T.obj a.obj) Q).symm ≪≫ eL0
  let eR : I ⋙ (T.flip.obj a.obj ⋙ Q) ≅ L ⋙ GR :=
    (Functor.associator I (T.flip.obj a.obj) Q).symm ≪≫ eR0
  obtain ⟨cL, hcL⟩ := extendComparison I Q W (T.obj a.obj ⋙ Q) GL (hinv a).1 eL
  obtain ⟨cR, hcR⟩ := extendComparison I Q W (T.flip.obj a.obj ⋙ Q) GR (hinv a).2 eR
  have hL0 : NatTrans.CommShift eL0.inv ℤ :=
    Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L V V F G a
  have hR0 : NatTrans.CommShift eR0.inv ℤ :=
    Functor.CommShift₂OfLocalization.commShift_liftingIsoApp L L V V F.flip G.flip a
  have : NatTrans.CommShift eL0.hom ℤ := by
    have : NatTrans.CommShift eL0.symm.hom ℤ := hL0
    exact NatTrans.CommShift.of_iso_inv eL0.symm ℤ
  have : NatTrans.CommShift eR0.hom ℤ := by
    have : NatTrans.CommShift eR0.symm.hom ℤ := hR0
    exact NatTrans.CommShift.of_iso_inv eR0.symm ℤ
  have : NatTrans.CommShift eL.hom ℤ := by dsimp [eL]; infer_instance
  have : NatTrans.CommShift eR.hom ℤ := by dsimp [eR]; infer_instance
  have : NatTrans.CommShift cL.hom ℤ := extendComparison_commShift I Q W _ _ cL eL hcL
  have : NatTrans.CommShift cR.hom ℤ := extendComparison_commShift I Q W _ _ cR eR hcR
  have : (T.obj a.obj).IsTriangulated := (htri a.obj).1
  have : (T.flip.obj a.obj).IsTriangulated := (htri a.obj).2
  refine ⟨⟨Functor.isTriangulated_of_precomp_iso cL.symm,
    Functor.isTriangulated_of_precomp_iso cR.symm⟩, ⟨cL, inferInstance, ?_⟩,
    ⟨cR, inferInstance, ?_⟩⟩
  · intro b
    apply Iso.ext
    have h := congrArg Iso.hom (hcL b)
    change cL.hom.app b.obj = 𝟙 _ ≫ e.hom.app (a, b) at h
    simpa using h
  · intro b
    apply Iso.ext
    have h := congrArg Iso.hom (hcR b)
    change cR.hom.app b.obj = 𝟙 _ ≫ e.hom.app (b, a) at h
    simpa using h

private def chainComparison
    {A H D : Type*} [Category* A] [Category* H] [Category* D]
    (q : A ⥤ H) (Q : H ⥤ D) (Q0 : A ⥤ D) (F : A ⥤ A) (K : H ⥤ H) (G : D ⥤ D)
    (e : q ⋙ Q ≅ Q0) (t : q ⋙ K ≅ F ⋙ q) (c : K ⋙ Q ≅ Q ⋙ G) :
    F ⋙ Q0 ≅ Q0 ⋙ G :=
  Functor.isoWhiskerLeft F e.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight t.symm Q ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft q c ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e G

private theorem chainComparison_commShift
    {A H D : Type*} [Category* A] [Category* H] [Category* D]
    [HasShift A ℤ] [HasShift H ℤ] [HasShift D ℤ]
    (q : A ⥤ H) (Q : H ⥤ D) (Q0 : A ⥤ D) (F : A ⥤ A) (K : H ⥤ H) (G : D ⥤ D)
    [q.CommShift ℤ] [Q.CommShift ℤ] [Q0.CommShift ℤ]
    [F.CommShift ℤ] [K.CommShift ℤ] [G.CommShift ℤ]
    (e : q ⋙ Q ≅ Q0) (t : q ⋙ K ≅ F ⋙ q) (c : K ⋙ Q ≅ Q ⋙ G)
    [NatTrans.CommShift e.hom ℤ] [NatTrans.CommShift t.hom ℤ]
    [NatTrans.CommShift c.hom ℤ] :
    NatTrans.CommShift (chainComparison q Q Q0 F K G e t c).hom ℤ := by
  dsimp [chainComparison]
  infer_instance

private theorem chainComparison_app
    {A H D : Type*} [Category* A] [Category* H] [Category* D]
    (q : A ⥤ H) (Q : H ⥤ D) (Q0 : A ⥤ D) (F : A ⥤ A) (K : H ⥤ H) (G : D ⥤ D)
    (e : q ⋙ Q ≅ Q0) (t : q ⋙ K ≅ F ⋙ q) (c : K ⋙ Q ≅ Q ⋙ G) (X : A) :
    (chainComparison q Q Q0 F K G e t c).hom.app X =
      e.inv.app (F.obj X) ≫ Q.map (t.inv.app X) ≫ c.hom.app (q.obj X) ≫
        G.map (e.hom.app X) := by
  simp [chainComparison]
private theorem inverts_via_full
    {A H D : Type*} [Category* A] [Category* H] [Category* D]
    (q : A ⥤ H) [q.Full] (hq : Function.Surjective q.obj)
    (Q : H ⥤ D) (W : MorphismProperty H) (hQ : W.IsInvertedBy Q)
    (F : A ⥤ A) (K : H ⥤ H) (t : q ⋙ K ≅ F ⋙ q)
    (hF : ∀ {X Y : A} (f : X ⟶ Y), W (q.map f) → W (q.map (F.map f))) :
    W.IsInvertedBy (K ⋙ Q) := by
  intro X Y f hf
  obtain ⟨X, rfl⟩ := hq X
  obtain ⟨Y, rfl⟩ := hq Y
  obtain ⟨g, rfl⟩ := q.map_surjective f
  have hg : IsIso (Q.map (q.map (F.map g))) := hQ _ (hF g hf)
  let e : (q ⋙ K) ⋙ Q ≅ F ⋙ q ⋙ Q :=
    Functor.isoWhiskerRight t Q ≪≫ Functor.associator F q Q
  exact (NatIso.isIso_map_iff e g).2 hg

private def mapDoubleNatIso
    {M : Type*} [Category* M] [HasZeroMorphisms M]
    {T S : M ⥤ M ⥤ M} [T.PreservesZeroMorphisms]
    [∀ X, (T.obj X).PreservesZeroMorphisms] [S.PreservesZeroMorphisms]
    [∀ X, (S.obj X).PreservesZeroMorphisms]
    (β : T ≅ S) (E A : CochainComplex M ℤ) :
    (((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj E).obj A) ≅
      (((S.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj E).obj A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ (β.app (E.X p)).app (A.X q)) (by
        intro q q' hqq'
        exact ((β.app (E.X p)).hom.naturality (A.d q q')).symm)) (by
      intro p p' hpp'
      ext q : 1
      exact (NatTrans.congr_app (β.hom.naturality (E.d p p')) (A.X q)).symm)

private theorem tensor_quasiIso_generic
    {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
    [CategoryWithHomology M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (hcone : ∀ {B B' : CochainComplex M ℤ} (f : B ⟶ B'),
      QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic)
    (β : T ≅ T.flip) (A : CochainComplex M ℤ)
    (hA : ∀ E : CochainComplex M ℤ, E.Acyclic →
      (CochainComplex.mapBifunctor E A T).Acyclic)
    {B B' : CochainComplex M ℤ} (f : B ⟶ B') (hf : QuasiIso f) :
    QuasiIso ((T.map₂CochainComplex.obj A).map f) ∧
      QuasiIso ((T.map₂CochainComplex.flip.obj A).map f) := by
  let E := CochainComplex.mappingCone f
  have hc := hA E ((hcone f).1 hf)
  let e := mapDoubleNatIso β E A
  have hcL : (CochainComplex.mapBifunctor A E T).Acyclic := by
    intro i
    exact (hc i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso A E T (.up ℤ))
  constructor
  · apply (hcone _).2
    intro i
    exact (hcL i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso A f T)
  · apply (hcone _).2
    intro i
    exact (hc i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f A T)

section HomotopyShiftData

attribute [local instance 2000] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj

private structure HomotopyTensorShiftData
    {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M] [HasZeroObject M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T] where
  shift : (homotopyBifunctor T).CommShift₂Int
  triangulated : letI := shift
    ∀ X, ((homotopyBifunctor T).obj X).IsTriangulated ∧
      ((homotopyBifunctor T).flip.obj X).IsTriangulated
  compatL : letI := shift
    ∀ A, NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ
  compatR : letI := shift
    ∀ A, NatTrans.CommShift
      (T.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) A).hom ℤ

private def homotopyTensorShiftData
    {M : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M] [HasZeroObject M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T] :
    HomotopyTensorShiftData T where
  shift := bifunctorHomotopyShift T
  triangulated := bifunctorHomotopyShift_triangulated T
  compatL := bifunctorHomotopyShift_compatL T
  compatR := bifunctorHomotopyShift_compatR T

end HomotopyShiftData

private theorem descendCochainBifunctor
    {M D : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
    [HasZeroObject M] [Category* D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (hT : HomotopyTensorShiftData T)
    (Q : HomotopyCategory M (.up ℤ) ⥤ D)
    (W : MorphismProperty (HomotopyCategory M (.up ℤ))) [W.ContainsIdentities]
    [Q.IsLocalization W] [Q.CommShift ℤ] [Q.IsTriangulated] [Q.mapArrow.EssSurj]
    (Q₀ : CochainComplex M ℤ ⥤ D) [Q₀.CommShift ℤ]
    (eQ : HomotopyCategory.quotient M (.up ℤ) ⋙ Q ≅ Q₀)
    [NatTrans.CommShift eQ.hom ℤ]
    (hcone : ∀ {B B' : CochainComplex M ℤ} (f : B ⟶ B'),
      Q₀.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ∈ distTriang D)
    (P : ObjectProperty (HomotopyCategory M (.up ℤ))) [P.IsStableUnderShift ℤ]
    [(P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι)] (G : D ⥤ D ⥤ D)
    (e : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj (homotopyBifunctor T) ⋙ Q ≅
      ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ Functor.uncurry.obj G)
    (hinv : ∀ a : P.FullSubcategory,
      W.IsInvertedBy ((homotopyBifunctor T).obj a.obj ⋙ Q) ∧
      W.IsInvertedBy ((homotopyBifunctor T).flip.obj a.obj ⋙ Q)) :
    ∃ _s : G.CommShift₂Int, ∀ (A : CochainComplex M ℤ)
      (hA : P ((HomotopyCategory.quotient M (.up ℤ)).obj A)),
      ((G.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).IsTriangulated ∧
        (G.flip.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).IsTriangulated) ∧
      (∃ cL : T.map₂CochainComplex.obj A ⋙ Q₀ ≅ Q₀ ⋙
          G.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A)),
        NatTrans.CommShift cL.hom ℤ ∧ ∀ (B : CochainComplex M ℤ)
          (hB : P ((HomotopyCategory.quotient M (.up ℤ)).obj B)),
          cL.app B = (eQ.app ((T.map₂CochainComplex.obj A).obj B)).symm ≪≫
            (Q.mapIso ((T.quotientCompBifunctorMapHomotopyObjIso
              (.up ℤ) (.up ℤ) (.up ℤ) A).app B)).symm ≪≫
            e.app (⟨_, hA⟩, ⟨_, hB⟩) ≪≫
            (G.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).mapIso (eQ.app B)) ∧
      (∃ cR : T.map₂CochainComplex.flip.obj A ⋙ Q₀ ≅ Q₀ ⋙
          G.flip.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A)),
        NatTrans.CommShift cR.hom ℤ ∧ ∀ (B : CochainComplex M ℤ)
          (hB : P ((HomotopyCategory.quotient M (.up ℤ)).obj B)),
          cR.app B = (eQ.app ((T.map₂CochainComplex.flip.obj A).obj B)).symm ≪≫
            (Q.mapIso ((T.quotientCompBifunctorMapHomotopyFlipObjIso
              (.up ℤ) (.up ℤ) (.up ℤ) A).app B)).symm ≪≫
            e.app (⟨_, hB⟩, ⟨_, hA⟩) ≪≫
            (G.flip.obj
              (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).mapIso (eQ.app B)) ∧
      (∀ {B B' : CochainComplex M ℤ} (f : B ⟶ B'),
        (G.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).mapTriangle.obj
          (Q₀.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) ∈ distTriang D ∧
        (G.flip.obj (Q.obj ((HomotopyCategory.quotient M (.up ℤ)).obj A))).mapTriangle.obj
          (Q₀.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) ∈ distTriang D) := by
  let : (homotopyBifunctor T).CommShift₂Int := hT.shift
  let : ∀ X, ((homotopyBifunctor T).obj X).CommShift ℤ := hT.shift.commShiftObj
  let : ∀ X, ((homotopyBifunctor T).flip.obj X).CommShift ℤ := hT.shift.commShiftFlipObj
  obtain ⟨s, hs⟩ := descendBifunctor Q W P (homotopyBifunctor T) G e hinv
    hT.triangulated
  refine ⟨s, fun A hA ↦ ?_⟩
  let q := HomotopyCategory.quotient M (.up ℤ)
  let a : P.FullSubcategory := ⟨q.obj A, hA⟩
  obtain ⟨⟨hGL, hGR⟩, ⟨cL, hcLs, hcL⟩, ⟨cR, hcRs, hcR⟩⟩ := hs a
  let GL := G.obj (Q.obj (q.obj A))
  let GR := G.flip.obj (Q.obj (q.obj A))
  have : NatTrans.CommShift cL.hom ℤ := hcLs
  have : NatTrans.CommShift cR.hom ℤ := hcRs
  have : GL.IsTriangulated := hGL
  have : GR.IsTriangulated := hGR
  let tL := T.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) A
  let tR := T.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) A
  have : NatTrans.CommShift tL.hom ℤ := hT.compatL A
  have : NatTrans.CommShift tR.hom ℤ := hT.compatR A
  let chainL := chainComparison q Q Q₀ (T.map₂CochainComplex.obj A)
    ((homotopyBifunctor T).obj a.obj) GL eQ tL cL
  let chainR := chainComparison q Q Q₀ (T.map₂CochainComplex.flip.obj A)
    ((homotopyBifunctor T).flip.obj a.obj) GR eQ tR cR
  have hcL' : NatTrans.CommShift chainL.hom ℤ :=
    chainComparison_commShift _ _ _ _ _ _ _ _ _
  have hcR' : NatTrans.CommShift chainR.hom ℤ :=
    chainComparison_commShift _ _ _ _ _ _ _ _ _
  refine ⟨⟨hGL, hGR⟩, ⟨chainL, hcL', ?_⟩, ⟨chainR, hcR', ?_⟩, ?_⟩
  · intro B hB
    let b : P.FullSubcategory := ⟨q.obj B, hB⟩
    apply Iso.ext
    change (chainComparison _ _ _ _ _ _ _ _ _).hom.app B = _
    rw [chainComparison_app]
    have h := congrArg Iso.hom (hcL b)
    change cL.hom.app (q.obj B) = e.hom.app (a, b) at h
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
          Functor.mapIso_inv, Category.assoc] using
      congrArg (fun f ↦ eQ.inv.app ((T.map₂CochainComplex.obj A).obj B) ≫
        Q.map (tL.inv.app B) ≫ f ≫ GL.map (eQ.hom.app B)) h
  · intro B hB
    let b : P.FullSubcategory := ⟨q.obj B, hB⟩
    apply Iso.ext
    change (chainComparison _ _ _ _ _ _ _ _ _).hom.app B = _
    rw [chainComparison_app]
    have h := congrArg Iso.hom (hcR b)
    change cR.hom.app (q.obj B) = e.hom.app (b, a) at h
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
          Functor.mapIso_inv, Category.assoc] using
      congrArg (fun f ↦ eQ.inv.app ((T.map₂CochainComplex.flip.obj A).obj B) ≫
        Q.map (tR.inv.app B) ≫ f ≫ GR.map (eQ.hom.app B)) h
  · intro B B' f
    exact ⟨GL.map_distinguished _ (hcone f), GR.map_distinguished _ (hcone f)⟩

private theorem homotopyBifunctor_inverts
    {M D : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
    [CategoryWithHomology M] [Category* D]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (Q : HomotopyCategory M (.up ℤ) ⥤ D)
    (hQ : (HomotopyCategory.quasiIso M (.up ℤ)).IsInvertedBy Q)
    (A : CochainComplex M ℤ)
    (hA : ∀ {B B' : CochainComplex M ℤ} (f : B ⟶ B'), QuasiIso f →
      QuasiIso ((T.map₂CochainComplex.obj A).map f) ∧
        QuasiIso ((T.map₂CochainComplex.flip.obj A).map f)) :
    (HomotopyCategory.quasiIso M (.up ℤ)).IsInvertedBy
      (((homotopyBifunctor T).obj ((HomotopyCategory.quotient _ _).obj A)) ⋙ Q) ∧
    (HomotopyCategory.quasiIso M (.up ℤ)).IsInvertedBy
      (((homotopyBifunctor T).flip.obj ((HomotopyCategory.quotient _ _).obj A)) ⋙ Q) := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  constructor
  · apply inverts_via_full q (fun X ↦ X.quotient_obj_surjective) Q W
      hQ ((T.map₂CochainComplex).obj A) _
      (T.quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) A)
    intro X Y f hf
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (hA f
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hf)).1
  · apply inverts_via_full q (fun X ↦ X.quotient_obj_surjective) Q W
      hQ ((T.map₂CochainComplex).flip.obj A) _
      (T.quotientCompBifunctorMapHomotopyFlipObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) A)
    intro X Y f hf
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (hA f
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hf)).2

/-- A tensor descent presentation: homotopy tensor, derived tensor, and their comparisons.
Packing the selected data keeps the dependent types of the comparisons shared.
Source: Stacks, Tag 06YU
(auxiliary; not a blueprint node). -/
structure TensorPresentation
    {CC H D : Type*} [Category* CC] [Category* H] [Category* D]
    (q : CC ⥤ H) (Q : H ⥤ D) (F : CC × CC ⥤ CC) (P : ObjectProperty H) where
  homotopyTensor : H × H ⥤ H
  homotopyComparison : (q.prod q) ⋙ homotopyTensor ≅ F ⋙ q
  derivedTensor : D × D ⥤ D
  resolvingComparison : (P.ι.prod P.ι) ⋙ homotopyTensor ⋙ Q ≅
    ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ derivedTensor

/-- Pack precisely the witnesses and comparisons specified by a descent theorem.
The projections reduce to the original choices, without selecting any additional object.
Source: Stacks, Tag 06YU
(auxiliary; not a blueprint node). -/
def TensorPresentation.ofExists
    {CC H D : Type*} [Category* CC] [Category* H] [Category* D]
    (q : CC ⥤ H) (Q : H ⥤ D) (F : CC × CC ⥤ CC) (P : ObjectProperty H)
    (h : ∃ B : H × H ⥤ H, Nonempty ((q.prod q) ⋙ B ≅ F ⋙ q) ∧
      ∃ T : D × D ⥤ D, Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ Q ≅
        ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ T)) : TensorPresentation q Q F P where
  homotopyTensor := h.choose
  homotopyComparison := h.choose_spec.1.some
  derivedTensor := h.choose_spec.2.choose
  resolvingComparison := h.choose_spec.2.choose_spec.some

/-- Compose the selected homotopy and resolving comparisons on a resolving pair.
This is the representative comparison in site tensor descent, expressed generically.
Source: Stacks, Tag 06YU
(auxiliary; not a blueprint node). -/
def TensorPresentation.representativeIso
    {CC H D : Type*} [Category* CC] [Category* H] [Category* D]
    {q : CC ⥤ H} {Q : H ⥤ D} {F : CC × CC ⥤ CC} {P : ObjectProperty H}
    (t : TensorPresentation q Q F P) (A B : CC) (hA : P (q.obj A)) (hB : P (q.obj B)) :
    Q.obj (q.obj (F.obj (A, B))) ≅ t.derivedTensor.obj (Q.obj (q.obj A), Q.obj (q.obj B)) :=
  (Q.mapIso (t.homotopyComparison.app (A, B))).symm ≪≫
    t.resolvingComparison.app (⟨q.obj A, hA⟩, ⟨q.obj B, hB⟩)

private def tensorPresentationComparison
    {M D : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
    [HasZeroObject M] [Category* D]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (Q : HomotopyCategory M (.up ℤ) ⥤ D)
    (P : ObjectProperty (HomotopyCategory M (.up ℤ)))
    (t : TensorPresentation (HomotopyCategory.quotient M (.up ℤ)) Q
      (Functor.uncurry.obj T.map₂CochainComplex) P) :
    (P.ι.prod P.ι) ⋙ Functor.uncurry.obj (homotopyBifunctor T) ⋙ Q ≅
      ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙
        Functor.uncurry.obj (Functor.curry.obj t.derivedTensor) :=
  Functor.isoWhiskerLeft (P.ι.prod P.ι)
    (Functor.isoWhiskerRight
      (homotopyComparisonGeneric T t.homotopyTensor t.homotopyComparison) Q) ≪≫
    t.resolvingComparison ≪≫ Functor.isoWhiskerLeft
      ((P.ι ⋙ Q).prod (P.ι ⋙ Q))
      (Functor.currying.counitIso.app t.derivedTensor).symm

private theorem tensorPresentation_comparison_app
    {M D : Type*} [Category* M] [Preadditive M] [HasBinaryBiproducts M]
    [HasZeroObject M] [Category* D]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (Q : HomotopyCategory M (.up ℤ) ⥤ D)
    (P : ObjectProperty (HomotopyCategory M (.up ℤ)))
    (t : TensorPresentation (HomotopyCategory.quotient M (.up ℤ)) Q
      (Functor.uncurry.obj T.map₂CochainComplex) P)
    (A B : CochainComplex M ℤ)
    (hA : P ((HomotopyCategory.quotient M (.up ℤ)).obj A))
    (hB : P ((HomotopyCategory.quotient M (.up ℤ)).obj B)) :
    (tensorPresentationComparison T Q P t).hom.app (⟨_, hA⟩, ⟨_, hB⟩) =
      (t.representativeIso A B hA hB).hom := by
  dsimp [tensorPresentationComparison, TensorPresentation.representativeIso,
    homotopyComparisonGeneric, Functor.currying]
  simp only [Category.comp_id, HomotopyCategory.quotient_obj_as]

/-- The resolving subcategory, its localization, and its existing tensor presentation.
The membership and localization fields prevent repeated expansion of the site descent
statement when using the dependent tensor comparisons.
Source: Stacks, Tags 06YS and 06YU
(auxiliary; not a blueprint node). -/
structure ResolvingTensorPresentation
    {CC H D : Type*} [Category* CC] [Category* H] [Category* D]
    (q : CC ⥤ H) (Q : H ⥤ D) (W : MorphismProperty H)
    (F : CC × CC ⥤ CC) (K : H → Prop) where
  property : ObjectProperty H
  membership : ∀ X, property X ↔ K X
  localization : (property.ι ⋙ Q).IsLocalization (W.inverseImage property.ι)
  tensor : TensorPresentation q Q F property

/-- Package all selected site descent data without changing any selected witness.
The localization field follows from the stated equivalence and its comparison to Q.
Source: Stacks, Tags 06YS and 06YU
(auxiliary; not a blueprint node). -/
def ResolvingTensorPresentation.ofExists
    {CC H D : Type*} [Category* CC] [Category* H] [Category* D]
    (q : CC ⥤ H) (Q : H ⥤ D) (W : MorphismProperty H)
    (F : CC × CC ⥤ CC) (K : H → Prop) (S : ObjectProperty H → Prop)
    (h : ∃ P : ObjectProperty H, (∀ X, P X ↔ K X) ∧
      (∃ E : (W.inverseImage P.ι).Localization ⥤ D,
        E.IsEquivalence ∧ Nonempty ((W.inverseImage P.ι).Q ⋙ E ≅ P.ι ⋙ Q)) ∧
      (∃ B : H × H ⥤ H, Nonempty ((q.prod q) ⋙ B ≅ F ⋙ q) ∧
        ∃ T : D × D ⥤ D, Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ Q ≅
          ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ T)) ∧ S P) :
    ResolvingTensorPresentation q Q W F K where
  property := h.choose
  membership := h.choose_spec.1
  localization := by
    let E := h.choose_spec.2.1.choose
    have : E.IsEquivalence := h.choose_spec.2.1.choose_spec.1
    exact Functor.IsLocalization.of_iso _ h.choose_spec.2.1.choose_spec.2.some
  tensor := TensorPresentation.ofExists q Q F h.choose h.choose_spec.2.2.1

private theorem descendTensorPresentation
    {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M]
    (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
    (hT : HomotopyTensorShiftData T)
    (P : ObjectProperty (HomotopyCategory M (.up ℤ))) [P.IsStableUnderShift ℤ]
    [(P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso M (.up ℤ)).inverseImage P.ι)]
    (t : TensorPresentation (HomotopyCategory.quotient M (.up ℤ)) DerivedCategory.Qh
      (Functor.uncurry.obj T.map₂CochainComplex) P)
    (hinv : ∀ a : P.FullSubcategory,
      (HomotopyCategory.quasiIso M (.up ℤ)).IsInvertedBy
        ((homotopyBifunctor T).obj a.obj ⋙ DerivedCategory.Qh) ∧
      (HomotopyCategory.quasiIso M (.up ℤ)).IsInvertedBy
        ((homotopyBifunctor T).flip.obj a.obj ⋙ DerivedCategory.Qh)) :
    ∃ _s : (Functor.curry.obj t.derivedTensor).CommShift₂Int,
      ∀ (A : CochainComplex M ℤ)
        (hA : P ((HomotopyCategory.quotient M (.up ℤ)).obj A)),
        (((Functor.curry.obj t.derivedTensor).obj (DerivedCategory.Q.obj A)).IsTriangulated ∧
          ((Functor.curry.obj t.derivedTensor).flip.obj
            (DerivedCategory.Q.obj A)).IsTriangulated) ∧
        (∃ cL : T.map₂CochainComplex.obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (Functor.curry.obj t.derivedTensor).obj
              (DerivedCategory.Q.obj A), NatTrans.CommShift cL.hom ℤ ∧
          ∀ (B : CochainComplex M ℤ)
            (hB : P ((HomotopyCategory.quotient M (.up ℤ)).obj B)),
            cL.app B = t.representativeIso A B hA hB) ∧
        (∃ cR : T.map₂CochainComplex.flip.obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (Functor.curry.obj t.derivedTensor).flip.obj
              (DerivedCategory.Q.obj A), NatTrans.CommShift cR.hom ℤ ∧
          ∀ (B : CochainComplex M ℤ)
            (hB : P ((HomotopyCategory.quotient M (.up ℤ)).obj B)),
            cR.app B = t.representativeIso B A hB hA) ∧
        (∀ {B B' : CochainComplex M ℤ} (f : B ⟶ B'),
          (((Functor.curry.obj t.derivedTensor).obj (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory M) ∧
          (((Functor.curry.obj t.derivedTensor).flip.obj
            (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory M)) := by
  let I := P.ι
  let Q : HomotopyCategory M (.up ℤ) ⥤ DerivedCategory M := DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso M (.up ℤ)
  let G := Functor.curry.obj t.derivedTensor
  let e : (I.prod I) ⋙ Functor.uncurry.obj (homotopyBifunctor T) ⋙ Q ≅
      ((I ⋙ Q).prod (I ⋙ Q)) ⋙ Functor.uncurry.obj G :=
    tensorPresentationComparison T Q P t
  have : Q.mapArrow.EssSurj := Localization.essSurj_mapArrow Q W
  obtain ⟨s, hs⟩ := descendCochainBifunctor T hT Q W DerivedCategory.Q
    (DerivedCategory.quotientCompQhIso M)
    (fun f ↦ DerivedCategory.mappingCone_triangle_distinguished f) P G e hinv
  refine ⟨s, fun A hA ↦ ?_⟩
  let q := HomotopyCategory.quotient M (.up ℤ)
  let a : P.FullSubcategory := ⟨q.obj A, hA⟩
  obtain ⟨htri, ⟨cL, hcLs, hcL⟩, ⟨cR, hcRs, hcR⟩, hcone⟩ := hs A hA
  refine ⟨htri, ⟨cL, hcLs, ?_⟩, ⟨cR, hcRs, ?_⟩, hcone⟩
  · intro B hB
    let b : P.FullSubcategory := ⟨q.obj B, hB⟩
    calc
      cL.app B = e.app (a, b) := by
        apply Iso.ext
        have h := congrArg Iso.hom (hcL B hB)
        change cL.hom.app B = 𝟙 _ ≫ Q.map (𝟙 _) ≫ e.hom.app (a, b) ≫
          (G.obj (Q.obj (q.obj A))).map (𝟙 _) at h
        erw [Q.map_id, (G.obj (Q.obj (q.obj A))).map_id] at h
        erw [Category.id_comp, Category.id_comp, Category.comp_id] at h
        exact h
      _ = t.representativeIso A B hA hB := by
        apply Iso.ext
        exact tensorPresentation_comparison_app T Q P t A B hA hB
  · intro B hB
    let b : P.FullSubcategory := ⟨q.obj B, hB⟩
    calc
      cR.app B = e.app (b, a) := by
        apply Iso.ext
        have h := congrArg Iso.hom (hcR B hB)
        change cR.hom.app B = 𝟙 _ ≫ Q.map (𝟙 _) ≫ e.hom.app (b, a) ≫
          (G.flip.obj (Q.obj (q.obj A))).map (𝟙 _) at h
        erw [Q.map_id, (G.flip.obj (Q.obj (q.obj A))).map_id] at h
        erw [Category.id_comp, Category.id_comp, Category.comp_id] at h
        exact h
      _ = t.representativeIso B A hB hA := by
        apply Iso.ext
        exact tensorPresentation_comparison_app T Q P t B A hB hA

end Generic

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The dependency's module-sheaf category on the given ringed site.
Source: Stacks, Modules on Sites, Section 03DA
(auxiliary; not a blueprint node). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

section LocalTensorDefinitions

/-- The existing canonical tensor of module sheaves.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
def ordinaryTensor : Modules R ⥤ Modules R ⥤ Modules R :=
  @curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)

/-- The canonical sheaf tensor is additive in its first argument.
Source: Stacks, Tag 03EK
(auxiliary; not a blueprint node). -/
theorem tensorAdditive : (ordinaryTensor R).Additive := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorAdditive

/-- The canonical sheaf tensor is additive in its second argument.
Source: Stacks, Tag 03EK
(auxiliary; not a blueprint node). -/
theorem tensorObjAdditive (M : Modules R) :
    ((ordinaryTensor R).obj M).Additive := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorObjAdditive

/-- The canonical direct-sum total tensor exists for every pair of complexes.
These named instances provide the interface of the unexpanded ordinary tensor.
Source: Stacks, Tag 06YM
(auxiliary; not a blueprint node). -/
theorem tensorHasMapBifunctor (A B : CochainComplex (Modules R) ℤ) :
    CochainComplex.HasMapBifunctor A B (ordinaryTensor R) := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorHasMapBifunctor
attribute [local irreducible] ordinaryTensor

/-- The existing direct-sum total tensor, as a curried bifunctor on complexes.
Source: Stacks, Tag 06YM (auxiliary; not a blueprint node). -/
abbrev totalTensor : CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (ordinaryTensor R).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- All the witnesses and proof fields of the published site tensor descent theorem.
This is a typed package of the original nested choices, rather than a new descent.
Source: Stacks, Tags 06YS and 06YU
(auxiliary; not a blueprint node). -/
def selectedResolvingTensorPresentation : ResolvingTensorPresentation
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
    (Functor.uncurry.obj (totalTensor R))
    (fun X ↦ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n)) :=
  ResolvingTensorPresentation.ofExists
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
    (Functor.uncurry.obj (totalTensor R))
    (fun X ↦ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n))
    (fun P ↦ ∀ (E : Type) (_ : Category.{0} E)
      (U V : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤ E),
      Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
        ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))
    (by
      unfold totalTensor ordinaryTensor
      exact (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R))

attribute [local irreducible] selectedResolvingTensorPresentation

/-- The resolving property already selected by site tensor descent.
Source: Stacks, Tags 06YS and 06YU
(auxiliary; not a blueprint node). -/
abbrev resolvingProperty : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
  (selectedResolvingTensorPresentation R).property

/-- The published membership equivalence for the resolving subcategory.
Source: Stacks, Tags 06YS and 06YU
(auxiliary; not a blueprint node). -/
theorem resolvingProperty_spec (X : HomotopyCategory (Modules R) (.up ℤ)) :
    resolvingProperty R X ↔ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n) :=
  (selectedResolvingTensorPresentation R).membership X

/-- The original homotopy and derived tensors with their selected comparisons.
The derived tensor field is literally the published `siteDerivedTensorIndependentCoefficients`,
so the exported `derivedTensor` unfolds reducibly to the original abbreviation; the other
fields are the selected choices, unchanged.
Source: Stacks, Tag 06YU
(auxiliary; not a blueprint node). -/
def selectedTensorPresentation : TensorPresentation
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (Functor.uncurry.obj (totalTensor R)) (resolvingProperty R) where
  homotopyTensor := (selectedResolvingTensorPresentation R).tensor.homotopyTensor
  homotopyComparison := (selectedResolvingTensorPresentation R).tensor.homotopyComparison
  derivedTensor := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R
  resolvingComparison := by
    with_unfolding_all exact (selectedResolvingTensorPresentation R).tensor.resolvingComparison

attribute [local irreducible] selectedTensorPresentation

/-- The published derived tensor, curried directly from the published bifunctor.
The shared presentation has this same field. Naming the bifunctor directly avoids
unfolding that large record when consumers compare the tensor with its published form.
Source: Stacks, Tag 06YU
(auxiliary; not a blueprint node). -/
def derivedTensor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) := Functor.curry.obj
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)

attribute [local irreducible] derivedTensor

attribute [local semireducible] selectedTensorPresentation

/-- The actual resolving comparison selected by the published descent theorem.
It is oriented from the localized total tensor to the derived tensor. Its arguments
are exactly flat-term K-flat complexes; the homotopy comparison is composed with the
resolving comparison, using the dependency's membership equivalence.
Source: Stacks, Tag 06YU (auxiliary; not a blueprint node). -/
def representativeIso
    (A B : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients B)
    (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n))
    (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)) :
    DerivedCategory.Q.obj (((totalTensor R).obj A).obj B) ≅
      (((derivedTensor R).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) := by
  unfold derivedTensor
  let e := DerivedCategory.quotientCompQhIso (Modules R)
  exact (e.app _).symm ≪≫
    (selectedTensorPresentation R).representativeIso A B
      ((resolvingProperty_spec R _).2 ⟨hA, hAf⟩)
      ((resolvingProperty_spec R _).2 ⟨hB, hBf⟩) ≪≫
    (selectedTensorPresentation R).derivedTensor.mapIso (Iso.prod (e.app A) (e.app B))

omit [HasDerivedCategory.{w} (Modules R)] in
private def ordinaryBraiding : ordinaryTensor R ≅ (ordinaryTensor R).flip := by
  unfold ordinaryTensor
  exact BraidedCategory.curriedBraidingNatIso (Modules R)

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem kFlat_iff_ordinary (A : CochainComplex (Modules R) ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients A ↔
      ∀ E : CochainComplex (Modules R) ℤ, E.Acyclic →
        (CochainComplex.mapBifunctor E A (ordinaryTensor R)).Acyclic := by
  unfold ordinaryTensor
  rfl

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem tensor_quasiIso
    (A : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    {B B' : CochainComplex (Modules R) ℤ} (f : B ⟶ B') (hf : QuasiIso f) :
    QuasiIso (((totalTensor R).obj A).map f) ∧
      QuasiIso (((totalTensor R).flip.obj A).map f) := by
  exact tensor_quasiIso_generic (ordinaryTensor R)
    (fun f ↦ CochainComplex.mappingCone.quasiIso_iff_acyclic f)
    (ordinaryBraiding R) A ((kFlat_iff_ordinary R A).1 hA) f hf

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem shift_kFlat
    (A : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A) (n : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧) := by
  apply (kFlat_iff_ordinary R (A⟦n⟧)).2
  intro E hE
  have ht := (kFlat_iff_ordinary R A).1 hA E hE
  have hs : (CochainComplex.mapBifunctor E A (ordinaryTensor R)⟦n⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (Modules R)).le_shift n _ ht
  intro i
  exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso E A (ordinaryTensor R) n).symm

private abbrev homotopyTensor : HomotopyCategory (Modules R) (.up ℤ) ⥤
    HomotopyCategory (Modules R) (.up ℤ) ⥤ HomotopyCategory (Modules R) (.up ℤ) :=
  (ordinaryTensor R).bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)

private theorem resolvingProperty_shift : (resolvingProperty R).IsStableUnderShift ℤ := by
  constructor
  intro n
  constructor
  intro X hX
  obtain ⟨A, rfl⟩ := X.quotient_obj_surjective
  have h := (resolvingProperty_spec R _).1 hX
  change CochainComplex.IsKFlatIndependentCoefficients A ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X i)) at h
  rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
  apply (resolvingProperty_spec R _).2
  constructor
  · exact shift_kFlat R A h.1 n
  · intro i
    exact h.2 (i + n)

set_option linter.unusedVariables false in
/-- Tensoring by a flat-term K-flat complex preserves all quasi-isomorphisms and
has exact descent to the published derived tensor. The natural representative
comparisons agree with the published comparisons on every resolving complex, and
commute with the canonical signed chain shifts. `CommShift₂Int` includes the zero
and addition laws, naturality in every derived fixed argument, and the mixed sign
`(-1)^(ab)`. `mapTriangle` includes the connecting arrow with its shift comparison.

Source: Stacks, Tags 06YM, 06YP and 06YU; derived.tex, definition-cone and
 definition-distinguished-triangle; more-algebra.tex, Tag 0FNH, item-shift-tensor
(auxiliary; not a blueprint node).

Proof (the node's nine steps):
1. Use the existing additive total tensor and its induced homotopy bifunctor.
   The chain-to-homotopy comparison comes from the generic bifunctor quotient API.
2. Use the generic total-tensor cone comparisons and the homotopy tensor's
   triangulated instances, which include compatibility of the connecting arrow.
3. The cone of an arbitrary quasi-isomorphism is acyclic. K-flatness gives
   acyclicity after tensoring on the right. Apply the braiding to the double
   complex and transpose the total complex to obtain the other order. The cone
   comparisons and cone criterion then prove both quasi-isomorphism assertions.
4. The signed second-variable shift comparison and shift stability of acyclic
   complexes prove K-flatness of every shift. Flat terms are reindexed by i+n.
5. Localize the coherent chain-level bifunctor shifts along the homotopy quotient.
   Localization uniqueness identifies the fixed-argument shifts with the canonical
   homotopy shifts. Replace those fields by the equal canonical structures, so
   the existing triangulated instances and comparison compatibility apply.
6. Fullness of the homotopy quotient transfers inversion of quasi-isomorphisms.
   The published equivalence for the resolving subcategory makes its inclusion
   followed by derived localization a localization itself.
7. Define the homotopy comparison by the inverse published chain comparison on
   underlying representatives; fullness of the quotient proves naturality. Restrict
   it to resolving pairs and compose with the published resolving comparison.
   The inverse currying counit matches the curried derived tensor and has identity
   components. Thus this comparison is normalized to representativeIso.
8. Localize the restricted homotopy bifunctor's shifts in both variables. Extend
   each fixed resolving comparison to all homotopy objects by localization.
   Uniqueness identifies its induced shift structure with the full bifunctor's
   shift structure. The normalized comparisons commute with shifts, and exactness
   follows by descent of triangulatedness along derived localization.
9. Compose with the canonical chain-to-homotopy and quotient-to-derived
   comparisons. Their identity components and the defining formula for the
   homotopy comparison give the exact representative normalization in both orders.
   CommShift₂Int supplies
   all derived fixed-argument naturality and the mixed sign. Exactness sends
   localized cone triangles, including their connecting arrows, to distinguished
   triangles. All totals are direct sums; no boundedness is used.
-/
theorem kFlat_fixed_tensor_triangulated :
    ∃ s : (derivedTensor R).CommShift₂Int,
      ∀ (A : CochainComplex (Modules R) ℤ)
        (hA : CochainComplex.IsKFlatIndependentCoefficients A)
        (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n)),
        (∀ (B B' : CochainComplex (Modules R) ℤ) (f : B ⟶ B'),
          QuasiIso f → QuasiIso (((totalTensor R).obj A).map f) ∧
            QuasiIso (((totalTensor R).flip.obj A).map f)) ∧
        (∀ n : ℤ, CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧) ∧
          ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) ((A⟦n⟧).X i)) ∧
        (((derivedTensor R).obj (DerivedCategory.Q.obj A)).IsTriangulated ∧
          ((derivedTensor R).flip.obj (DerivedCategory.Q.obj A)).IsTriangulated) ∧
        (∃ cL : (totalTensor R).obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (derivedTensor R).obj (DerivedCategory.Q.obj A),
          NatTrans.CommShift cL.hom ℤ ∧
          ∀ (B : CochainComplex (Modules R) ℤ)
            (hB : CochainComplex.IsKFlatIndependentCoefficients B)
            (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)),
            cL.app B = representativeIso R A B hA hB hAf hBf) ∧
        (∃ cR : (totalTensor R).flip.obj A ⋙ DerivedCategory.Q ≅
            DerivedCategory.Q ⋙ (derivedTensor R).flip.obj (DerivedCategory.Q.obj A),
          NatTrans.CommShift cR.hom ℤ ∧
          ∀ (B : CochainComplex (Modules R) ℤ)
            (hB : CochainComplex.IsKFlatIndependentCoefficients B)
            (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)),
            cR.app B = representativeIso R B A hB hA hBf hAf) ∧
        (∀ (B B' : CochainComplex (Modules R) ℤ) (f : B ⟶ B'),
          (((derivedTensor R).obj (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory (Modules R)) ∧
          (((derivedTensor R).flip.obj (DerivedCategory.Q.obj A)).mapTriangle.obj
            (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) ∈
              distTriang (DerivedCategory (Modules R))) := by
  let P : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) := resolvingProperty R
  let I : P.FullSubcategory ⥤ HomotopyCategory (Modules R) (.up ℤ) := P.ι
  let Q : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R) :=
    DerivedCategory.Qh
  let W : MorphismProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
    HomotopyCategory.quasiIso (Modules R) (.up ℤ)
  have : (resolvingProperty R).IsStableUnderShift ℤ := resolvingProperty_shift R
  have : (I ⋙ Q).IsLocalization (W.inverseImage I) :=
    (selectedResolvingTensorPresentation R).localization
  have hinv : ∀ a : (resolvingProperty R).FullSubcategory,
      W.IsInvertedBy ((homotopyTensor R).obj a.obj ⋙ Q) ∧
      W.IsInvertedBy ((homotopyTensor R).flip.obj a.obj ⋙ Q) := by
    intro a
    exact homotopyBifunctor_inverts (ordinaryTensor R) Q
      (Localization.inverts Q W) a.obj.as (fun f hf ↦
        tensor_quasiIso R a.obj.as ((resolvingProperty_spec R _).1 a.property).1 f hf)
  unfold derivedTensor
  obtain ⟨s, hs⟩ := descendTensorPresentation (ordinaryTensor R)
    (homotopyTensorShiftData (ordinaryTensor R)) P (selectedTensorPresentation R) hinv
  refine ⟨s, fun A hA hAf ↦ ?_⟩
  let q := HomotopyCategory.quotient (Modules R) (.up ℤ)
  let hPA := (resolvingProperty_spec R (q.obj A)).2 ⟨hA, hAf⟩
  obtain ⟨htri, ⟨cL, hcLs, hcL⟩, ⟨cR, hcRs, hcR⟩, hcone⟩ := hs A hPA
  refine ⟨(fun B B' f hf ↦ tensor_quasiIso R A hA f hf), ?_, htri,
    ⟨cL, hcLs, ?_⟩, ⟨cR, hcRs, ?_⟩, (fun B B' f ↦ hcone f)⟩
  · intro n
    exact ⟨shift_kFlat R A hA n, fun i ↦ hAf (i + n)⟩
  · intro B hB hBf
    let hPB := (resolvingProperty_spec R (q.obj B)).2 ⟨hB, hBf⟩
    apply Iso.ext
    simp only [Functor.comp_obj, Functor.curry_obj_obj_obj, Iso.app_hom, Iso.symm_hom,
      Iso.app_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
    erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg Iso.hom (hcL B hPB)
  · intro B hB hBf
    let hPB := (resolvingProperty_spec R (q.obj B)).2 ⟨hB, hBf⟩
    apply Iso.ext
    simp only [Functor.comp_obj, Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Iso.app_hom,
      Iso.symm_hom, Iso.app_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
    erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg Iso.hom (hcR B hPB)

end LocalTensorDefinitions

-- Preserve the original abbreviation interface for importing modules.
attribute [reducible] ordinaryTensor derivedTensor selectedResolvingTensorPresentation
  selectedTensorPresentation
  TensorPresentation.ofExists ResolvingTensorPresentation.ofExists

end SheafOfModules.KFlatFixedTensor
