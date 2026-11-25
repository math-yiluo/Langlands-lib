/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated

/-!
# Exact descent of tensoring with a fixed K-flat complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YM, 06YP and 06YU;
derived.tex, definition-cone and definition-distinguished-triangle;
more-algebra.tex, Tag 0FNH, item-shift-tensor.
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated)

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

section ShiftKFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- K-flatness for the canonical sheaf tensor is stable under shifts.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem shift_kFlat
    (A : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A) (n : ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients (A⟦n⟧) := by
  have (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := tensorAdditive R
  let := tensorObjAdditive R
  intro E hE
  have ht := hA E hE
  have hs : (CochainComplex.mapBifunctor E A (ordinaryTensor R)⟦n⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (Modules R)).le_shift n _ ht
  intro i
  exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso E A (ordinaryTensor R) n).symm

end ShiftKFlat

end SheafOfModules.KFlatFixedTensor
