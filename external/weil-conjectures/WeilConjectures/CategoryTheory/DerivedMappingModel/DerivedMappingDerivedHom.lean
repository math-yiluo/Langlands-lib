/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.CategoryTheory.GlobalHomResolutionRoof
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.DerivedMappingOrdinaryHom.DerivedMappingOrdinaryShift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # A derived Hom bifunctor with independent coefficient universes

Source: Stacks Project, Derived Categories, Tag 070I; Differential Graded Algebra,
Example 09L9. (blueprint: lem-sf-derived-mapping-derived-hom)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingModel

variable (B : Type b) [CommRing B] (A : Type u) [Category.{v} A] [Abelian A] [Linear B A]

private abbrev liftedPreadditive : Preadditive (ULiftHom.{b} A) where
  homGroup X Y := inferInstanceAs (AddCommGroup (ULift.{b} (X.objDown ⟶ Y.objDown)))
  add_comp _ _ _ f f' g := by
    apply ULift.ext
    exact Preadditive.add_comp _ _ _ f.down f'.down g.down
  comp_add _ _ _ f g g' := by
    apply ULift.ext
    exact Preadditive.comp_add _ _ _ f.down g.down g'.down

attribute [local instance] liftedPreadditive

private instance liftedDownEquiv :
    (ULiftHom.down : ULiftHom.{b} A ⥤ A).IsEquivalence :=
  Equivalence.isEquivalence_inverse (ULiftHom.equiv : A ≌ ULiftHom.{b} A)


private instance liftedDownAdditive : (ULiftHom.down : ULiftHom.{b} A ⥤ A).Additive where
  map_add := by intros; rfl

private instance liftedUpAdditive : (ULiftHom.up : A ⥤ ULiftHom.{b} A).Additive where
  map_add := by intros; rfl

private instance liftedFiniteProducts : HasFiniteProducts (ULiftHom.{b} A) :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (ULiftHom.down : ULiftHom.{b} A ⥤ A)⟩

private instance liftedAbelian : Abelian (ULiftHom.{b} A) :=
  abelianOfEquivalence (ULiftHom.down : ULiftHom.{b} A ⥤ A)

private abbrev liftedLinear : Linear (ULift.{v} B) (ULiftHom.{b} A) where
  homModule X Y := inferInstanceAs
    (Module (ULift.{v} B) (ULift.{b} (X.objDown ⟶ Y.objDown)))
  smul_comp _ _ _ a f g := by
    apply ULift.ext
    exact Linear.smul_comp _ _ _ a.down f.down g.down
  comp_smul _ _ _ f a g := by
    apply ULift.ext
    exact Linear.comp_smul _ _ _ f.down a.down g.down

attribute [local instance] liftedLinear

private def cochainTransport (X Y : CochainComplex A ℤ) (n : ℤ) :
    Cochain ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ) |>.obj X)
      ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ) |>.obj Y) n ≃ₗ[ULift.{v} B]
      ULift.{b} (Cochain X Y n) where
  toFun f := ULift.up (f.map (ULiftHom.down : ULiftHom.{b} A ⥤ A))
  invFun f := f.down.map (ULiftHom.up : A ⥤ ULiftHom.{b} A)
  left_inv f := by ext p q hpq; rfl
  right_inv f := by apply ULift.ext; ext p q hpq; rfl
  map_add' f g := by apply ULift.ext; ext p q hpq; rfl
  map_smul' a f := by apply ULift.ext; ext p q hpq; rfl


private def liftedHomIso (X Y : CochainComplex A ℤ) :
    globalLinearHom (ULift.{v} B)
      ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ) |>.obj X)
      ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ) |>.obj Y) ≅
        DerivedMappingOrdinaryHom.complex B X Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cochainTransport B A X Y n).toModuleIso) (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply ULift.ext
      change δ n m (f.map (ULiftHom.down : ULiftHom.{b} A ⥤ A)) =
        (δ n m f).map (ULiftHom.down : ULiftHom.{b} A ⥤ A)
      exact (δ_map n m f (ULiftHom.down : ULiftHom.{b} A ⥤ A)).symm)

private theorem liftedHomIso_naturality
    {X X' Y Y' : CochainComplex A ℤ} (f : X' ⟶ X) (g : Y ⟶ Y') :
    globalLinearHomMap (ULift.{v} B)
      (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map f)
      (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map g) ≫
        (liftedHomIso B A X' Y').hom =
      (liftedHomIso B A X Y).hom ≫ DerivedMappingOrdinaryHom.map B f g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  ext p q hpq
  change (((Cochain.ofHom
      (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map f)).comp
      (x.comp (Cochain.ofHom
        (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map g))
          (add_zero n)) (zero_add n)).map
        (ULiftHom.down : ULiftHom.{b} A ⥤ A)).v p q hpq =
    ((Cochain.ofHom f).comp
      ((x.map (ULiftHom.down : ULiftHom.{b} A ⥤ A)).comp (Cochain.ofHom g)
        (add_zero n)) (zero_add n)).v p q hpq
  simp

private instance liftedUpEquiv : (ULiftHom.up : A ⥤ ULiftHom.{b} A).IsEquivalence :=
  Equivalence.isEquivalence_functor (ULiftHom.equiv : A ≌ ULiftHom.{b} A)

omit [CommRing B] [Linear B A] in
private theorem liftedIsKInjective (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).obj I) where
  nonempty_homotopy_zero {K} f hK := by
    let adj : (ULiftHom.down : ULiftHom.{b} A ⥤ A) ⊣
        (ULiftHom.up : A ⥤ ULiftHom.{b} A) :=
      (ULiftHom.equiv : A ≌ ULiftHom.{b} A).symm.toAdjunction
    let adj' := adj.mapHomologicalComplex (.up ℤ)
    have hLK : (((ULiftHom.down : ULiftHom.{b} A ⥤ A).mapHomologicalComplex
        (.up ℤ)).obj K).Acyclic := by
      intro n
      exact (hK n).map (ULiftHom.down : ULiftHom.{b} A ⥤ A)
    let h := CochainComplex.IsKInjective.homotopyZero
      ((adj'.homEquiv _ _).symm f) hLK
    have hf : f = adj'.unit.app K ≫
        ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map
          ((adj'.homEquiv _ _).symm f) :=
      ((adj'.homEquiv _ _).apply_symm_apply f).symm.trans (adj'.homEquiv_unit _ _ _)
    rw [hf]
    exact ⟨(((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomotopy h).compLeft
      (adj'.unit.app K)).trans (.ofEq (by simp))⟩

omit [CommRing B] [Linear B A] in
private theorem liftedResolutions [Abelian.HasKInjectiveResolutions A]
    (K : CochainComplex (ULiftHom.{b} A) ℤ) :
    ∃ (I : CochainComplex (ULiftHom.{b} A) ℤ) (s : K ⟶ I),
      I.IsKInjective ∧ QuasiIso s := by
  let E := (ULiftHom.equiv : A ≌ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)
  obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (E.inverse.obj K)
  have : QuasiIso s := hs
  have : I.IsKInjective := hI
  have : CochainComplex.IsKInjective (E.functor.obj I) := liftedIsKInjective A I
  refine ⟨E.functor.obj I, (E.counitIso.app K).inv ≫ E.functor.map s,
    inferInstance, ?_⟩
  have : QuasiIso (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex
      (.up ℤ)).map s) := inferInstance
  change QuasiIso ((E.counitIso.app K).inv ≫
    ((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map s)
  infer_instance

variable [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]

/-- The lifted native Hom map depends only on the two homotopy classes.
Proof: transport homotopy invariance of the global resolution roof through the
explicit cochain isomorphism for the lifted Hom universe.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
theorem native_homotopy_invariance [Abelian.HasKInjectiveResolutions A]
    {X X' Y Y' : CochainComplex A ℤ} (f f' : X' ⟶ X) (g g' : Y ⟶ Y')
    (hf : Nonempty (Homotopy f f')) (hg : Nonempty (Homotopy g g')) :
    DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B f g) =
      DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B f' g') := by
  let := HasDerivedCategory.standard (ULiftHom.{b} A)
  obtain ⟨r⟩ := globalHom_resolution_roof (ULift.{v} B) (A := ULiftHom.{b} A)
    (liftedResolutions A)
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  have h := r.homotopy_invariance _ _ _ _ _ _ _ _
    ⟨(ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomotopy hf⟩
    ⟨(ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomotopy hg⟩
  apply (cancel_epi (DerivedCategory.Q.map (liftedHomIso B A X Y).hom)).mp
  calc
    _ = DerivedCategory.Q.map
        (globalLinearHomMap (ULift.{v} B)
          (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map f)
          (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).map g)) ≫
        DerivedCategory.Q.map (liftedHomIso B A X' Y').hom := by
      rw [← Functor.map_comp, ← liftedHomIso_naturality, Functor.map_comp]
    _ = _ := by
      rw [h, ← Functor.map_comp, liftedHomIso_naturality, Functor.map_comp]

/-- The native ordinary Hom complex descended to homotopy classes.
Its arrows use chosen representatives; the preceding invariance theorem proves
independence and the identity and composition laws.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
def homotopyFunctor [Abelian.HasKInjectiveResolutions A] :
    (HomotopyCategory A (.up ℤ))ᵒᵖ × HomotopyCategory A (.up ℤ) ⥤
      DerivedCategory (ModuleCat.{max b v} (ULift.{v} B)) where
  obj P := DerivedCategory.Q.obj
    (DerivedMappingOrdinaryHom.complex B P.1.unop.as P.2.as)
  map f := DerivedCategory.Q.map
    (DerivedMappingOrdinaryHom.map B f.1.unop.out f.2.out)
  map_id P := by
    change DerivedCategory.Q.map
      (DerivedMappingOrdinaryHom.map B (Quot.out (𝟙 P.1.unop)) (Quot.out (𝟙 P.2))) = _
    have h₁ : Nonempty (Homotopy (Quot.out (𝟙 P.1.unop)) (𝟙 P.1.unop.as)) :=
      ⟨HomotopyCategory.homotopyOfEq _ _ (by simp; rfl)⟩
    have h₂ : Nonempty (Homotopy (Quot.out (𝟙 P.2)) (𝟙 P.2.as)) :=
      ⟨HomotopyCategory.homotopyOfEq _ _ (by simp; rfl)⟩
    rw [native_homotopy_invariance B A _ _ _ _ h₁ h₂]
    exact (DerivedMappingOrdinaryHom.functor B ⋙ DerivedCategory.Q).map_id
      (Opposite.op P.1.unop.as, P.2.as)
  map_comp {P Q R} f g := by
    change DerivedCategory.Q.map
      (DerivedMappingOrdinaryHom.map B (Quot.out (g.1.unop ≫ f.1.unop))
        (Quot.out (f.2 ≫ g.2))) = _
    have h₁ : Nonempty (Homotopy (g.1.unop ≫ f.1.unop).out
        (g.1.unop.out ≫ f.1.unop.out)) :=
      ⟨HomotopyCategory.homotopyOfEq _ _ (by simp)⟩
    have h₂ : Nonempty (Homotopy (f.2 ≫ g.2).out (f.2.out ≫ g.2.out)) :=
      ⟨HomotopyCategory.homotopyOfEq _ _ (by simp)⟩
    rw [native_homotopy_invariance B A _ _ _ _ h₁ h₂]
    exact (DerivedMappingOrdinaryHom.functor B ⋙ DerivedCategory.Q).map_comp
      (X := (Opposite.op P.1.unop.as, P.2.as))
      (Y := (Opposite.op Q.1.unop.as, Q.2.as))
      (Z := (Opposite.op R.1.unop.as, R.2.as))
      (f.1.unop.out.op, f.2.out) (g.1.unop.out.op, g.2.out)

/-- The descended Hom bifunctor agrees with ordinary Hom on quotient arrows.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: each chosen representative of a quotient arrow is homotopic to the original
chain map, so homotopy invariance gives the equality. -/
theorem homotopyFunctor_map_quotient [Abelian.HasKInjectiveResolutions A]
    {X X' Y Y' : CochainComplex A ℤ} (f : X' ⟶ X) (g : Y ⟶ Y') :
    (homotopyFunctor B A).map
      (X := (Opposite.op ((HomotopyCategory.quotient A (.up ℤ)).obj X),
        (HomotopyCategory.quotient A (.up ℤ)).obj Y))
      (Y := (Opposite.op ((HomotopyCategory.quotient A (.up ℤ)).obj X'),
        (HomotopyCategory.quotient A (.up ℤ)).obj Y'))
      (((HomotopyCategory.quotient A (.up ℤ)).map f).op,
        (HomotopyCategory.quotient A (.up ℤ)).map g) =
      DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B f g) := by
  apply native_homotopy_invariance B A
  · exact ⟨HomotopyCategory.homotopyOfEq _ _ (by simp)⟩
  · exact ⟨HomotopyCategory.homotopyOfEq _ _ (by simp)⟩

open CategoryTheory.MonoidalCategory

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
private lemma tensor_iota
    {K K' L L' : CochainComplex (ModuleCat.{max b v} (ULift.{v} B)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (f ⊗ₘ g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj K' L' p q n h := by
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rw [CategoryTheory.MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

/-- Ordinary composition transported from the lifted Hom universe along `liftedHomIso`.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom). -/
private def nativeComp [HasDerivedCategory.{w} (ULiftHom.{b} A)]
    (r : GlobalHomResolutionRoof (ULift.{v} B) (A := ULiftHom.{b} A))
    (X Y Z : CochainComplex A ℤ) :
    DerivedMappingOrdinaryHom.complex B Y Z ⊗ DerivedMappingOrdinaryHom.complex B X Y ⟶
      DerivedMappingOrdinaryHom.complex B X Z :=
  ((liftedHomIso B A Y Z).inv ⊗ₘ (liftedHomIso B A X Y).inv) ≫
    r.comp _ _ _ ≫ (liftedHomIso B A X Z).hom

/-- The scalar identity transported from the lifted Hom universe along `liftedHomIso`.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom). -/
private def nativeUnit [HasDerivedCategory.{w} (ULiftHom.{b} A)]
    (r : GlobalHomResolutionRoof (ULift.{v} B) (A := ULiftHom.{b} A))
    (X : CochainComplex A ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{max b v} (ULift.{v} B)) (0 : ℤ)).obj
      (ModuleCat.of (ULift.{v} B) (ULift.{v} B)) ⟶
        DerivedMappingOrdinaryHom.complex B X X :=
  r.unit _ ≫ (liftedHomIso B A X X).hom

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
private lemma tensor_iota_apply
    {K K' L L' : CochainComplex (ModuleCat.{max b v} (ULift.{v} B)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℤ) (h : p + q = n) (x : K.X p) (y : L.X q) :
    (f ⊗ₘ g).f n (HomologicalComplex.ιTensorObj K L p q n h (x ⊗ₜ[ULift.{v} B] y)) =
      HomologicalComplex.ιTensorObj K' L' p q n h (f.f p x ⊗ₜ[ULift.{v} B] g.f q y) :=
  congrArg (fun φ ↦ φ.hom (x ⊗ₜ[ULift.{v} B] y)) (tensor_iota B f g p q n h)

private theorem nativeComp_apply [HasDerivedCategory.{w} (ULiftHom.{b} A)]
    (r : GlobalHomResolutionRoof (ULift.{v} B) (A := ULiftHom.{b} A))
    (X Y Z : CochainComplex A ℤ) (a d n : ℤ) (h : a + d = n)
    (g : (DerivedMappingOrdinaryHom.complex B Y Z).X a)
    (f : (DerivedMappingOrdinaryHom.complex B X Y).X d) :
    ((nativeComp B A r X Y Z).f n
      (HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
        (DerivedMappingOrdinaryHom.complex B X Y) a d n h
          (g ⊗ₜ[ULift.{v} B] f))).down =
      f.down.comp g.down ((add_comm d a).trans h) := by
  change ((liftedHomIso B A X Z).hom.f n ((r.comp _ _ _).f n
    (((liftedHomIso B A Y Z).inv ⊗ₘ (liftedHomIso B A X Y).inv).f n
      (HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
        (DerivedMappingOrdinaryHom.complex B X Y) a d n h (g ⊗ₜ[ULift.{v} B] f))))).down = _
  rw [tensor_iota_apply, r.comp_formula]
  ext p q hpq
  rfl

private theorem nativeUnit_apply [HasDerivedCategory.{w} (ULiftHom.{b} A)]
    (r : GlobalHomResolutionRoof (ULift.{v} B) (A := ULiftHom.{b} A))
    (X : CochainComplex A ℤ) (a : ULift.{v} B) :
    ((nativeUnit B A r X).f 0 a).down = a.down • Cochain.ofHom (𝟙 X) := by
  have hr := r.unit_formula
    (((ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)).obj X) a
  change ((liftedHomIso B A X X).hom.f 0 ((r.unit _).f 0
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of (ULift.{v} B) (ULift.{v} B))).inv a))).down = _
  rw [hr]
  ext p
  rfl

/-- Ordinary composition and scalar identities have their actual cochain formulas.
Source: Stacks 09L9 and 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: apply the global Hom roof theorem to the category with lifted Hom universes.
Transport its composition and unit through the explicit degreewise cochain isomorphism.
Naturality of the tensor summand inclusions proves the composition formula; evaluation
of the unit gives the scalar identity. The formulas determine these maps uniquely. -/
theorem ordinaryOperations_exists [Abelian.HasKInjectiveResolutions A] :
    ∃ (comp : ∀ X Y Z : CochainComplex A ℤ,
        DerivedMappingOrdinaryHom.complex B Y Z ⊗ DerivedMappingOrdinaryHom.complex B X Y ⟶
          DerivedMappingOrdinaryHom.complex B X Z)
      (unit : ∀ X : CochainComplex A ℤ,
        (CochainComplex.singleFunctor (ModuleCat.{max b v} (ULift.{v} B)) (0 : ℤ)).obj
          (ModuleCat.of (ULift.{v} B) (ULift.{v} B)) ⟶
            DerivedMappingOrdinaryHom.complex B X X),
      (∀ (X Y Z : CochainComplex A ℤ) (a d n : ℤ) (h : a + d = n)
        (g : (DerivedMappingOrdinaryHom.complex B Y Z).X a)
        (f : (DerivedMappingOrdinaryHom.complex B X Y).X d),
        ((comp X Y Z).f n
          (HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
            (DerivedMappingOrdinaryHom.complex B X Y) a d n h
              (g ⊗ₜ[ULift.{v} B] f))).down =
          f.down.comp g.down ((add_comm d a).trans h)) ∧
      (∀ (X : CochainComplex A ℤ) (a : ULift.{v} B),
        ((unit X).f 0 a).down = a.down • Cochain.ofHom (𝟙 X)) := by
  let _ := HasDerivedCategory.standard (ULiftHom.{b} A)
  obtain ⟨r⟩ := globalHom_resolution_roof (ULift.{v} B) (A := ULiftHom.{b} A)
    (liftedResolutions A)
  exact ⟨nativeComp B A r, nativeUnit B A r,
    nativeComp_apply B A r, nativeUnit_apply B A r⟩

/-- Ordinary composition, specified by its values on all graded pure tensors.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom). -/
def ordinaryComposition [Abelian.HasKInjectiveResolutions A]
    (X Y Z : CochainComplex A ℤ) :
    DerivedMappingOrdinaryHom.complex B Y Z ⊗ DerivedMappingOrdinaryHom.complex B X Y ⟶
      DerivedMappingOrdinaryHom.complex B X Z :=
  (ordinaryOperations_exists B A).choose X Y Z

/-- The ordinary scalar identity map, uniquely specified by its degree-zero formula.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom). -/
def ordinaryIdentity [Abelian.HasKInjectiveResolutions A] (X : CochainComplex A ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{max b v} (ULift.{v} B)) (0 : ℤ)).obj
      (ModuleCat.of (ULift.{v} B) (ULift.{v} B)) ⟶
        DerivedMappingOrdinaryHom.complex B X X :=
  (ordinaryOperations_exists B A).choose_spec.choose X

/-- The recorded ordinary composition has the literal cochain composition formula.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: use the pure-tensor characterization of the constructed operations. -/
theorem ordinaryComposition_apply [Abelian.HasKInjectiveResolutions A]
    (X Y Z : CochainComplex A ℤ) (a d n : ℤ) (h : a + d = n)
    (g : (DerivedMappingOrdinaryHom.complex B Y Z).X a)
    (f : (DerivedMappingOrdinaryHom.complex B X Y).X d) :
    ((ordinaryComposition B A X Y Z).f n
      (HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
        (DerivedMappingOrdinaryHom.complex B X Y) a d n h (g ⊗ₜ[ULift.{v} B] f))).down =
      f.down.comp g.down ((add_comm d a).trans h) :=
  (ordinaryOperations_exists B A).choose_spec.choose_spec.1 X Y Z a d n h g f

/-- The recorded ordinary identity sends a scalar to the scalar identity cochain.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: use the degree-zero characterization of the constructed operations. -/
theorem ordinaryIdentity_apply [Abelian.HasKInjectiveResolutions A]
    (X : CochainComplex A ℤ) (a : ULift.{v} B) :
    ((ordinaryIdentity B A X).f 0 a).down = a.down • Cochain.ofHom (𝟙 X) :=
  (ordinaryOperations_exists B A).choose_spec.choose_spec.2 X a

/-- The homogeneous pure-tensor formula determines ordinary composition uniquely.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: in every degree, the graded tensor inclusions determine a map out of the total
tensor complex. Pure tensors determine each such module map. The given formula and
the recorded composition formula agree on all of them. -/
theorem ordinaryComposition_unique [Abelian.HasKInjectiveResolutions A]
    (X Y Z : CochainComplex A ℤ)
    (c : DerivedMappingOrdinaryHom.complex B Y Z ⊗
      DerivedMappingOrdinaryHom.complex B X Y ⟶ DerivedMappingOrdinaryHom.complex B X Z)
    (hc : ∀ (a d n : ℤ) (h : a + d = n)
      (g : (DerivedMappingOrdinaryHom.complex B Y Z).X a)
      (f : (DerivedMappingOrdinaryHom.complex B X Y).X d),
      (c.f n (HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
        (DerivedMappingOrdinaryHom.complex B X Y) a d n h
          (g ⊗ₜ[ULift.{v} B] f))).down = f.down.comp g.down ((add_comm d a).trans h)) :
    c = ordinaryComposition B A X Y Z := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a d h
  change a + d = n at h
  change HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
    (DerivedMappingOrdinaryHom.complex B X Y) a d n h ≫ c.f n =
    HomologicalComplex.ιTensorObj (DerivedMappingOrdinaryHom.complex B Y Z)
      (DerivedMappingOrdinaryHom.complex B X Y) a d n h ≫
        (ordinaryComposition B A X Y Z).f n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro g f
  apply ULift.ext
  exact (hc a d n h g f).trans (ordinaryComposition_apply B A X Y Z a d n h g f).symm

/-- The degree-zero scalar formula determines the ordinary identity uniquely.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: maps out of a complex concentrated in degree zero are determined in that degree.
The stated scalar formula agrees pointwise with the recorded identity. -/
theorem ordinaryIdentity_unique [Abelian.HasKInjectiveResolutions A]
    (X : CochainComplex A ℤ)
    (c : (CochainComplex.singleFunctor (ModuleCat.{max b v} (ULift.{v} B)) (0 : ℤ)).obj
      (ModuleCat.of (ULift.{v} B) (ULift.{v} B)) ⟶
        DerivedMappingOrdinaryHom.complex B X X)
    (hc : ∀ a : ULift.{v} B, (c.f 0 a).down = a.down • Cochain.ofHom (𝟙 X)) :
    c = ordinaryIdentity B A X := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ULift.{v} B at a
  apply ULift.ext
  exact (hc a).trans (ordinaryIdentity_apply B A X a).symm

/-- Source-resolution precomposition is a quasi-isomorphism into a K-injective target,
with both source and target Hom groups in the original independent universes.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: lift the category's Hom universe, apply the precomposition assertion of the
global Hom roof to the lifted resolution, and conjugate by the cochain isomorphisms. -/
theorem precomp_quasiIso [Abelian.HasKInjectiveResolutions A]
    {X I J : CochainComplex A ℤ} (s : X ⟶ I)
    [QuasiIso s] [I.IsKInjective] [J.IsKInjective] :
    QuasiIso (DerivedMappingOrdinaryHom.map B s (𝟙 J)) := by
  let _ := HasDerivedCategory.standard (ULiftHom.{b} A)
  let U := (ULiftHom.up : A ⥤ ULiftHom.{b} A).mapHomologicalComplex (.up ℤ)
  have : CochainComplex.IsKInjective (U.obj I) := liftedIsKInjective A I
  have : CochainComplex.IsKInjective (U.obj J) := liftedIsKInjective A J
  let R : GlobalHomResolution (U.obj X) :=
    ⟨U.obj I, U.map s, inferInstance, inferInstance⟩
  obtain ⟨r⟩ := globalHom_resolution_roof (ULift.{v} B) (A := ULiftHom.{b} A)
    (liftedResolutions A)
  let f := globalLinearHomMap (ULift.{v} B) (U.map s) (𝟙 (U.obj J))
  have : QuasiIso f := r.precomp_quasiIso (U.obj X) (U.obj J) R inferInstance
  have hn := liftedHomIso_naturality B A s (𝟙 J)
  simp only [Functor.map_id] at hn
  have he : DerivedMappingOrdinaryHom.map B s (𝟙 J) =
      (liftedHomIso B A I J).inv ≫ f ≫ (liftedHomIso B A X J).hom := by
    apply (cancel_epi (liftedHomIso B A I J).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn.symm
  rw [he]
  infer_instance

variable [HasDerivedCategory.{w} A]

/-- The specified derived Hom bifunctor on the fixed K-injective representatives.
Apply the inverse K-injective equivalence in both variables and then the
constructed homotopy-category Hom functor.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
def derivedHom [Abelian.HasKInjectiveResolutions A] :
    (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤
      DerivedCategory (ModuleCat.{max b v} (ULift.{v} B)) :=
  let E := HomotopyCategory.KInjectives.equivalence A
  let I := E.inverse ⋙ ObjectProperty.ι _
  I.op.prod I ⋙ homotopyFunctor B A

/-- The fixed K-injective representative supplied by the inverse equivalence.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
def representative [Abelian.HasKInjectiveResolutions A] (P : DerivedCategory A) :
    CochainComplex A ℤ :=
  ((HomotopyCategory.KInjectives.equivalence A).inverse.obj P).obj.as

/-- Each fixed representative is K-injective by membership in the full subcategory.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
theorem representative_injective [Abelian.HasKInjectiveResolutions A]
    (P : DerivedCategory A) : (representative A P).IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact ((HomotopyCategory.KInjectives.equivalence A).inverse.obj P).property

/-- The inverse-equivalence counit identifies an object with its fixed representative.
Source: Stacks 09L9, 070I and 070Y
(blueprint: lem-sf-derived-mapping-derived-hom). -/
def representativeIso [Abelian.HasKInjectiveResolutions A]
    (P : DerivedCategory A) : DerivedCategory.Q.obj (representative A P) ≅ P :=
  (DerivedCategory.quotientCompQhIso A).symm.app (representative A P) ≪≫
    (HomotopyCategory.KInjectives.equivalence A).counitIso.app P

/-- The actual chain map representing a morphism between the fixed K-injective models.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom). -/
def representativeMap [Abelian.HasKInjectiveResolutions A]
    {P Q : DerivedCategory A} (f : P ⟶ Q) : representative A P ⟶ representative A Q :=
  Quot.out ((HomotopyCategory.KInjectives.equivalence A).inverse.map f).hom

/-- Representative maps intertwine their fixed comparison isomorphisms.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: apply naturality of the quotient comparison, then naturality of the counit of
the K-injective equivalence. -/
theorem representativeMap_naturality [Abelian.HasKInjectiveResolutions A]
    {P Q : DerivedCategory A} (f : P ⟶ Q) :
    DerivedCategory.Q.map (representativeMap A f) ≫ (representativeIso A Q).hom =
      (representativeIso A P).hom ≫ f := by
  let E := HomotopyCategory.KInjectives.equivalence A
  have hq := (DerivedCategory.quotientCompQhIso A).inv.naturality
    (representativeMap A f)
  dsimp only [Functor.comp_map] at hq
  have hq' : DerivedCategory.Q.map (representativeMap A f) ≫
      (DerivedCategory.quotientCompQhIso A).inv.app (representative A Q) =
    (DerivedCategory.quotientCompQhIso A).inv.app (representative A P) ≫
      DerivedCategory.Qh.map (E.inverse.map f).hom := by
    change DerivedCategory.Q.map (representativeMap A f) ≫
      (DerivedCategory.quotientCompQhIso A).inv.app (representative A Q) =
        (DerivedCategory.quotientCompQhIso A).inv.app (representative A P) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map
            (E.inverse.map f).hom.out) at hq
    simpa only [HomotopyCategory.quotient_map_out] using hq
  change DerivedCategory.Q.map (representativeMap A f) ≫
      ((DerivedCategory.quotientCompQhIso A).inv.app (representative A Q) ≫
        E.counitIso.hom.app Q) =
    ((DerivedCategory.quotientCompQhIso A).inv.app (representative A P) ≫
      E.counitIso.hom.app P) ≫ f
  rw [← Category.assoc, hq', Category.assoc]
  have hc := E.counitIso.hom.naturality f
  change DerivedCategory.Qh.map (E.inverse.map f).hom ≫ E.counitIso.hom.app Q =
    E.counitIso.hom.app P ≫ f at hc
  rw [hc, Category.assoc]

/-- On arrows the constructed bifunctor applies ordinary Hom to the recorded maps.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: unfold the composite functor and the chosen representatives of quotient arrows. -/
theorem derivedHom_map [Abelian.HasKInjectiveResolutions A]
    {P P' Q Q' : DerivedCategory A} (f : P' ⟶ P) (g : Q ⟶ Q') :
    (derivedHom B A).map (X := (Opposite.op P, Q)) (Y := (Opposite.op P', Q')) (f.op, g) =
      DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B
        (representativeMap A f) (representativeMap A g)) := rfl

/-- The fixed representative admits an augmentation whose derived arrow is the
inverse of the recorded comparison isomorphism.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: maps into a K-injective are represented by actual chain maps. -/
theorem augmentation_exists [Abelian.HasKInjectiveResolutions A]
    (X : CochainComplex A ℤ) :
    ∃ s : X ⟶ representative A (DerivedCategory.Q.obj X),
      DerivedCategory.Q.map s = (representativeIso A (DerivedCategory.Q.obj X)).inv := by
  have := representative_injective A (DerivedCategory.Q.obj X)
  exact CochainComplex.IsKInjective.exists_Q_map_eq X _ _

/-- Choose the chain map representing this specified derived arrow. Its homotopy class
is uniquely determined, which is the equality used by localized ordinary Hom.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom). -/
def augmentation [Abelian.HasKInjectiveResolutions A] (X : CochainComplex A ℤ) :
    X ⟶ representative A (DerivedCategory.Q.obj X) :=
  (augmentation_exists A X).choose

/-- The chosen chain map has exactly the specified image in the derived category.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: use the specification of the choice. -/
theorem augmentation_eq [Abelian.HasKInjectiveResolutions A] (X : CochainComplex A ℤ) :
    DerivedCategory.Q.map (augmentation A X) =
      (representativeIso A (DerivedCategory.Q.obj X)).inv :=
  (augmentation_exists A X).choose_spec

/-- These augmentations are quasi-isomorphisms.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: their localized images are the inverse comparison isomorphisms. -/
theorem augmentation_quasiIso [Abelian.HasKInjectiveResolutions A]
    (X : CochainComplex A ℤ) : QuasiIso (augmentation A X) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, augmentation_eq]
  infer_instance

/-- Equality after localization into a K-injective target gives an actual homotopy.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: conjugate the equality through the quotient comparison. The map from homotopy
classes into a K-injective is injective, and equality in the homotopy quotient means
there is a chain homotopy. -/
theorem homotopy_of_Q_eq {X I : CochainComplex A ℤ} [I.IsKInjective]
    (f g : X ⟶ I) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj X) I).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app I)).mp
  have hf := (DerivedCategory.quotientCompQhIso A).hom.naturality f
  have hg := (DerivedCategory.quotientCompQhIso A).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  exact hf.trans ((congrArg
    (fun t ↦ (DerivedCategory.quotientCompQhIso A).hom.app X ≫ t) h).trans hg.symm)

/-- Augmentations commute with representative maps up to an actual chain homotopy.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: localize the two composites, use the prescribed augmentation images and
naturality of the representative isomorphism, and use injectivity into the target model. -/
theorem augmentation_naturality [Abelian.HasKInjectiveResolutions A]
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    Nonempty (Homotopy (augmentation A X ≫ representativeMap A (DerivedCategory.Q.map f))
      (f ≫ augmentation A Y)) := by
  have := representative_injective A (DerivedCategory.Q.obj Y)
  apply homotopy_of_Q_eq A
  rw [Functor.map_comp, Functor.map_comp, augmentation_eq, augmentation_eq]
  apply (cancel_mono (representativeIso A (DerivedCategory.Q.obj Y)).hom).mp
  rw [Category.assoc, representativeMap_naturality]
  simp

/-- The canonical ordinary-to-derived Hom arrow, written as an explicit two-sided roof.
The denominator is source-resolution precomposition into a K-injective target.
Source: Stacks 070I and 0B6E (blueprint: lem-sf-derived-mapping-derived-hom). -/
def comparisonApp [Abelian.HasKInjectiveResolutions A] (X Y : CochainComplex A ℤ) :
    DerivedCategory.Q.obj (DerivedMappingOrdinaryHom.complex B X Y) ⟶
      (derivedHom B A).obj (Opposite.op (DerivedCategory.Q.obj X), DerivedCategory.Q.obj Y) := by
  have := representative_injective A (DerivedCategory.Q.obj X)
  have := representative_injective A (DerivedCategory.Q.obj Y)
  have := augmentation_quasiIso A X
  have := precomp_quasiIso B A (augmentation A X)
    (J := representative A (DerivedCategory.Q.obj Y))
  exact DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B (𝟙 X) (augmentation A Y)) ≫
    inv (DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B (augmentation A X)
      (𝟙 (representative A (DerivedCategory.Q.obj Y)))))

/-- The explicit comparison satisfies its defining two-sided roof equation.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: source precomposition is invertible into the target representative; cancel its
inverse in the definition of the comparison. -/
theorem comparisonApp_roof [Abelian.HasKInjectiveResolutions A]
    (X Y : CochainComplex A ℤ) :
    comparisonApp B A X Y ≫
      DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B (augmentation A X)
        (𝟙 (representative A (DerivedCategory.Q.obj Y)))) =
      DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B (𝟙 X) (augmentation A Y)) := by
  have := representative_injective A (DerivedCategory.Q.obj X)
  have := representative_injective A (DerivedCategory.Q.obj Y)
  have := augmentation_quasiIso A X
  have := precomp_quasiIso B A (augmentation A X)
    (J := representative A (DerivedCategory.Q.obj Y))
  simp [comparisonApp, Category.assoc]

/-- The explicit two-sided roof is natural in both complexes.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: postcompose with the invertible source-resolution map at the output pair.
Use the roof equations. The two augmentation squares commute up to the actual
homotopies already constructed; homotopy invariance of ordinary Hom identifies their
localized images. Functoriality of ordinary Hom then gives the desired square. -/
theorem comparisonApp_naturality [Abelian.HasKInjectiveResolutions A]
    {X X' Y Y' : CochainComplex A ℤ} (f : X' ⟶ X) (g : Y ⟶ Y') :
    DerivedCategory.Q.map (DerivedMappingOrdinaryHom.map B f g) ≫
        comparisonApp B A X' Y' =
      comparisonApp B A X Y ≫ (derivedHom B A).map
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) := by
  have := representative_injective A (DerivedCategory.Q.obj X')
  have := representative_injective A (DerivedCategory.Q.obj Y')
  have := augmentation_quasiIso A X'
  have := precomp_quasiIso B A (augmentation A X')
    (J := representative A (DerivedCategory.Q.obj Y'))
  let O := DerivedMappingOrdinaryHom.functor B (A := A) ⋙ DerivedCategory.Q
  let RX := representative A (DerivedCategory.Q.obj X)
  let RY := representative A (DerivedCategory.Q.obj Y)
  let RX' := representative A (DerivedCategory.Q.obj X')
  let RY' := representative A (DerivedCategory.Q.obj Y')
  let rf := representativeMap A (DerivedCategory.Q.map f)
  let rg := representativeMap A (DerivedCategory.Q.map g)
  obtain ⟨hf⟩ := augmentation_naturality A f
  obtain ⟨hg⟩ := augmentation_naturality A g
  apply (cancel_mono (DerivedCategory.Q.map
    (DerivedMappingOrdinaryHom.map B (augmentation A X') (𝟙 RY')))).mp
  rw [Category.assoc, comparisonApp_roof, derivedHom_map]
  change O.map (X := (Opposite.op X, Y)) (Y := (Opposite.op X', Y')) (f.op, g) ≫
      O.map (X := (Opposite.op X', Y')) (Y := (Opposite.op X', RY'))
        ((𝟙 X').op, augmentation A Y') =
    (comparisonApp B A X Y ≫
      O.map (X := (Opposite.op RX, RY)) (Y := (Opposite.op RX', RY')) (rf.op, rg)) ≫
        O.map (X := (Opposite.op RX', RY')) (Y := (Opposite.op X', RY'))
          ((augmentation A X').op, 𝟙 RY')
  calc
    _ = O.map (X := (Opposite.op X, Y)) (Y := (Opposite.op X', RY'))
        (f.op, g ≫ augmentation A Y') := by
      rw [← O.map_comp]
      congr 1
      ext <;> simp
    _ = O.map (X := (Opposite.op X, Y)) (Y := (Opposite.op X', RY'))
        (f.op, augmentation A Y ≫ rg) := by
      exact native_homotopy_invariance B A f f _ _ ⟨Homotopy.refl f⟩ ⟨hg.symm⟩
    _ = O.map (X := (Opposite.op X, Y)) (Y := (Opposite.op X, RY))
        ((𝟙 X).op, augmentation A Y) ≫ O.map (f.op, rg) := by
      rw [← O.map_comp]
      congr 1
      ext <;> simp
    _ = (comparisonApp B A X Y ≫
        O.map (X := (Opposite.op RX, RY)) (Y := (Opposite.op X, RY))
          ((augmentation A X).op, 𝟙 RY)) ≫ O.map (f.op, rg) := by
      exact congrArg (fun t : O.obj (Opposite.op X, Y) ⟶ O.obj (Opposite.op X, RY) ↦
        t ≫ O.map (X := (Opposite.op X, RY)) (Y := (Opposite.op X', RY')) (f.op, rg))
          (comparisonApp_roof B A X Y).symm
    _ = comparisonApp B A X Y ≫
        O.map (X := (Opposite.op RX, RY)) (Y := (Opposite.op X', RY'))
          ((f ≫ augmentation A X).op, rg) := by
      rw [Category.assoc, ← O.map_comp]
      congr 2
      ext <;> simp
    _ = comparisonApp B A X Y ≫
        O.map (X := (Opposite.op RX, RY)) (Y := (Opposite.op X', RY'))
          ((augmentation A X' ≫ rf).op, rg) := by
      congr 1
      exact native_homotopy_invariance B A _ _ rg rg ⟨hf.symm⟩ ⟨Homotopy.refl rg⟩
    _ = _ := by
      rw [Category.assoc, ← O.map_comp]
      congr 2
      apply Prod.ext
      · rfl
      · exact (Category.comp_id rg).symm


/-- The ordinary-to-derived Hom comparison, with its proved naturality.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom). -/
def comparison [Abelian.HasKInjectiveResolutions A] :
    DerivedMappingOrdinaryHom.functor B ⋙ DerivedCategory.Q ⟶
      (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ derivedHom B A where
  app P := comparisonApp B A P.1.unop P.2
  naturality {_ _} f := comparisonApp_naturality B A f.1.unop f.2

/-- Into a K-injective target, the explicit ordinary-to-derived comparison is invertible.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: the target augmentation is a quasi-isomorphism between K-injectives, hence a
homotopy equivalence. The descended Hom functor therefore sends it to an isomorphism.
The denominator of the comparison roof is invertible by source precomposition. -/
theorem comparison_resolved [Abelian.HasKInjectiveResolutions A]
    (X Y : CochainComplex A ℤ) [Y.IsKInjective] :
    IsIso ((comparison B A).app (Opposite.op X, Y)) := by
  have := representative_injective A (DerivedCategory.Q.obj X)
  have := representative_injective A (DerivedCategory.Q.obj Y)
  have := augmentation_quasiIso A X
  have hY := augmentation_quasiIso A Y
  have := precomp_quasiIso B A (augmentation A X)
    (J := representative A (DerivedCategory.Q.obj Y))
  have : IsIso ((HomotopyCategory.quotient A (.up ℤ)).map (augmentation A Y)) := by
    rw [HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences]
    exact (CochainComplex.IsKInjective.quasiIso_iff _).mp hY
  have : IsIso (DerivedCategory.Q.map
      (DerivedMappingOrdinaryHom.map B (𝟙 X) (augmentation A Y))) := by
    rw [← homotopyFunctor_map_quotient B A]
    let f : (Opposite.op ((HomotopyCategory.quotient A (.up ℤ)).obj X),
        (HomotopyCategory.quotient A (.up ℤ)).obj Y) ⟶
        (Opposite.op ((HomotopyCategory.quotient A (.up ℤ)).obj X),
          (HomotopyCategory.quotient A (.up ℤ)).obj
            (representative A (DerivedCategory.Q.obj Y))) :=
      (((HomotopyCategory.quotient A (.up ℤ)).map (𝟙 X)).op,
        (HomotopyCategory.quotient A (.up ℤ)).map (augmentation A Y))
    have : IsIso f := by
      apply (isIso_prod_iff _ _).mpr
      exact ⟨inferInstance, inferInstance⟩
    change IsIso ((homotopyFunctor B A).map f)
    infer_instance
  change IsIso (comparisonApp B A X Y)
  dsimp only [comparisonApp]
  infer_instance

/-- This bifunctor is computed by the ordinary linear Hom of the recorded representatives.
Source: Stacks 070I and 09L9 (blueprint: lem-sf-derived-mapping-derived-hom).
Proof: unfold the composite bifunctor and the K-injective inverse equivalence. -/
theorem derivedHom_obj [Abelian.HasKInjectiveResolutions A] (P Q : DerivedCategory A) :
    (derivedHom B A).obj (Opposite.op P, Q) =
      DerivedCategory.Q.obj
        (DerivedMappingOrdinaryHom.complex B (representative A P) (representative A Q)) := rfl

/-- Derived composition on the fixed K-injective representatives, using the lax
comparison from derived tensor to ordinary tensor.
Source: Stacks 09L9 and 0B6E (blueprint: lem-sf-derived-mapping-derived-hom). -/
def derivedComposition [Abelian.HasKInjectiveResolutions A]
    (P Q R : DerivedCategory A) :
    (derivedHom B A).obj (Opposite.op Q, R) ⊗
      (derivedHom B A).obj (Opposite.op P, Q) ⟶
        (derivedHom B A).obj (Opposite.op P, R) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q
    (DerivedMappingOrdinaryHom.complex B (representative A Q) (representative A R))
    (DerivedMappingOrdinaryHom.complex B (representative A P) (representative A Q)) ≫
      DerivedCategory.Q.map
        (ordinaryComposition B A (representative A P) (representative A Q) (representative A R))

/-- The derived identity is the ordinary scalar identity on the fixed representative.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-derived-hom). -/
def derivedIdentity [Abelian.HasKInjectiveResolutions A] (P : DerivedCategory A) :
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{max b v} (ULift.{v} B)) (0 : ℤ)).obj
        (ModuleCat.of (ULift.{v} B) (ULift.{v} B))) ⟶
      (derivedHom B A).obj (Opposite.op P, P) :=
  DerivedCategory.Q.map (ordinaryIdentity B A (representative A P))

/-- The inverse K-injective equivalence compares the representative of a shifted object
with the shift of its representative, in the homotopy category.
Source: Stacks 070I and 070Y (blueprint: lem-sf-derived-mapping-derived-hom). -/
def representativeShiftIso [Abelian.HasKInjectiveResolutions A]
    (Q : DerivedCategory A) (n : ℤ) :
    (HomotopyCategory.quotient A (.up ℤ)).obj (representative A (Q⟦n⟧)) ≅
      (HomotopyCategory.quotient A (.up ℤ)).obj ((representative A Q)⟦n⟧) :=
  let I := (HomotopyCategory.KInjectives.equivalence A).inverse ⋙ ObjectProperty.ι _
  (I.commShiftIso n).app Q ≪≫
    ((HomotopyCategory.quotient A (.up ℤ)).commShiftIso n).symm.app (representative A Q)

/-- The derived target shift is constructed from the representative shift isomorphism,
the signed ordinary Hom shift, and the localization's canonical shift comparison.
Source: Stacks 09L9 and 070Y (blueprint: lem-sf-derived-mapping-derived-hom). -/
def derivedShift [Abelian.HasKInjectiveResolutions A]
    (P Q : DerivedCategory A) (n : ℤ) :
    (derivedHom B A).obj (Opposite.op P, Q⟦n⟧) ≅
      ((derivedHom B A).obj (Opposite.op P, Q))⟦n⟧ :=
  (homotopyFunctor B A).mapIso
    (Iso.prod (Iso.refl (Opposite.op
      ((HomotopyCategory.quotient A (.up ℤ)).obj (representative A P))))
      (representativeShiftIso A Q n)) ≪≫
    DerivedCategory.Q.mapIso
      (DerivedMappingOrdinaryHom.targetShift B (representative A P) (representative A Q) n) ≪≫
    (DerivedCategory.Q.commShiftIso n).app
      (DerivedMappingOrdinaryHom.complex B (representative A P) (representative A Q))

end CategoryTheory.DerivedMappingModel
