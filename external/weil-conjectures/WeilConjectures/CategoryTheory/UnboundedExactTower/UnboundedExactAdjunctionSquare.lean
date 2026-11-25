/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Exact unbounded adjunctions, strict towers, and square mates

Source: Stacks Project, Derived Categories, Tags 0DVC, 0FND, 08BJ and 070I;
Cohomology on Sites, Tag 07A7; the constant/evaluation application is agent supplied
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

The index `op n` denotes positive level `n + 1`. All comparisons below are constructed
from the specified ordinary adjunction and exact-localization comparisons. In particular,
no arbitrary natural isomorphism or faithful derived evaluation is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u vA uA vB uB wA wB wTA wTB wA' wB' wTA' wTB'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedExactTower


/-- The existing Grothendieck-category K-injective resolution construction for module
sheaves. Source: Stacks 079P, 07A5
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
instance moduleResolutions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) :=
  letI := SheafOfModules.isGrothendieckAbelian R
  inferInstance

private def evaluationZeroConstAdjunction
    (A : Type uA) [Category.{vA} A] :
    (evaluation ℕᵒᵖ A).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun T ↦ {
        app := fun n ↦ T.map (homOfLE (Nat.zero_le n.unop)).op
        naturality := by
          intro n m t
          change T.map t ≫ T.map _ = T.map _ ≫ 𝟙 _
          rw [Category.comp_id, ← T.map_comp]
          congr 1 }
      naturality := by
        intro T U t
        ext n
        exact (t.naturality (homOfLE (Nat.zero_le n.unop)).op).symm }
    counit := { app := fun X ↦ 𝟙 X }
    left_triangle := by
      ext T
      dsimp
      simp
    right_triangle := by
      ext X n
      dsimp
      simp }

private theorem towerProperties (A : Type uA) [Category.{vA} A] [Abelian A] :
    Nonempty ((evaluation ℕᵒᵖ A).obj (op 0) ⊣ Functor.const ℕᵒᵖ) ∧
      PreservesFiniteLimits (Functor.const ℕᵒᵖ : A ⥤ _) ∧
      PreservesFiniteColimits (Functor.const ℕᵒᵖ : A ⥤ _) ∧
      (∀ n : ℕᵒᵖ, PreservesFiniteLimits ((evaluation ℕᵒᵖ A).obj n) ∧
        PreservesFiniteColimits ((evaluation ℕᵒᵖ A).obj n)) ∧
      (∀ I : CochainComplex A ℤ, I.IsKInjective →
        CochainComplex.IsKInjective
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ), I.IsKInjective →
        CochainComplex.IsKInjective
          ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I)) := by
  have h := evaluationZeroConstAdjunction A
  have := h.preservesKInjectiveComplexes
  refine ⟨⟨h⟩, inferInstance, inferInstance, fun n ↦ ⟨inferInstance, inferInstance⟩,
    ?_, ?_⟩
  · intro I hI
    have := hI
    infer_instance
  · intro I n hI
    have := hI
    exact tower_evaluation_isKInjective A I n

private theorem isIso_of_kinjective_components
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [Abelian.HasKInjectiveResolutions A]
    {E : Type*} [Category E] {V W : DerivedCategory A ⥤ E} (α : V ⟶ W)
    (h : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      IsIso (α.app (DerivedCategory.Q.obj I))) : IsIso α := by
  have : ∀ X, IsIso (α.app X) := by
    intro X
    obtain ⟨I, hI, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage X)
    have := hi
    have := h I hI
    let e : X ≅ DerivedCategory.Q.obj I :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map i)
    have ht : IsIso (V.map e.hom ≫ α.app (DerivedCategory.Q.obj I)) := inferInstance
    rw [α.naturality] at ht
    exact (isIso_comp_right_iff _ _).mp ht
  exact NatIso.isIso_of_isIso_app α

private theorem mate_homEquiv
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ H} {R₂ : H ⥤ E}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) {V : C ⥤ E} {W : D ⥤ H}
    (α : TwoSquare V L₁ L₂ W) (M : C) (N : D) (t : L₁.obj M ⟶ N) :
    b.homEquiv _ _ (α.app M ≫ W.map t) =
      V.map (a.homEquiv M N t) ≫ (mateEquiv a b α).app N := by
  rw [a.homEquiv_unit, b.homEquiv_unit, V.map_comp, Category.assoc]
  rw [show V.map (R₁.map t) ≫ (mateEquiv a b α).app N =
    (mateEquiv a b α).app (L₁.obj M) ≫ R₂.map (W.map t) from
    (mateEquiv a b α).naturality t]
  rw [← Category.assoc, unit_mateEquiv]
  simp only [R₂.map_comp, Category.assoc]
  rfl

private theorem mate_cube
    {C D C' D' E H E' H' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category E] [Category H] [Category E'] [Category H']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {T : E ⥤ H} {U : H ⥤ E} {T' : E' ⥤ H'} {U' : H' ⥤ E'}
    (a : L ⊣ R) (b : L' ⊣ R') (aT : T ⊣ U) (bT : T' ⊣ U')
    {V : C ⥤ E} {W : D ⥤ H} {V' : C' ⥤ E'} {W' : D' ⥤ H'}
    {g : C ⥤ C'} {h : D ⥤ D'} {gt : E ⥤ E'} {ht : H ⥤ H'}
    (s : g ⋙ L' ⟶ L ⋙ h) (st : gt ⋙ T' ⟶ T ⋙ ht)
    (c : V ⋙ T ≅ L ⋙ W) (c' : V' ⋙ T' ≅ L' ⋙ W')
    (e : V ⋙ gt ≅ g ⋙ V') (d : W ⋙ ht ≅ h ⋙ W')
    (hc : ∀ X : C,
      T'.map (e.hom.app X) ≫ c'.hom.app (g.obj X) ≫ W'.map (s.app X) =
        st.app (V.obj X) ≫ ht.map (c.hom.app X) ≫ d.hom.app (L.obj X)) (N : D) :
    e.inv.app (R.obj N) ≫ gt.map
        ((mateEquiv a aT (TwoSquare.mk _ _ _ _ c.hom)).app N) ≫
        (mateEquiv aT bT (TwoSquare.mk _ _ _ _ st)).app (W.obj N) =
      V'.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ s)).app N) ≫
        (mateEquiv b bT (TwoSquare.mk _ _ _ _ c'.hom)).app (h.obj N) ≫
        U'.map (d.inv.app N) := by
  exact (exchangeMate_cube a b aT bT V W V' W'
    c.symm e.symm d.symm c'.symm s st hc N).symm

private theorem derivedNatIso_refl
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro I
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app I)).1
  erw [Functor.mapDerivedCategoryNatIso_fac]
  change F.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map (𝟙 _) =
    𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app I
  simp

section Comparisons

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The descended constant/inverse-image identity, using the ordinary identity-component
comparison `compConstIso`. Source: Stacks 015F, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def constantInterchange :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ)
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm ≪≫
    (Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)).symm

variable {F} {G : A ⥤ B} [G.Additive]
  [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

/-- The constant comparison is the mate of the canonical descended inverse-image
comparison. Its invertibility and representative normalization are conclusions below.
Source: Stacks 07A7, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def constantComparison (a : F ⊣ G) :
    G.rightDerivedFunctor ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⟶
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor :=
  (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (constantInterchange F).hom))

/-- The evaluation comparison is the mate of the inverse of the canonical descended
termwise/evaluation identity. Source: Stacks 07A7, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def evaluationComparison (a : F ⊣ G) (n : ℕᵒᵖ) :
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor ⋙
        ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    a.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (towerDerivedEvaluationInterchange F n).inv))

/-- The canonical cochain-level unit of the existing total right derived functor.
It is obtained from its homotopy-level unit using the quotient factorization isomorphisms.
Source: Stacks 070K (blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def cochainUnit (G : A ⥤ B) [G.Additive] (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app I)

omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem cochainUnit_isIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (cochainUnit G I) := by
  unfold cochainUnit
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem cochain_counit (a : F ⊣ G) (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (cochainUnit G I) ≫
        a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso A (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient A (.up ℤ)).obj I)
  change F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app _) ≫
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app _ =
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫ _ at h
  simp only [cochainUnit, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp, Category.assoc] at h ⊢
  simp only [Quotient.lift.isLift_hom] at h ⊢
  repeat erw [Functor.map_id] at h
  repeat erw [Functor.map_id]
  repeat erw [Category.id_comp] at h
  repeat erw [Category.id_comp]
  exact h

end Comparisons

section Square

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

/-- Localize the given inverse-image composition comparison with the specified
composition isomorphisms. Source: Stacks 015F and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def localizedSquare (θ : g ⋙ F' ≅ F ⋙ h) :
    g.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ h.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso g F' ≪≫
    Functor.mapDerivedCategoryNatIso θ ≪≫ (Functor.mapDerivedCategoryCompIso F h).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')] in
private theorem localizedSquare_fac (θ : g ⋙ F' ≅ F ⋙ h)
    (M : CochainComplex B ℤ) :
    (localizedSquare F F' g h θ).hom.app (DerivedCategory.Q.obj M) ≫
        h.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app M) ≫
        h.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F'.mapDerivedCategory.map (g.mapDerivedCategoryFactors.hom.app M) ≫
        F'.mapDerivedCategoryFactors.hom.app ((g.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app M) := by
  simp only [localizedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fac F h M
  have hc' := Functor.mapDerivedCategoryCompIso_fac g F' M
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ h))
      (.up ℤ)).hom.app M = 𝟙 _ := rfl
  have hi' : (Functor.mapHomologicalComplexCompIso (Iso.refl (g ⋙ F'))
      (.up ℤ)).hom.app M = 𝟙 _ := rfl
  erw [hi, Functor.map_id, Category.comp_id] at hc
  erw [hi', Functor.map_id, Category.comp_id] at hc'
  erw [hc, Functor.mapDerivedCategoryNatIso_fac]
  erw [← hc']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The termwise inverse-image comparison, with component θ at each level.
Source: Stacks 07A7, termwise diagram application
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def towerSquare (θ : g ⋙ F' ≅ F ⋙ h) :
    (Functor.whiskeringRight ℕᵒᵖ B B').obj g ⋙
        (Functor.whiskeringRight ℕᵒᵖ B' A').obj F' ≅
      (Functor.whiskeringRight ℕᵒᵖ B A).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ A A').obj h :=
  NatIso.ofComponents (fun T => Functor.isoWhiskerLeft T θ) (fun {T U} t => by
    ext n
    exact θ.hom.naturality (t.app n))

private theorem constant_cube (θ : g ⋙ F' ≅ F ⋙ h) (M : DerivedCategory B) :
    ((Functor.whiskeringRight ℕᵒᵖ B' A').obj F').mapDerivedCategory.map
        ((constantInterchange g).hom.app M) ≫
      (constantInterchange F').hom.app (g.mapDerivedCategory.obj M) ≫
      (Functor.const ℕᵒᵖ : A' ⥤ _).mapDerivedCategory.map
        ((localizedSquare F F' g h θ).hom.app M) =
    (localizedSquare _ _ _ _ (towerSquare F F' g h θ)).hom.app
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj M) ≫
      ((Functor.whiskeringRight ℕᵒᵖ A A').obj h).mapDerivedCategory.map
        ((constantInterchange F).hom.app M) ≫
      (constantInterchange h).hom.app (F.mapDerivedCategory.obj M) := by
  have hc := Functor.mapDerivedCategory_exactCube
    (Functor.const ℕᵒᵖ : B ⥤ _) ((Functor.whiskeringRight ℕᵒᵖ B B').obj g)
    ((Functor.whiskeringRight ℕᵒᵖ B' A').obj F')
    g (Functor.const ℕᵒᵖ : B' ⥤ _) F' (Functor.const ℕᵒᵖ : A' ⥤ _)
    F h ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)
    ((Functor.whiskeringRight ℕᵒᵖ A A').obj h) (Functor.const ℕᵒᵖ : A ⥤ _)
    (Functor.compConstIso ℕᵒᵖ g).symm (Functor.compConstIso ℕᵒᵖ F').symm θ
    (towerSquare F F' g h θ) (Functor.compConstIso ℕᵒᵖ F).symm
    (Functor.compConstIso ℕᵒᵖ h).symm (by
      intro X
      ext n
      simp [towerSquare])
  exact NatTrans.congr_app hc M

variable {F F' g h} {G : A ⥤ B} {G' : A' ⥤ B'} [G.Additive] [G'.Additive]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')] in
private theorem localized_mate_cochain (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : g ⋙ F' ≅ F ⋙ h) (I : CochainComplex A ℤ) :
    g.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        g.mapDerivedCategory.map (cochainUnit G I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
            (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (h.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)) (.up ℤ)).app I) ≫
        cochainUnit G' ((h.mapHomologicalComplex (.up ℤ)).obj I) := by
  apply (a'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [a'.mapDerivedCategoryRightDerivedAdjunction.counit.naturality]
  have hm := mateEquiv_counit a.mapDerivedCategoryRightDerivedAdjunction
    a'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom) (DerivedCategory.Q.obj I)
  erw [reassoc_of% hm]
  erw [reassoc_of% (localizedSquare F F' g h θ).hom.naturality (cochainUnit G I)]
  simp only [Functor.id_map]
  rw [← h.mapDerivedCategory.map_comp_assoc, cochain_counit]
  simp only [Functor.map_comp, Category.assoc]
  erw [h.mapDerivedCategoryFactors_hom_naturality]
  erw [reassoc_of% localizedSquare_fac F F' g h θ
    ((G.mapHomologicalComplex (.up ℤ)).obj I)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [cochain_counit]
  erw [reassoc_of% F'.mapDerivedCategoryFactors_hom_naturality
    ((NatTrans.mapHomologicalComplex
      (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)) (.up ℤ)).app I)]
  simp only [← Functor.map_comp]
  congr 2
  ext n
  exact (mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ θ.hom) (I.X n)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A')] [HasDerivedCategory (ℕᵒᵖ ⥤ B')]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')] in
/-- The canonical derived square mate is represented by the ordinary mate on complexes.
Source: Stacks 070I, 08BJ and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

Transpose by the derived adjunction, apply its counit normalization, and use the
localization factorization of the inverse-image square. The ordinary mate counit
identity in each degree gives the resulting equality. -/
theorem localized_mate_cochain_normalization (a : F ⊣ G) (a' : F' ⊣ G')
    (θ : g ⋙ F' ≅ F ⋙ h) (I : CochainComplex A ℤ) :
    g.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        g.mapDerivedCategory.map (cochainUnit G I) ≫
        (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
            (DerivedCategory.Q.obj I) ≫
        G'.rightDerivedFunctor.map (h.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)) (.up ℤ)).app I) ≫
        cochainUnit G' ((h.mapHomologicalComplex (.up ℤ)).obj I) := by
  exact localized_mate_cochain a a' θ I

/-- Equality of the actual ordinary and tower square mates after constants and evaluation.
Neither equality requires the mate to be invertible or derived evaluation to be faithful.
Source: Stacks 07A7 and the explicit counit-transpose calculation
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def SquareCompatible (a : F ⊣ G) (a' : F' ⊣ G') (θ : g ⋙ F' ≅ F ⋙ h) : Prop :=
  (∀ K : DerivedCategory A,
    (constantInterchange g).inv.app (G.rightDerivedFunctor.obj K) ≫
      ((Functor.whiskeringRight ℕᵒᵖ B B').obj g).mapDerivedCategory.map
        ((constantComparison a).app K) ≫
      (mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
        (a'.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (localizedSquare _ _ _ _ (towerSquare F F' g h θ)).hom)).app
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K) =
    (Functor.const ℕᵒᵖ : B' ⥤ _).mapDerivedCategory.map
        ((mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app K) ≫
      (constantComparison a').app (h.mapDerivedCategory.obj K) ≫
      ((Functor.whiskeringRight ℕᵒᵖ A' B').obj G').rightDerivedFunctor.map
        ((constantInterchange h).inv.app K)) ∧
  (∀ (n : ℕᵒᵖ) (K : DerivedCategory (ℕᵒᵖ ⥤ A)),
    ((evaluation ℕᵒᵖ B').obj n).mapDerivedCategory.map
        ((mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
          (a'.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _
            (localizedSquare _ _ _ _ (towerSquare F F' g h θ)).hom)).app K) ≫
      (evaluationComparison a' n).app
        (((Functor.whiskeringRight ℕᵒᵖ A A').obj h).mapDerivedCategory.obj K) ≫
      G'.rightDerivedFunctor.map ((towerDerivedEvaluationInterchange h n).hom.app K) =
    (towerDerivedEvaluationInterchange g n).hom.app
        (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.obj K) ≫
      g.mapDerivedCategory.map ((evaluationComparison a n).app K) ≫
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
          (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.obj K))

end Square

section ComparisonProofs

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  {F : B ⥤ A} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : A ⥤ B} [G.Additive] [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem constant_mate (a : F ⊣ G) :
    (mateEquiv a (a.whiskerRight ℕᵒᵖ)
      (TwoSquare.mk _ _ _ _ (Functor.compConstIso ℕᵒᵖ F).inv)) =
      (Functor.compConstIso ℕᵒᵖ G).hom := by
  ext X n
  simp [mateEquiv]

private theorem constant_normalization (a : F ⊣ G) (I : CochainComplex A ℤ) :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map (cochainUnit G I) ≫
        (constantComparison a).app (DerivedCategory.Q.obj I) ≫
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.map
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ G).hom (.up ℤ)).app I) ≫
        cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj G)
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I) := by
  have ht := localized_mate_cochain a (a.whiskerRight ℕᵒᵖ)
    (Functor.compConstIso ℕᵒᵖ F).symm I
  erw [constant_mate] at ht
  exact ht

omit [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem evaluation_localizedSquare (n : ℕᵒᵖ) :
    localizedSquare ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) F
      ((evaluation ℕᵒᵖ B).obj n) ((evaluation ℕᵒᵖ A).obj n) (Iso.refl _) =
      (towerDerivedEvaluationInterchange F n).symm := by
  unfold localizedSquare towerDerivedEvaluationInterchange
  rw [derivedNatIso_refl]
  ext X
  simp

omit [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] in
private theorem evaluation_mate (a : F ⊣ G) (n : ℕᵒᵖ) :
    (mateEquiv (a.whiskerRight ℕᵒᵖ) a
      (TwoSquare.mk ((evaluation ℕᵒᵖ B).obj n)
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F) F ((evaluation ℕᵒᵖ A).obj n)
        (𝟙 (((evaluation ℕᵒᵖ B).obj n) ⋙ F)))) =
      𝟙 (((evaluation ℕᵒᵖ A).obj n) ⋙ G) := by
  ext T
  simp [mateEquiv]

private theorem evaluation_normalization (a : F ⊣ G) (n : ℕᵒᵖ)
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I) ≫
        ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
          (cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj G) I) ≫
        (evaluationComparison a n).app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map
          (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app I) =
      cochainUnit G ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I) := by
  have ht := localized_mate_cochain (a.whiskerRight ℕᵒᵖ) a
    (g := (evaluation ℕᵒᵖ B).obj n) (h := (evaluation ℕᵒᵖ A).obj n) (Iso.refl _) I
  rw [evaluation_localizedSquare] at ht
  erw [evaluation_mate] at ht
  have hid : (NatTrans.mapHomologicalComplex
      (𝟙 (((evaluation ℕᵒᵖ A).obj n) ⋙ G)) (.up ℤ)).app I = 𝟙 _ := by
    ext k
    rfl
  erw [hid, Functor.map_id, Category.id_comp] at ht
  exact ht

private theorem constant_isIso (a : F ⊣ G) : IsIso (constantComparison a) := by
  apply isIso_of_kinjective_components
  intro I hI
  have := hI
  have := (towerProperties A).2.2.2.2.1 I hI
  have := cochainUnit_isIso (G := G) I
  have := cochainUnit_isIso (G := (Functor.whiskeringRight ℕᵒᵖ A B).obj G)
    (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)
  have ht := constant_normalization a I
  have hc : IsIso ((NatTrans.mapHomologicalComplex
      (Functor.compConstIso ℕᵒᵖ G).hom (.up ℤ)).app I) := by
    change IsIso ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ G)
      (.up ℤ)).hom.app I)
    infer_instance
  have hs : IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (Functor.compConstIso ℕᵒᵖ G).hom (.up ℤ)).app I) ≫
      cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj G)
        (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)) :=
    inferInstance
  rw [← ht] at hs
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hs

private theorem evaluation_isIso (a : F ⊣ G) (n : ℕᵒᵖ) :
    IsIso (evaluationComparison a n) := by
  apply isIso_of_kinjective_components
  intro I hI
  have := hI
  have : CochainComplex.IsKInjective
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I) :=
    tower_evaluation_isKInjective A I n
  have := cochainUnit_isIso (G := (Functor.whiskeringRight ℕᵒᵖ A B).obj G) I
  have hs := cochainUnit_isIso (G := G)
    ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I)
  rw [← evaluation_normalization a n I] at hs
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hs

end ComparisonProofs

section EvaluationCube

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

end EvaluationCube

end CategoryTheory.UnboundedExactTower
