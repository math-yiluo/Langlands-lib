/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Coherence of normalized scalar tensor comparisons

Source: Stacks 07A4 and 0D6D. The pure-generator equations determine the chain
comparisons before their coherence descends to unbounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules CategoryTheory.Functor
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R : Sheaf J CommRingCat.{max c v r}}
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
attribute [local irreducible] monoidalCategory
  Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors
private theorem exact_restriction_inv_factors {A B D : Type*}
    [Category A] [Category B] [Category D] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : D ⥤ B) (G : B ⥤ A) (H : D ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (P : CochainComplex D ℤ) :
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).inv.app P) ≫
        H.mapDerivedCategoryFactors.inv.app P ≫
          (Functor.mapDerivedCategoryNatIso e ≪≫
            (Functor.mapDerivedCategoryCompIso F G).symm).hom.app (DerivedCategory.Q.obj P) := by
  have h := Functor.exactDerivedRestrictionComposition_inv_factors F G H e.symm P
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv ((Functor.mapDerivedCategoryNatIso e ≪≫
    (Functor.mapDerivedCategoryCompIso F G).symm).app (DerivedCategory.Q.obj P)).symm).2
  simpa only [Functor.exactDerivedRestrictionComposition, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm,
    NatIso.mapHomologicalComplex, Category.assoc] using h

private theorem map_postcompose_iso_cancel {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) {X Y Z : A} (e : Y ≅ Z) {f : X ⟶ Y} {g : X ⟶ Z}
    (h : g = f ≫ e.hom) : Q.map g ≫ Q.map e.inv = Q.map f := by
  rw [h, Q.map_comp, Category.assoc, ← Q.map_comp, e.hom_inv_id, Q.map_id, Category.comp_id]

private theorem mapComplex_unit_comparison_f {A : Type*} [Category A] [Preadditive A]
    [HasZeroObject A] (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A)
    (P : CochainComplex A ℤ) (n : ℤ) :
    ((((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P).f n)) =
        e.hom.app (P.X n) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
  exact Category.comp_id _

private theorem leftAdjointUniq_hom_comp_eq
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {U : B ⥤ A} (d : F ⊣ U) (e : G ⊣ U)
    {X : A} {Y : B} (p : G.obj X ⟶ Y) (q : F.obj X ⟶ Y)
    (h : d.homEquiv X Y q = e.homEquiv X Y p) :
    (Adjunction.leftAdjointUniq d e).hom.app X ≫ p = q := by
  apply (d.homEquiv X Y).injective
  calc
    d.homEquiv X Y ((Adjunction.leftAdjointUniq d e).hom.app X ≫ p) =
        e.homEquiv X Y p := by
      rw [d.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
        Adjunction.homEquiv_unit]
    _ = d.homEquiv X Y q := h.symm

-- The categorical pasting calculation underlying the composition equation.
private theorem diagram_paste {Cat : Type*} [Category Cat]
    {A B B' C D E X Y Z N K P Q R H U V W : Cat}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E} {t : E ⟶ Z}
    {x : D ⟶ X} {y : X ⟶ Y} {z : Y ⟶ Z} {n : C ⟶ N} {m : N ⟶ X}
    {et : A ⟶ K} {qa : K ⟶ P} {rs : P ⟶ N} {ft : P ⟶ Q}
    {qb : Q ⟶ R} {rt : R ⟶ Y} {ff : K ⟶ H} {qfa : H ⟶ Q}
    {qk : R ⟶ U} {rc : U ⟶ Z} {kc : H ⟶ V} {qmc : V ⟶ U}
    {cc : A ⟶ W} {gc : W ⟶ V} {hr : W ⟶ B'} {r : B ⟶ B'} {ec : B' ⟶ E}
    (hsplit : d ≫ t = x ≫ y ≫ z) (hnat : c ≫ x = n ≫ m)
    (ha : a ≫ b ≫ n = et ≫ qa ≫ rs) (hb : rs ≫ m ≫ y = ft ≫ qb ≫ rt)
    (hf : qa ≫ ft = ff ≫ qfa) (hrc : rt ≫ z = qk ≫ rc)
    (ht : qfa ≫ qb ≫ qk = kc ≫ qmc) (hcc : et ≫ ff ≫ kc = cc ≫ gc)
    (hc : gc ≫ qmc ≫ rc = hr ≫ ec ≫ t) (hn : cc ≫ hr = a ≫ r) :
    a ≫ b ≫ c ≫ d ≫ t = a ≫ r ≫ ec ≫ t := by
  simp only [hsplit, ← Category.assoc c x, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc b n, ← Category.assoc a (b ≫ n), ha]
  simp only [Category.assoc]
  rw [← Category.assoc m y, ← Category.assoc rs (m ≫ y), hb]
  simp only [Category.assoc]
  rw [← Category.assoc qa ft, hf]
  simp only [Category.assoc]
  rw [hrc, ← Category.assoc qb qk, ← Category.assoc qfa (qb ≫ qk), ht]
  simp only [Category.assoc]
  rw [← Category.assoc ff kc, ← Category.assoc et (ff ≫ kc), hcc]
  simp only [Category.assoc]
  rw [hc]
  rw [← Category.assoc cc hr, hn]
  simp only [Category.assoc]

private theorem total_pure_hom_ext
    (P Q : CochainComplex (scalarModules J R) ℤ) (n : ℤ)
    (H : scalarModules J R)
    {f g : ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n ⟶ H}
    (hh : ∀ (p q : ℤ) (h : p + q = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) =
        g.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)) :
    f = g := by
  let := monoidalCategory R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R (P.X p) (Q.X q) H
  intro V x y
  exact hh p q h V x y

private theorem tensor_generator_map
    {P P' Q Q' : CochainComplex (scalarModules J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q n : ℤ) (h : p + q = n)
    (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g)).f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) =
      coefficientTensorGenerator.{r, c, v} J R P' Q' p q n h V
        ((f.f p).val.app V x) ((g.f q).val.app V y) := by
  let := monoidalCategory R
  dsimp only [coefficientTotalTensor, coefficientTensorGenerator]
  change ((HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ)).f n).val.app V
      ((CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h).val.app V
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
    (CochainComplex.ιMapBifunctor P' Q' (curriedTensor _) p q n h).val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (P'.X p) (Q'.X q) V
        ((f.f p).val.app V x) ((g.f q).val.app V y))
  have ht : HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor _) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor _) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ) := by
    simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]
  rw [ht]
  have hh := congrArg (fun k ↦ k.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
    (HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor _) (.up ℤ) p q n h)
  simp only [curriedTensor_map_app, curriedTensor_obj_map,
    ← tensorHom_def_assoc] at hh
  exact hh.trans
      (congrArg (fun z ↦ (CochainComplex.ιMapBifunctor P' Q' (curriedTensor _)
        p q n h).val.app V z)
        (SheafOfModules.ScalarHomOrdinary.pure_map R (f.f p) (g.f q) V x y))

attribute [local instance] ScalarDerivedPair.extension_additive

variable [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (M : ScalarHomModels.{c, v, r, w} J) {S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

private noncomputable def chainAdj :
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⊣
      (scalarRestriction a).mapHomologicalComplex (.up ℤ) :=
  letI := (M.scalar a).extension_additive
  (M.scalar a).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)

@[simp] private theorem chainAdj_unit_f
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    ((chainAdj M a).unit.app P).f n = (M.scalar a).ordinaryAdjunction.unit.app (P.X n) := rfl

attribute [local irreducible] chainAdj

private noncomputable def pairComparison :
    DerivedCategory.Q ⋙ (M.scalar a).derived ⟶
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso _).inv (M.scalar a).derived ≫
    whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) (M.scalar a).counit ≫
    whiskerRight ((M.scalar a).extension.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    whiskerLeft (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive)
      (DerivedCategory.quotientCompQhIso _).hom

private theorem pairComparison_app (P : CochainComplex (scalarModules J R) ℤ) :
    (pairComparison M a).app P = scalarPairComplexComparison
      (M.scalar a).extension (M.scalar a).extension_additive
      (M.scalar a).derived (M.scalar a).counit P := by
  change _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

attribute [local irreducible] pairComparison scalarPairComplexComparison coefficientTotalTensor
  coefficientTensorGenerator

private theorem unit_comparison_flat
    (P : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)) :
    (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map ((pairComparison M a).app P) ≫
          (scalarRestrictionComparison a).hom.app
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) =
      DerivedCategory.Q.map
        ((chainAdj M a).unit.app P) := by
  let s := M.scalar a
  let := s.extension_additive
  let adj := chainAdj M a
  have hi : scalarChainTranspose a s.extension s.extension_additive
      s.ordinaryAdjunction P _ (adj.unit.app P) = 𝟙 _ := by
    dsimp only [scalarChainTranspose, chainAdj, adj, scalarComplex]
    simpa only [chainAdj, s] using
      (s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv_symm_unit P
  have hn := s.normalization P hp hf _ (adj.unit.app P)
  erw [hi, DerivedCategory.Q.map_id, Category.comp_id] at hn
  have hh := congrArg (s.adjunction.homEquiv _ _) hn
  simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at hh
  rw [pairComparison_app]
  dsimp only [scalarComplex] at *
  erw [← Category.assoc, ← hh, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem unit_comparison (P : CochainComplex (scalarModules J R) ℤ) :
    (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map ((pairComparison M a).app P) ≫
          (scalarRestrictionComparison a).hom.app
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) =
      DerivedCategory.Q.map
        ((chainAdj M a).unit.app P) := by
  let s := M.scalar a
  let := s.extension_additive
  let F := scalarComplex s.extension s.extension_additive
  let U := (scalarRestriction a).mapHomologicalComplex (.up ℤ)
  let eta := (chainAdj M a).unit
  let lhs : DerivedCategory.Q ⟶ F ⋙ U ⋙ DerivedCategory.Q :=
    whiskerLeft DerivedCategory.Q s.adjunction.unit ≫
      whiskerRight (pairComparison M a) (scalarDerivedRestriction a) ≫
        whiskerLeft F (scalarRestrictionComparison a).hom
  let rhs : DerivedCategory.Q ⟶ F ⋙ U ⋙ DerivedCategory.Q :=
    whiskerRight eta DerivedCategory.Q
  obtain ⟨P', f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have : QuasiIso f := hq
  have he : lhs.app P' = rhs.app P' := by
    apply unit_comparison_flat M a P' hp
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P'.X n)).symm (hf n)
  change lhs.app P = rhs.app P
  apply (cancel_epi (DerivedCategory.Q.map f)).mp
  rw [lhs.naturality, rhs.naturality, he]

private theorem transpose_unit_comparison
    (P : CochainComplex (scalarModules J R) ℤ) :
    (M.scalar a).adjunction.homEquiv _ _ ((pairComparison M a).app P) =
      DerivedCategory.Q.map ((chainAdj M a).unit.app P) ≫
        (scalarRestrictionComparison a).inv.app
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) := by
  rw [Adjunction.homEquiv_unit]
  apply (Iso.eq_comp_inv ((scalarRestrictionComparison a).app
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P))).2
  change _ ≫ (scalarRestrictionComparison a).hom.app
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) = _
  have h := unit_comparison M a P
  dsimp only [scalarComplex, Functor.comp_obj, Functor.id_obj] at h ⊢
  simpa only [Category.assoc] using h

private theorem transpose_comparison
    (P : CochainComplex (scalarModules J R) ℤ)
    (H : CochainComplex (scalarModules J S) ℤ)
    (t : (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P ⟶ H) :
    (M.scalar a).adjunction.homEquiv _ _
        ((pairComparison M a).app P ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
          ((chainAdj M a).homEquiv _ _ t) ≫
        (scalarRestrictionComparison a).inv.app H := by
  let s := M.scalar a
  let := s.extension_additive
  dsimp only [scalarComplex] at *
  erw [s.adjunction.homEquiv_naturality_right, transpose_unit_comparison M a P]
  erw [Category.assoc, ← (scalarRestrictionComparison a).inv.naturality,
    ← Category.assoc, ← DerivedCategory.Q.map_comp]
  rfl

attribute [local irreducible] scalarHomOrdinaryRestrictionComp

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private noncomputable def chainRestrictionComp {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) :
    (scalarRestriction (a ≫ b)).mapHomologicalComplex (.up ℤ) ≅
      (scalarRestriction b).mapHomologicalComplex (.up ℤ) ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (scalarHomOrdinaryRestrictionComp.{c, v, r} a b) (.up ℤ)

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
@[simp] private theorem chainRestrictionComp_f {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (H : CochainComplex (scalarModules J T) ℤ) (n : ℤ) :
    (((chainRestrictionComp.{c, v, r} a b).hom.app H).f n) =
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app (H.X n) := rfl

private noncomputable def ordinaryComp {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) : (M.scalar a).extension ⋙ (M.scalar b).extension ≅
      (M.scalar (a ≫ b)).extension :=
  Adjunction.leftAdjointUniq
    ((M.scalar a).ordinaryAdjunction.comp (M.scalar b).ordinaryAdjunction)
    ((M.scalar (a ≫ b)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b))

attribute [local irreducible] ordinaryComp

private noncomputable def complexComp {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) :
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        scalarComplex (M.scalar b).extension (M.scalar b).extension_additive ≅
      scalarComplex (M.scalar (a ≫ b)).extension (M.scalar (a ≫ b)).extension_additive :=
  Functor.mapHomologicalComplexCompIso
    (Iso.refl ((M.scalar a).extension ⋙ (M.scalar b).extension)) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex (ordinaryComp M a b) (.up ℤ)

@[simp] private theorem complexComp_f {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    (((complexComp M a b).hom.app P).f n) = (ordinaryComp M a b).hom.app (P.X n) := by
  change (𝟙 _ ≫ _) = _
  exact Category.id_comp _

attribute [local irreducible] complexComp

private theorem complexComp_transpose {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ) :
    (((chainAdj M a).comp (chainAdj M b)).homEquiv _ _
      ((complexComp M a b).hom.app P)) =
      (chainAdj M (a ≫ b)).unit.app P ≫ (chainRestrictionComp.{c, v, r} a b).hom.app
        ((scalarComplex (M.scalar (a ≫ b)).extension
          (M.scalar (a ≫ b)).extension_additive).obj P) := by
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.comp_map,
    Functor.mapHomologicalComplex_map_f, chainAdj_unit_f, complexComp_f, chainRestrictionComp_f]
  simp only [scalarComplex, Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  change _ = (M.scalar (a ≫ b)).ordinaryAdjunction.unit.app (P.X n) ≫
    (scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app
      ((M.scalar (a ≫ b)).extension.obj (P.X n))
  unfold ordinaryComp
  simpa only [Adjunction.comp_unit_app, Functor.comp_map, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app] using
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((M.scalar a).ordinaryAdjunction.comp (M.scalar b).ordinaryAdjunction)
      ((M.scalar (a ≫ b)).ordinaryAdjunction.ofNatIsoRight
        (scalarHomOrdinaryRestrictionComp.{c, v, r} a b)) (P.X n))

private theorem restriction_comp_fac {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (H : CochainComplex (scalarModules J T) ℤ) :
    (scalarRestrictionComparison a).inv.app
        (((scalarRestriction b).mapHomologicalComplex (.up ℤ)).obj H) ≫
        (scalarDerivedRestriction a).map ((scalarRestrictionComparison b).inv.app H) =
      DerivedCategory.Q.map ((chainRestrictionComp.{c, v, r} a b).inv.app H) ≫
        (scalarRestrictionComparison (a ≫ b)).inv.app H ≫
        (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app (DerivedCategory.Q.obj H) := by
  exact exact_restriction_inv_factors (scalarRestriction b) (scalarRestriction a)
    (scalarRestriction (a ≫ b)) (scalarHomOrdinaryRestrictionComp.{c, v, r} a b) H

attribute [local irreducible] scalarHomRestrictionComp

private theorem composite_transpose {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ)
    (H : CochainComplex (scalarModules J T) ℤ)
    (t : (scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).obj
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) ⟶ H) :
    ((M.scalar a).adjunction.comp (M.scalar b).adjunction).homEquiv _ _
      ((M.scalar b).derived.map ((pairComparison M a).app P) ≫
        (pairComparison M b).app _ ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map
        (((chainAdj M a).comp
          (chainAdj M b)).homEquiv _ _ t) ≫
        DerivedCategory.Q.map ((chainRestrictionComp.{c, v, r} a b).inv.app H) ≫
        (scalarRestrictionComparison (a ≫ b)).inv.app H ≫
          (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app (DerivedCategory.Q.obj H) := by
  let sa := M.scalar a
  let sb := M.scalar b
  let := sa.extension_additive
  let := sb.extension_additive
  dsimp only [scalarComplex] at *
  rw [Adjunction.comp_homEquiv]
  change sa.adjunction.homEquiv _ _ (sb.adjunction.homEquiv _ _ _) = _
  erw [sb.adjunction.homEquiv_naturality_left, transpose_comparison M b]
  erw [← Category.assoc, sa.adjunction.homEquiv_naturality_right,
    transpose_comparison M a, Category.assoc, restriction_comp_fac.{c, v, r, w} a b]
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem comp_comparison {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj P) ≫
        (pairComparison M (a ≫ b)).app P =
      (M.scalar b).derived.map ((pairComparison M a).app P) ≫
        (pairComparison M b).app _ ≫ DerivedCategory.Q.map ((complexComp M a b).hom.app P) := by
  let sa := M.scalar a
  let sb := M.scalar b
  let sc := M.scalar (a ≫ b)
  let := sa.extension_additive
  let := sb.extension_additive
  let := sc.extension_additive
  let d := sa.adjunction.comp sb.adjunction
  let e := sc.adjunction.ofNatIsoRight (scalarHomRestrictionComp.{c, v, r, w} a b)
  dsimp only [scalarComplex] at *
  change (Adjunction.leftAdjointUniq d e).hom.app (DerivedCategory.Q.obj P) ≫
    (pairComparison M (a ≫ b)).app P = _
  apply leftAdjointUniq_hom_comp_eq d e
  refine (composite_transpose M a b P _ _).trans ?_
  let E := (scalarComplex sc.extension sc.extension_additive).obj P
  let k := (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app (DerivedCategory.Q.obj E)
  have hn := congrArg (fun f ↦ f ≫ k) (transpose_unit_comparison M (a ≫ b) P)
  have he := Adjunction.homEquiv_ofNatIsoRight_apply sc.adjunction
    (scalarHomRestrictionComp.{c, v, r, w} a b) ((pairComparison M (a ≫ b)).app P)
  have hm := map_postcompose_iso_cancel DerivedCategory.Q
    ((chainRestrictionComp.{c, v, r} a b).app E) (complexComp_transpose M a b P)
  apply Eq.trans (by
    simpa only [Iso.app_inv, Category.assoc] using
      congrArg (fun f ↦ f ≫ (scalarRestrictionComparison (a ≫ b)).inv.app E ≫ k) hm)
  apply Eq.trans _ he.symm
  dsimp only [E, k, sc, Functor.comp_obj, scalarComplex] at hn ⊢
  simpa only [Category.assoc] using hn.symm

attribute [local irreducible] scalarHomExtensionComp

attribute [local semireducible] scalarHomOrdinaryRestrictionComp

private theorem complexComp_unit {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (P : CochainComplex (scalarModules J R) ℤ)
    (n : ℤ) (V : Cᵒᵖ) (x : (P.X n).val.obj V) :
    (((complexComp M a b).hom.app P).f n).val.app V
        (scalarHomUnitSection M b _ V (scalarHomUnitSection M a _ V x)) =
      scalarHomUnitSection M (a ≫ b) _ V x := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((M.scalar a).ordinaryAdjunction.comp (M.scalar b).ordinaryAdjunction)
    ((M.scalar (a ≫ b)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b)) (P.X n)
  have hv := congrArg (fun f ↦ f.val.app V x) hu
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app] at hv
  rw [complexComp_f]
  unfold ordinaryComp scalarHomUnitSection
  exact hv

private theorem complex_comp_coherence {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (ma : ScalarHomTensorComparison M a)
    (mb : ScalarHomTensorComparison M b) (mc : ScalarHomTensorComparison M (a ≫ b))
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    (scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).map
        (ma.complexIso P Q).hom ≫
      (mb.complexIso
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)).hom ≫
      (coefficientTotalTensor.{r, c, v} J T).map
        (X := ((scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).obj
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P),
          (scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).obj
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)))
        (Y := ((scalarComplex (M.scalar (a ≫ b)).extension
          (M.scalar (a ≫ b)).extension_additive).obj P,
          (scalarComplex (M.scalar (a ≫ b)).extension
          (M.scalar (a ≫ b)).extension_additive).obj Q)) (Prod.mkHom
        ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q)) =
    (complexComp M a b).hom.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
      (mc.complexIso P Q).hom := by
  let sa := M.scalar a
  let sb := M.scalar b
  let sc := M.scalar (a ≫ b)
  let := sa.extension_additive
  let := sb.extension_additive
  let := sc.extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [scalarComplex]
  apply ((sa.ordinaryAdjunction.comp sb.ordinaryAdjunction).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.comp_unit_app]
  apply total_pure_hom_ext
  intro p q h V x y
  have hn (X Y : scalarModules J S) (f : X ⟶ Y) (z : X.val.obj V) :
      (sb.extension.map f).val.app V (scalarHomUnitSection M b X V z) =
        scalarHomUnitSection M b Y V (f.val.app V z) :=
    (congrArg (fun k ↦ k.val.app V z) (sb.ordinaryAdjunction.unit.naturality f)).symm
  change (((coefficientTotalTensor.{r, c, v} J T).map (Prod.mkHom
      ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q))).f n).val.app V
        (((mb.complexIso _ _).hom.f n).val.app V
          ((sb.extension.map ((ma.complexIso P Q).hom.f n)).val.app V
            (scalarHomUnitSection M b _ V (scalarHomUnitSection M a _ V _)))) =
    ((mc.complexIso P Q).hom.f n).val.app V
      ((((complexComp M a b).hom.app _).f n).val.app V
        (scalarHomUnitSection M b _ V (scalarHomUnitSection M a _ V _)))
  rw [hn]
  have ha := ma.generators P Q p q n h V x y
  apply Eq.trans (congrArg (fun z ↦
    ((((coefficientTotalTensor.{r, c, v} J T).map (Prod.mkHom
      ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q))).f n).val.app V)
      (((mb.complexIso _ _).hom.f n).val.app V
        (scalarHomUnitSection M b _ V z))) ha)
  have hb := mb.generators
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
    p q n h V (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y)
  apply Eq.trans (congrArg (fun z ↦
    ((((coefficientTotalTensor.{r, c, v} J T).map (Prod.mkHom
      ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q))).f n).val.app V) z) hb)
  erw [tensor_generator_map]
  have hx := complexComp_unit M a b P p V x
  have hy := complexComp_unit M a b Q q V y
  have hz := complexComp_unit M a b
    ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) n V
    (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)
  apply Eq.trans (congrArg₂ (fun z t ↦ coefficientTensorGenerator.{r, c, v}
    J T _ _ p q n h V z t) hx hy)
  exact (mc.generators P Q p q n h V x y).symm.trans
    (congrArg (fun z ↦ ((mc.complexIso P Q).hom.f n).val.app V z) hz.symm)

attribute [local irreducible] scalarHomOrdinaryRestrictionId

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
private noncomputable def chainRestrictionId (R : Sheaf J CommRingCat.{max c v r}) :
    (scalarRestriction (𝟙 R)).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (scalarModules J R) ℤ) :=
  NatIso.mapHomologicalComplex (scalarHomOrdinaryRestrictionId.{c, v, r} R) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (scalarModules J R) (.up ℤ)

omit [∀ A : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J A)] in
@[simp] private theorem chainRestrictionId_f (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    (((chainRestrictionId.{c, v, r} R).hom.app P).f n) =
      (scalarHomOrdinaryRestrictionId.{c, v, r} R).hom.app (P.X n) := by
  exact mapComplex_unit_comparison_f (scalarRestriction (𝟙 R))
    (scalarHomOrdinaryRestrictionId.{c, v, r} R) P n

private noncomputable def complexId (R : Sheaf J CommRingCat.{max c v r}) :
    scalarComplex (M.scalar (𝟙 R)).extension (M.scalar (𝟙 R)).extension_additive ≅
      𝟭 (CochainComplex (scalarModules J R) ℤ) :=
  letI := (M.scalar (𝟙 R)).extension_additive
  Adjunction.leftAdjointUniq
    ((chainAdj M (𝟙 R)).ofNatIsoRight
      (chainRestrictionId.{c, v, r} R)) Adjunction.id

private theorem leftAdjointUniq_inv_id
    {A : Type*} [Category A] {L U : A ⥤ A}
    (adj : L ⊣ U) (e : U ≅ 𝟭 A) (X : A) :
    (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) Adjunction.id).inv.app X =
      adj.unit.app X ≫ e.hom.app (L.obj X) := by
  apply (cancel_mono
    ((Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) Adjunction.id).hom.app X)).mp
  rw [Iso.inv_hom_id_app]
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, whiskerLeft_app,
    Functor.id_map, Adjunction.id_unit, NatTrans.id_app, Category.assoc] using
    (Adjunction.unit_leftAdjointUniq_hom_app
      (adj.ofNatIsoRight e) Adjunction.id X).symm

private theorem adjunction_id_comparison
    {A B : Type*} [Category A] [Category B]
    {F U : A ⥤ A} {L V : B ⥤ B} (d : F ⊣ U) (c : L ⊣ V)
    (Q : B ⥤ A) (ρ : Q ⋙ U ≅ V ⋙ Q) (ε : Q ⋙ F ⟶ L ⋙ Q)
    (e : U ≅ 𝟭 A) (e₀ : V ≅ 𝟭 B)
    (he : ∀ P, e.hom.app (Q.obj P) = ρ.hom.app P ≫ Q.map (e₀.hom.app P))
    (hu : ∀ P, d.unit.app (Q.obj P) ≫ U.map (ε.app P) ≫
      ρ.hom.app (L.obj P) = Q.map (c.unit.app P)) (P : B) :
    (Adjunction.leftAdjointUniq (d.ofNatIsoRight e) Adjunction.id).inv.app (Q.obj P) ≫
      ε.app P = Q.map
        ((Adjunction.leftAdjointUniq (c.ofNatIsoRight e₀) Adjunction.id).inv.app P) := by
  rw [leftAdjointUniq_inv_id, leftAdjointUniq_inv_id, Q.map_comp]
  have hn := e.hom.naturality (ε.app P)
  dsimp only [Functor.id_map, Functor.comp_obj] at hn
  calc
    (d.unit.app (Q.obj P) ≫ e.hom.app (F.obj (Q.obj P))) ≫ ε.app P =
        d.unit.app (Q.obj P) ≫ U.map (ε.app P) ≫ e.hom.app (Q.obj (L.obj P)) := by
      rw [Category.assoc, ← hn]
    _ = d.unit.app (Q.obj P) ≫ U.map (ε.app P) ≫ ρ.hom.app (L.obj P) ≫
        Q.map (e₀.hom.app (L.obj P)) := by rw [he]
    _ = Q.map (c.unit.app P) ≫ Q.map (e₀.hom.app (L.obj P)) := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ Q.map (e₀.hom.app (L.obj P))) (hu P)

private theorem restriction_id_fac (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarHomRestrictionId.{c, v, r, w} R).hom.app (DerivedCategory.Q.obj P) =
      (scalarRestrictionComparison (𝟙 R)).hom.app P ≫
        DerivedCategory.Q.map ((chainRestrictionId.{c, v, r} R).hom.app P) := by
  apply (cancel_epi ((scalarRestrictionComparison (𝟙 R)).inv.app P)).mp
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact Functor.exactDerivedRestrictionUnit_inv_factors (scalarRestriction (𝟙 R))
    (scalarHomOrdinaryRestrictionId.{c, v, r} R) P

attribute [local irreducible] scalarHomRestrictionId

private theorem id_comparison (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarHomExtensionId M R).inv.app (DerivedCategory.Q.obj P) ≫
        (pairComparison M (𝟙 R)).app P =
      DerivedCategory.Q.map ((complexId M R).inv.app P) := by
  let s := M.scalar (𝟙 R)
  let := s.extension_additive
  exact adjunction_id_comparison s.adjunction (chainAdj M (𝟙 R)) DerivedCategory.Q
    (scalarRestrictionComparison (𝟙 R)) (pairComparison M (𝟙 R))
    (scalarHomRestrictionId.{c, v, r, w} R)
    (chainRestrictionId.{c, v, r} R)
    (restriction_id_fac.{c, v, r, w} R)
    (unit_comparison M (𝟙 R)) P

attribute [local irreducible] scalarHomExtensionId

attribute [local semireducible] scalarHomOrdinaryRestrictionId

private theorem complexId_unit (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
    (x : (P.X n).val.obj V) :
    (((complexId M R).inv.app P).f n).val.app V x =
      scalarHomUnitSection M (𝟙 R) _ V x := by
  rw [complexId, leftAdjointUniq_inv_id]
  simp only [HomologicalComplex.comp_f,
    chainRestrictionId_f, chainAdj_unit_f]
  rfl

attribute [local irreducible] complexId

private theorem complex_id_coherence (R : Sheaf J CommRingCat.{max c v r})
    (mi : ScalarHomTensorComparison M (𝟙 R))
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    (coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom
        ((complexId M R).inv.app P) ((complexId M R).inv.app Q)) =
      (complexId M R).inv.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        (mi.complexIso P Q).hom := by
  let s := M.scalar (𝟙 R)
  let := s.extension_additive
  let F := scalarComplex s.extension s.extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply total_pure_hom_ext
  intro p q h V x y
  change _ = ((mi.complexIso P Q).hom.f n).val.app V
    ((((complexId M R).inv.app _).f n).val.app V _)
  have hx := complexId_unit M R P p V x
  have hy := complexId_unit M R Q q V y
  have hz := complexId_unit M R
    ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) n V
    (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)
  apply Eq.trans (tensor_generator_map
    ((complexId M R).inv.app P) ((complexId M R).inv.app Q) p q n h V x y)
  apply Eq.trans (congrArg₂ (fun z t ↦ coefficientTensorGenerator.{r, c, v}
    J R (F.obj P) (F.obj Q) p q n h V z t) hx hy)
  exact (mi.generators P Q p q n h V x y).symm.trans
    (congrArg (fun z ↦ ((mi.complexIso P Q).hom.f n).val.app V z) hz.symm)

private theorem representatives_ext (_M : ScalarHomModels.{c, v, r, w} J)
    {E : Type*} [Category E]
    {F G : DerivedCategory (scalarModules J R) × DerivedCategory (scalarModules J R) ⥤ E}
    {f g : F ⟶ G}
    (h : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
      (_hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (_hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
      f.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        g.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : f = g := by
  have hres (X : DerivedCategory (scalarModules J R)) :
      ∃ (P : CochainComplex (scalarModules J R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
          Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let K := DerivedCategory.Q.objPreimage X
    obtain ⟨P, p, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    have : QuasiIso p := hq
    exact ⟨P, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫
      DerivedCategory.Q.objObjPreimageIso X⟩⟩
  apply NatTrans.ext
  funext X
  obtain ⟨P, hp, ⟨eP⟩⟩ := hres X.1
  obtain ⟨Q, hq, ⟨eQ⟩⟩ := hres X.2
  let e := eP.prod eQ
  apply (cancel_epi (F.map e.hom)).mp
  rw [f.naturality, g.naturality, h P Q hp hq]

private theorem tensor_representative_naturality
    (R : Sheaf J CommRingCat.{max c v r})
    (P Q P' Q' : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (hp' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P')
    (hq' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g)) ≫
        (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
          P' Q' hp' hq').hom =
      (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
        P Q hp hq).hom ≫
        (M.closed R).tensor.map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  exact (M.model R).comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hp⟩) (Y := ⟨P', hp'⟩) f)
      (ObjectProperty.homMk (X := ⟨Q, hq⟩) (Y := ⟨Q', hq'⟩) g))

attribute [local irreducible] CoefficientTensorModels.iso

private theorem id_on_representatives
    (R : Sheaf J CommRingCat.{max c v r}) (mi : ScalarHomTensorComparison M (𝟙 R))
    (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    (M.closed R).tensor.map (Prod.mkHom
        ((scalarHomExtensionId M R).inv.app (DerivedCategory.Q.obj P))
        ((scalarHomExtensionId M R).inv.app (DerivedCategory.Q.obj Q))) =
      (scalarHomExtensionId M R).inv.app
          ((M.closed R).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        mi.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let s := M.scalar (𝟙 R)
  let F := scalarComplex s.extension s.extension_additive
  let T := (M.closed R).tensor
  let r := (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
    P Q hp hq).hom
  let r' := (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
    (F.obj P) (F.obj Q) (mi.preservesKFlat P hp) (mi.preservesKFlat Q hq)).hom
  have he (Y : CochainComplex (scalarModules J R) ℤ)
      (hy : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Y) :
      IsIso ((pairComparison M (𝟙 R)).app Y) := by
    rw [pairComparison_app]
    exact s.computes Y hy
  have := he P hp
  have := he Q hq
  have : IsIso (Prod.mkHom ((pairComparison M (𝟙 R)).app P)
      ((pairComparison M (𝟙 R)).app Q)) := by
    change IsIso ((asIso ((pairComparison M (𝟙 R)).app P)).prod
      (asIso ((pairComparison M (𝟙 R)).app Q))).hom
    infer_instance
  apply (cancel_epi r).mp
  apply (cancel_mono (T.map (Prod.mkHom
    ((pairComparison M (𝟙 R)).app P) ((pairComparison M (𝟙 R)).app Q)))).mp
  have hn := mi.normalization P Q hp hq
  simp only [← pairComparison_app M (𝟙 R)] at hn
  change s.derived.map r ≫ mi.iso.hom.app _ ≫
    T.map (Prod.mkHom ((pairComparison M (𝟙 R)).app P)
      ((pairComparison M (𝟙 R)).app Q)) =
    (pairComparison M (𝟙 R)).app _ ≫ DerivedCategory.Q.map (mi.complexIso P Q).hom ≫ r'
      at hn
  have hr : DerivedCategory.Q.map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom
        ((complexId M R).inv.app P) ((complexId M R).inv.app Q))) ≫ r' =
      r ≫ T.map (Prod.mkHom
        (DerivedCategory.Q.map ((complexId M R).inv.app P))
        (DerivedCategory.Q.map ((complexId M R).inv.app Q))) := by
    exact tensor_representative_naturality M R P Q (F.obj P) (F.obj Q) hp hq
      (mi.preservesKFlat P hp) (mi.preservesKFlat Q hq)
      ((complexId M R).inv.app P) ((complexId M R).inv.app Q)
  simp only [Category.assoc]
  rw [← T.map_comp]
  change r ≫ T.map (Prod.mkHom
    (((scalarHomExtensionId M R).inv.app _) ≫ (pairComparison M (𝟙 R)).app P)
    (((scalarHomExtensionId M R).inv.app _) ≫ (pairComparison M (𝟙 R)).app Q)) = _
  rw [id_comparison, id_comparison, ← hr]
  erw [(scalarHomExtensionId M R).inv.naturality_assoc r, hn,
    reassoc_of% (id_comparison M R
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))),
    ← DerivedCategory.Q.map_comp_assoc, ← complex_id_coherence M R mi]

private theorem comp_on_representatives {T : Sheaf J CommRingCat.{max c v r}}
    (b : S ⟶ T) (ma : ScalarHomTensorComparison M a)
    (mb : ScalarHomTensorComparison M b) (mc : ScalarHomTensorComparison M (a ≫ b))
    (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    (M.scalar b).derived.map (ma.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        mb.iso.hom.app ((M.scalar a).derived.obj (DerivedCategory.Q.obj P),
          (M.scalar a).derived.obj (DerivedCategory.Q.obj Q)) ≫
        (M.closed T).tensor.map (Prod.mkHom
          ((scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj P))
          ((scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj Q))) =
      (scalarHomExtensionComp M a b).hom.app
          ((M.closed R).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        mc.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let Fa := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
  let Fb := scalarComplex (M.scalar b).extension (M.scalar b).extension_additive
  let Fc := scalarComplex (M.scalar (a ≫ b)).extension (M.scalar (a ≫ b)).extension_additive
  let F := (M.scalar a).derived
  let G := (M.scalar b).derived
  let H := (M.scalar (a ≫ b)).derived
  let U := (M.closed S).tensor
  let V := (M.closed T).tensor
  let cc := scalarHomExtensionComp M a b
  let rR := (CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
    P Q hp hq).hom
  let rS := (CoefficientTensorModels.iso.{r, c, v, w} J S (M.closed S) (M.model S)
    (Fa.obj P) (Fa.obj Q) (ma.preservesKFlat P hp) (ma.preservesKFlat Q hq)).hom
  let rT := (CoefficientTensorModels.iso.{r, c, v, w} J T (M.closed T) (M.model T)
    (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q))
      (mb.preservesKFlat _ (ma.preservesKFlat P hp))
      (mb.preservesKFlat _ (ma.preservesKFlat Q hq))).hom
  let rC := (CoefficientTensorModels.iso.{r, c, v, w} J T (M.closed T) (M.model T)
    (Fc.obj P) (Fc.obj Q) (mc.preservesKFlat P hp) (mc.preservesKFlat Q hq)).hom
  let e (Y : CochainComplex (scalarModules J R) ℤ) := (pairComparison M a).app Y
  let f (Y : CochainComplex (scalarModules J S) ℤ) := (pairComparison M b).app Y
  let g (Y : CochainComplex (scalarModules J R) ℤ) := (pairComparison M (a ≫ b)).app Y
  let k (Y : CochainComplex (scalarModules J R) ℤ) :=
    DerivedCategory.Q.map ((complexComp M a b).hom.app Y)
  have he (Y : CochainComplex (scalarModules J R) ℤ)
      (hy : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Y) :
      IsIso (g Y) := by
    dsimp only [g]
    rw [pairComparison_app]
    exact (M.scalar (a ≫ b)).computes Y hy
  have := he P hp
  have := he Q hq
  have : IsIso (Prod.mkHom (g P) (g Q)) := by
    change IsIso ((asIso (g P)).prod (asIso (g Q))).hom
    infer_instance
  have ha := ma.normalization P Q hp hq
  simp only [← pairComparison_app M a] at ha
  change F.map rR ≫ ma.iso.hom.app _ ≫ U.map (Prod.mkHom (e P) (e Q)) =
    e _ ≫ DerivedCategory.Q.map (ma.complexIso P Q).hom ≫ rS at ha
  have hb := mb.normalization (Fa.obj P) (Fa.obj Q)
    (ma.preservesKFlat P hp) (ma.preservesKFlat Q hq)
  simp only [← pairComparison_app M b] at hb
  change G.map rS ≫ mb.iso.hom.app _ ≫ V.map (Prod.mkHom (f (Fa.obj P)) (f (Fa.obj Q))) =
    f _ ≫ DerivedCategory.Q.map (mb.complexIso _ _).hom ≫ rT at hb
  have hc := mc.normalization P Q hp hq
  simp only [← pairComparison_app M (a ≫ b)] at hc
  change H.map rR ≫ mc.iso.hom.app _ ≫ V.map (Prod.mkHom (g P) (g Q)) =
    g _ ≫ DerivedCategory.Q.map (mc.complexIso P Q).hom ≫ rC at hc
  have hsplit : V.map (Prod.mkHom
      (cc.hom.app (DerivedCategory.Q.obj P) ≫ g P)
      (cc.hom.app (DerivedCategory.Q.obj Q) ≫ g Q)) =
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) ≫
        V.map (Prod.mkHom (f (Fa.obj P)) (f (Fa.obj Q))) ≫
          V.map (Prod.mkHom (k P) (k Q)) := by
    rw [← V.map_comp, ← V.map_comp]
    congr 1
    exact Prod.ext (comp_comparison M a b P) (comp_comparison M a b Q)
  have hr : DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J T).map
      (Prod.mkHom ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q))) ≫ rC =
      rT ≫ V.map (Prod.mkHom (k P) (k Q)) := by
    exact tensor_representative_naturality M T
      (Fb.obj (Fa.obj P)) (Fb.obj (Fa.obj Q)) (Fc.obj P) (Fc.obj Q)
      (mb.preservesKFlat _ (ma.preservesKFlat P hp))
      (mb.preservesKFlat _ (ma.preservesKFlat Q hq))
      (mc.preservesKFlat P hp) (mc.preservesKFlat Q hq)
      ((complexComp M a b).hom.app P) ((complexComp M a b).hom.app Q)
  have hnat := mb.iso.hom.naturality (Prod.mkHom (e P) (e Q))
  change G.map (U.map (Prod.mkHom (e P) (e Q))) ≫ mb.iso.hom.app _ =
    mb.iso.hom.app _ ≫ V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) at hnat
  have hf := (pairComparison M b).naturality (ma.complexIso P Q).hom
  change G.map (DerivedCategory.Q.map (ma.complexIso P Q).hom) ≫ f _ =
    f _ ≫ DerivedCategory.Q.map (Fb.map (ma.complexIso P Q).hom) at hf
  have hs : V.map (Prod.mkHom (cc.hom.app (DerivedCategory.Q.obj P))
        (cc.hom.app (DerivedCategory.Q.obj Q))) ≫ V.map (Prod.mkHom (g P) (g Q)) =
      V.map (Prod.mkHom (G.map (e P)) (G.map (e Q))) ≫
        V.map (Prod.mkHom (f (Fa.obj P)) (f (Fa.obj Q))) ≫
          V.map (Prod.mkHom (k P) (k Q)) := by
    rw [← V.map_comp]
    exact hsplit
  have hga := congrArg G.map ha
  simp only [Functor.map_comp] at hga
  have ht := congrArg DerivedCategory.Q.map (complex_comp_coherence M a b ma mb mc P Q)
  simp only [Functor.map_comp] at ht
  have hcc := comp_comparison M a b ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))
  have hn := cc.hom.naturality rR
  dsimp only [Functor.comp_map] at hn
  apply (cancel_epi (G.map (F.map rR))).mp
  apply (cancel_mono (V.map (Prod.mkHom (g P) (g Q)))).mp
  simp only [Category.assoc]
  exact diagram_paste hs hnat.symm hga hb hf hr.symm ht hcc.symm hc.symm hn.symm

end CategoryTheory.ScalarHomTensor

namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- The normalized derived scalar tensor comparisons respect the unit-normalized
left-adjoint composition and identity comparisons.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0D6D.
(blueprint: lem-sfb-scalar-hom-tensor-coherence).

Proof: the normalized derived transpose gives the unit square on K-flat complexes
with flat terms. Naturality along a K-flat resolution extends that square to all
complexes. Applying the adjunction Hom bijections then identifies the derived
leftAdjointUniq composition and identity comparisons with their chain analogues.
On total pure generators the chain composition square follows from the three
generator equations and the unit equation for leftAdjointUniq. The identity square
follows from the same generator equation. Paste these squares with the specified
derived tensor normalization squares. Cancel the representative isomorphisms and
use naturality along K-flat representative isomorphisms to obtain both equations.
No flatness of a coefficient map or of an intermediate complex is required. -/
theorem scalarHomTensorCoherence
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) :
    (∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
      (X Y : DerivedCategory (scalarModules J R)),
      (M.scalar b).derived.map ((μ a).iso.hom.app (X, Y)) ≫
          (μ b).iso.hom.app ((M.scalar a).derived.obj X, (M.scalar a).derived.obj Y) ≫
            (M.closed T).tensor.map (Prod.mkHom
              ((scalarHomExtensionComp M a b).hom.app X)
              ((scalarHomExtensionComp M a b).hom.app Y)) =
        (scalarHomExtensionComp M a b).hom.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (a ≫ b)).iso.hom.app (X, Y)) ∧
    (∀ (R : Sheaf J CommRingCat.{max c v r})
      (X Y : DerivedCategory (scalarModules J R)),
      (M.closed R).tensor.map (Prod.mkHom
          ((scalarHomExtensionId M R).inv.app X) ((scalarHomExtensionId M R).inv.app Y)) =
        (scalarHomExtensionId M R).inv.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (𝟙 R)).iso.hom.app (X, Y)) := by
  constructor
  · intro R S T a b X Y
    let F := (M.scalar a).derived
    let G := (M.scalar b).derived
    let H := (M.scalar (a ≫ b)).derived
    let cc := scalarHomExtensionComp M a b
    let lhs : (M.closed R).tensor ⋙ F ⋙ G ⟶ (H.prod H) ⋙ (M.closed T).tensor :=
      whiskerRight (μ a).iso.hom G ≫
        whiskerLeft (F.prod F) (μ b).iso.hom ≫
          whiskerRight (NatTrans.prod cc.hom cc.hom) (M.closed T).tensor
    let rhs : (M.closed R).tensor ⋙ F ⋙ G ⟶ (H.prod H) ⋙ (M.closed T).tensor :=
      whiskerLeft (M.closed R).tensor cc.hom ≫ (μ (a ≫ b)).iso.hom
    have hh : lhs = rhs := ScalarHomTensor.representatives_ext M (J := J) (R := R) (by
      intro P Q hp hq
      exact ScalarHomTensor.comp_on_representatives M a b (μ a) (μ b) (μ (a ≫ b))
        P Q hp hq)
    exact congrArg (fun f ↦ f.app (X, Y)) hh
  · intro R X Y
    let F := (M.scalar (𝟙 R)).derived
    let ci := scalarHomExtensionId M R
    let lhs : (M.closed R).tensor ⟶ (F.prod F) ⋙ (M.closed R).tensor :=
      whiskerRight (NatTrans.prod ci.inv ci.inv) (M.closed R).tensor
    let rhs : (M.closed R).tensor ⟶ (F.prod F) ⋙ (M.closed R).tensor :=
      whiskerLeft (M.closed R).tensor ci.inv ≫ (μ (𝟙 R)).iso.hom
    have hh : lhs = rhs := ScalarHomTensor.representatives_ext M (J := J) (R := R) (by
      intro P Q hp hq
      exact ScalarHomTensor.id_on_representatives M R (μ (𝟙 R)) P Q hp hq)
    exact congrArg (fun f ↦ f.app (X, Y)) hh

end CategoryTheory
