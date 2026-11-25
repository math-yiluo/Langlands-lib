/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import all WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc

/-! The complete-to-unit direction of the extended Cech criterion.

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-complete-implies-unit-isIso).

Proof: for one section, apply contravariant derived internal Hom to the degreewise
split sequence O[1/s][-1] → [O → O[1/s]] → O. Vanishing on the localization makes
precomposition by the augmentation invertible. Tensor–Hom currying and the K-flatness
of the factors extend this to the ordered finite tensor defining extended Cech.
For a complete object, the required vanishing holds for each member of every local
generating list. The augmented local description and internal-Hom restriction
comparison identify the actual augmentation maps. Invertibility descends along the
generating cover; composition with evaluation at one gives the specified unit.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible] derivedInternalHom ringedDerivedHomUnit

private theorem precomposition_comp
    {A : Type*} [Category A] (H : Aᵒᵖ × A ⥤ A)
    {P Q R : A} (a : P ⟶ Q) (b : Q ⟶ R) (E : A) :
    H.map (Prod.mkHom (a ≫ b).op (𝟙 E)) =
      H.map (Prod.mkHom b.op (𝟙 E)) ≫ H.map (Prod.mkHom a.op (𝟙 E)) := by
  rw [← H.map_comp]
  congr 1
  ext <;> simp

private theorem precomposition_of_isIso
    {A : Type*} [Category A] (H : Aᵒᵖ × A ⥤ A)
    {P Q : A} (a : P ⟶ Q) [IsIso a] (E : A) :
    IsIso (H.map (Prod.mkHom a.op (𝟙 E))) := by
  have : IsIso (Prod.mkHom a.op (𝟙 E)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

private theorem shortExact_precomposition_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (S : ShortComplex (ringedSiteComplex O)) (hS : S.ShortExact)
    (E : ringedSiteDerived O)
    (hE : IsZero ((derivedInternalHom J O).obj (op (DerivedCategory.Q.obj S.X₁), E))) :
    IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map S.g).op (𝟙 E))) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let F := (Functor.curry.obj (derivedInternalHom J O)).flip.obj E
  obtain ⟨shiftF, exactF⟩ := ringedInternalHom_contravariant_exact J O E
  let : F.CommShift ℤ := shiftF
  have : F.IsTriangulated := exactF
  let T := (triangleOpEquivalence (DerivedCategory A)).functor.obj
    (op (DerivedCategory.triangleOfSES hS))
  have hT : T ∈ distTriang (DerivedCategory A)ᵒᵖ :=
    Pretriangulated.op_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  exact ((F.mapTriangle.obj T).isZero₃_iff_isIso₁ (F.map_distinguished T hT)).mp hE

private theorem localization_single_one_isZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (s : (O.obj ⋙ forget CommRingCat).sections) (E : ringedSiteDerived O)
    (hE : IsZero ((derivedInternalHom J O).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (ringedSectionLocalization O s)), E))) :
    IsZero ((derivedInternalHom J O).obj
      (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 1).obj
        (ringedSectionLocalization O s))), E)) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let F := (Functor.curry.obj (derivedInternalHom J O)).flip.obj E
  let L := (CochainComplex.singleFunctor A 0).obj (ringedSectionLocalization O s)
  let eL : (CochainComplex.singleFunctor A 1).obj (ringedSectionLocalization O s) ≅
      L⟦(-1 : ℤ)⟧ :=
    (((CochainComplex.singleFunctors A).shiftIso (-1) 1 0 (by omega)).app _).symm
  let eQ : Q.obj ((CochainComplex.singleFunctor A 1).obj
      (ringedSectionLocalization O s)) ≅ (Q.obj L)⟦(-1 : ℤ)⟧ :=
    Q.mapIso eL ≪≫ (Q.commShiftIso (-1)).app L
  obtain ⟨eH⟩ := derivedInternalHom_shift_left J O (Q.obj L) (-1)
  exact ((shiftFunctor _ (1 : ℤ)).map_isZero hE).of_iso
    ((F.mapIso eQ.op).symm ≪≫ (eH.app E).symm)

@[irreducible] private noncomputable def concentratedIso
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    (K : CochainComplex A ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] (M : A) (eX : K.X n ≅ M) :
    K ≅ (CochainComplex.singleFunctor A n).obj M := by
  refine {
    hom := HomologicalComplex.mkHomToSingle eX.hom (fun i hi ↦
      (K.isZero_of_isStrictlyGE n i (by change i + 1 = n at hi; omega)).eq_of_src _ _)
    inv := HomologicalComplex.mkHomFromSingle eX.inv (fun i hi ↦
      (K.isZero_of_isStrictlyLE n i (by change n + 1 = i at hi; omega)).eq_of_tgt _ _)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · ext i
    obtain hi | rfl | hi := lt_trichotomy i n
    · exact (K.isZero_of_isStrictlyGE n i hi).eq_of_src _ _
    · simp
    · exact (K.isZero_of_isStrictlyLE n i hi).eq_of_src _ _
  · apply HomologicalComplex.from_single_hom_ext
    simp

private theorem concentratedIso_hom_f
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    (K : CochainComplex A ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [K.IsStrictlyLE n] (M : A) (eX : K.X n ≅ M) :
    (concentratedIso K n M eX).hom.f n =
      eX.hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) n M).inv := by
  simp [concentratedIso]

private theorem stupidTrunc_isStrictlyGE
    {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    CochainComplex.IsStrictlyGE (K.stupidTrunc (ComplexShape.embeddingUpIntGE n)) n :=
  ⟨fun i hi ↦ K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE n) i hi⟩

private theorem stupidTrunc_isStrictlyLE
    {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    CochainComplex.IsStrictlyLE (K.stupidTrunc (ComplexShape.embeddingUpIntLE n)) n :=
  ⟨fun i hi ↦ K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE n) i hi⟩

private theorem localization_precomposition_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (s : (O.obj ⋙ forget CommRingCat).sections) (E : ringedSiteDerived O)
    (hE : IsZero ((derivedInternalHom J O).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (ringedSectionLocalization O s)), E))) :
    IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map (ringedLocalizationTwoTermAugmentation O s)).op
        (𝟙 E))) := by
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let L := ringedLocalizationTwoTerm O s
  let : L.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff L 0).mpr (by
    intro i hi
    change IsZero (ringedLocalizationTwoTermX O s i)
    simp only [ringedLocalizationTwoTermX, ite_eq_right (by omega : i ≠ 0),
      ite_eq_right (by omega : i ≠ 1)]
    exact isZero_zero _)
  let : L.IsStrictlyLE 1 := (CochainComplex.isStrictlyLE_iff L 1).mpr (by
    intro i hi
    change IsZero (ringedLocalizationTwoTermX O s i)
    simp only [ringedLocalizationTwoTermX, ite_eq_right (by omega : i ≠ 0),
      ite_eq_right (by omega : i ≠ 1)]
    exact isZero_zero _)
  let ac := ComplexShape.Embedding.embeddingUpInt_areComplementary 0 1 (by omega)
  let S := L.shortComplexStupidTrunc ac
  let : CochainComplex.IsStrictlyGE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE 1)) 1 := stupidTrunc_isStrictlyGE L 1
  let : CochainComplex.IsStrictlyLE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE 1)) 1 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE
      (L.stupidTrunc (ComplexShape.embeddingUpIntGE 1)) 1)
  let : CochainComplex.IsStrictlyGE
      (L.stupidTrunc (ComplexShape.embeddingUpIntLE 0)) 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyGE
      (L.stupidTrunc (ComplexShape.embeddingUpIntLE 0)) 0)
  let : CochainComplex.IsStrictlyLE
      (L.stupidTrunc (ComplexShape.embeddingUpIntLE 0)) 0 := stupidTrunc_isStrictlyLE L 0
  have hS : S.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n ↦ (L.shortComplexStupidTruncSplitting ac n).shortExact)
  let e₁ : L.stupidTrunc (ComplexShape.embeddingUpIntGE 1) ≅ (CochainComplex.singleFunctor A 1).obj
      (ringedSectionLocalization O s) :=
    concentratedIso _ 1 _
      (L.stupidTruncXIso (ComplexShape.embeddingUpIntGE 1) (i := 0) (by simp) ≪≫
        eqToIso (ringedLocalizationTwoTermX_one O s))
  have hz : IsZero ((derivedInternalHom J O).obj (op (DerivedCategory.Q.obj S.X₁), E)) := by
    let F := (Functor.curry.obj (derivedInternalHom J O)).flip.obj E
    exact (localization_single_one_isZero O s E hE).of_iso
      (F.mapIso (DerivedCategory.Q.mapIso e₁).op).symm
  have hp := shortExact_precomposition_isIso O S hS E hz
  let φ : (L.stupidTrunc (ComplexShape.embeddingUpIntLE 0)).X 0 ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
    (L.stupidTruncXIso (ComplexShape.embeddingUpIntLE 0) (i := 0) (by simp)).hom ≫
      (ringedLocalizationTwoTermAugmentation O s).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).hom
  have : IsIso ((ringedLocalizationTwoTermAugmentation O s).f 0) := by
    change IsIso (ringedLocalizationTwoTermAugmentationF O s 0)
    simp only [ringedLocalizationTwoTermAugmentationF, dite_true]
    infer_instance
  have : IsIso φ := by dsimp only [φ]; infer_instance
  let e₃ : L.stupidTrunc (ComplexShape.embeddingUpIntLE 0) ≅ ringedSiteRingComplex O :=
    concentratedIso _ 0 _ (asIso φ)
  let q := e₃.hom
  have hq : IsIso q := inferInstance
  have heq : S.g ≫ q = ringedLocalizationTwoTermAugmentation O s := by
    apply HomologicalComplex.to_single_hom_ext (K := L) (j := (0 : ℤ))
      (A := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
      (f := S.g ≫ q) (g := ringedLocalizationTwoTermAugmentation O s)
    simp only [HomologicalComplex.comp_f]
    rw [show q.f 0 = φ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv from
        concentratedIso_hom_f _ 0 _ (asIso φ)]
    dsimp only [S, HomologicalComplex.shortComplexStupidTrunc,
      HomologicalComplex.πStupidTrunc, φ]
    simp [HomologicalComplex.πStupidTruncf, Category.assoc]
  rw [← heq, Functor.map_comp, precomposition_comp]
  have : IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map S.g).op (𝟙 E))) := hp
  have : IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map q).op (𝟙 E))) :=
    precomposition_of_isIso _ _ E
  infer_instance

private theorem precomposition_target_iso
    {A : Type*} [Category A] (H : Aᵒᵖ × A ⥤ A)
    {P Q E E' : A} (a : P ⟶ Q) (e : E ≅ E')
    (ha : IsIso (H.map (Prod.mkHom a.op (𝟙 E)))) : IsIso (H.map (Prod.mkHom a.op (𝟙 E'))) := by
  exact (NatIso.isIso_map_iff ((Functor.curry.obj H).flip.mapIso e) a.op).mp ha

private theorem tensor_precomposition_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (P L : ringedSiteComplex O)
    (hP : P.IsKFlatTensor) (hL : L.IsKFlatTensor)
    (a : P ⟶ ringedSiteRingComplex O) (b : L ⟶ ringedSiteRingComplex O)
    (E : ringedSiteDerived O)
    (ha : IsIso ((derivedInternalHom J O).map (Prod.mkHom (DerivedCategory.Q.map a).op (𝟙 E))))
    (hb : IsIso ((derivedInternalHom J O).map (Prod.mkHom (DerivedCategory.Q.map b).op (𝟙 E)))) :
    IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map ((KFlatRHom.total O).map
        (X := (P, L)) (Y := (ringedSiteRingComplex O, ringedSiteRingComplex O))
        (a, b))).op (𝟙 E))) := by
  let Q := DerivedCategory.Q (C := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let H := derivedInternalHom J O
  let P' : (KFlatRHom.flat O).FullSubcategory := ⟨P, hP⟩
  let L' : (KFlatRHom.flat O).FullSubcategory := ⟨L, hL⟩
  let U : (KFlatRHom.flat O).FullSubcategory :=
    ⟨ringedSiteRingComplex O, ringComplex_kflat O⟩
  let a' : P' ⟶ U := ObjectProperty.homMk a
  let b' : L' ⟶ U := ObjectProperty.homMk b
  let X := (op U, (op U, E))
  let Y := (op P', (op L', E))
  let f : X ⟶ Y := (a'.op, (b'.op, 𝟙 E))
  have : IsIso (ringedDerivedHomUnit O E) := derivedHomUnit_isIso O E
  have houter : IsIso (H.map (Prod.mkHom (Q.map a).op
      (𝟙 (H.obj (op (Q.obj (ringedSiteRingComplex O)), E))))) :=
    precomposition_target_iso H (Q.map a) (asIso (ringedDerivedHomUnit O E)) ha
  have hinner : IsIso (H.map
      (X := (op (Q.obj P), H.obj (op (Q.obj (ringedSiteRingComplex O)), E)))
      (Y := (op (Q.obj P), H.obj (op (Q.obj L), E)))
      (𝟙 _, H.map (Prod.mkHom (Q.map b).op (𝟙 E)))) := by
    have := hb
    have : IsIso (Prod.mkHom (𝟙 (op (Q.obj P)))
        (H.map (Prod.mkHom (Q.map b).op (𝟙 E)))) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    infer_instance
  have hleft : IsIso ((KFlatRHom.left O).map f) := by
    change IsIso (H.map
      (Prod.mkHom (Q.map a).op (H.map (Prod.mkHom (Q.map b).op (𝟙 E)))))
    have heq : H.map
        (Prod.mkHom (Q.map a).op (H.map (Prod.mkHom (Q.map b).op (𝟙 E)))) =
        H.map (Prod.mkHom (Q.map a).op (𝟙 _)) ≫
          H.map (Prod.mkHom (𝟙 _) (H.map (Prod.mkHom (Q.map b).op (𝟙 E)))) := by
      rw [← H.map_comp]
      congr 1
      ext <;> simp
    rw [heq]
    exact IsIso.comp_isIso
  have hright := (NatIso.isIso_map_iff (KFlatRHom.curryIso O) f).mp hleft
  exact hright

private theorem cech_precomposition_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (E : ringedSiteDerived O)
    (hE : ∀ i, IsZero ((derivedInternalHom J O).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization O (b i))), E))) :
    IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map (ringedExtendedCech O r b).2).op (𝟙 E))) := by
  induction r with
  | zero =>
    change IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map (𝟙 (ringedSiteRingComplex O))).op (𝟙 E)))
    simp only [Functor.map_id, op_id, ← prod_id']
    infer_instance
  | succ r ih =>
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := (SheafOfModules.tensorClosed O).1.some
    let := (SheafOfModules.tensorClosed O).2.1.some
    let P := ringedLocalizationTwoTerm O (b 0)
    let L := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
    let a := ringedLocalizationTwoTermAugmentation O (b 0)
    let c := (ringedExtendedCech O r (fun i ↦ b i.succ)).2
    have ht := tensor_precomposition_isIso O P L
      (localizationFactor_kflat O (b 0)) (cech_kflat O r (fun i ↦ b i.succ)) a c E
      (localization_precomposition_isIso O (b 0) E (hE 0))
      (ih (fun i ↦ b i.succ) (fun i ↦ hE i.succ))
    change IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map
        (HomologicalComplex.tensorHom a c ≫
          (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom)).op (𝟙 E)))
    rw [Functor.map_comp, precomposition_comp]
    rw [total_map O] at ht
    have : IsIso ((derivedInternalHom J O).map
        (Prod.mkHom (DerivedCategory.Q.map (HomologicalComplex.tensorHom a c)).op (𝟙 E))) := ht
    have : IsIso ((derivedInternalHom J O).map
        (Prod.mkHom (DerivedCategory.Q.map (HomologicalComplex.leftUnitor
          (ringedSiteRingComplex O)).hom).op (𝟙 E))) :=
      precomposition_of_isIso _ _ E
    infer_instance

private theorem derived_isIso_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [∀ U : C, (SheafOfModules.overFunctor.{u} R U).Additive]
    [∀ U : C, PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U)]
    [∀ U : C, PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    {A : Type u} (U : A → C) (hU : J.CoversTop U)
    {X Y : DerivedCategory (SheafOfModules.{u} R)} (g : X ⟶ Y)
    (hg : ∀ a, IsIso ((SheafOfModules.overFunctor.{u} R (U a)).mapDerivedCategory.map g)) :
    IsIso g := by
  apply (DerivedCategory.isIso_iff _ g).mpr
  intro n
  have hsheaf : IsIso ((SheafOfModules.toSheaf R).map
      ((DerivedCategory.homologyFunctor _ n).map g)) := by
    apply Sheaf.isIso_of_coversTop hU
      (f := (SheafOfModules.toSheaf R).map ((DerivedCategory.homologyFunctor _ n).map g))
    intro a
    let F := SheafOfModules.overFunctor.{u} R (U a)
    have : IsIso (F.mapDerivedCategory.map g) := hg a
    have hhom : IsIso ((DerivedCategory.homologyFunctor _ n).map
        (F.mapDerivedCategory.map g)) := inferInstance
    have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).mpr (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          (F.mapDerivedCategory.map g))
        exact hhom)
    change IsIso ((SheafOfModules.toSheaf (R.over (U a))).map
      (F.map ((DerivedCategory.homologyFunctor _ n).map g)))
    infer_instance
  have := hsheaf
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

/-- A locally derived complete object has invertible augmented extended Cech unit.

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(blueprint: lem-weil-pbc-extended-cech-complete-implies-unit-isIso). -/
theorem ringedExtendedCech_complete_implies_unit_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsLocallyDerivedRingedIdealComplete O I ι E →
      IsIso (ringedCechCompletionUnit O K ε E) := by
  intro hE
  classical
  let (U : C) : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  have : IsIso (ringedDerivedHomUnit O E) := derivedHomUnit_isIso O E
  change IsIso (ringedDerivedHomUnit O E ≫
    (derivedInternalHom J O).map (Prod.mkHom (DerivedCategory.Q.map ε).op (𝟙 E)))
  have hg : IsIso ((derivedInternalHom J O).map
      (Prod.mkHom (DerivedCategory.Q.map ε).op (𝟙 E))) := by
    apply derived_isIso_of_cover ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      (fun a : RingedIdealGeneratingIndex O I ι ↦ a.U)
      (coversTop_ringedIdealGeneratingIndex O I ι)
      ((derivedInternalHom J O).map (Prod.mkHom (DerivedCategory.Q.map ε).op (𝟙 E)))
    intro a
    let V := ringedDerivedRestriction O a.U
    let H := derivedInternalHom (J.over a.U) (O.over a.U)
    let F := (Functor.curry.obj H).flip.obj (V.obj E)
    let b := fun i ↦ ringedSliceSection O a.U (a.f i)
    have hlocal : IsIso (F.map
        (DerivedCategory.Q.map (ringedExtendedCech (O.over a.U) a.r b).2).op) := by
      apply cech_precomposition_isIso (O.over a.U) a.r b (V.obj E)
      intro i
      apply hE a.U (a.f i)
      obtain ⟨σ, e, he⟩ := a.generates
      refine ⟨(σ.s (e.symm i)).val (op (Over.mk (𝟙 a.U))), ?_⟩
      have hi := he (e.symm i)
      change ι.val.app (op a.U) ((σ.s (e.symm i)).val (op (Over.mk (𝟙 a.U)))) =
        a.f (e (e.symm i)) at hi
      simpa only [Equiv.apply_symm_apply] using hi
    obtain ⟨eK, heK⟩ := hK a.U a.r a.f a.generates
    let o := ringedDerivedRingRestrictionIso O a.U
    have heq : V.map (DerivedCategory.Q.map ε) ≫ o.hom =
        eK.inv ≫ DerivedCategory.Q.map
          (ringedExtendedCech (O.over a.U) a.r b).2 := by
      dsimp only [V, o]
      rw [← heK, Iso.inv_hom_id_assoc]
    have hcomp : IsIso (F.map (V.map (DerivedCategory.Q.map ε) ≫ o.hom).op) := by
      rw [heq, op_comp, F.map_comp]
      infer_instance
    have hpre : IsIso (F.map (V.map (DerivedCategory.Q.map ε)).op) := by
      rw [op_comp, F.map_comp] at hcomp
      exact IsIso.of_isIso_comp_left (F.map o.hom.op) _
    obtain ⟨eHom, _, _⟩ := ringedInternalHom_restriction J O
    exact (NatIso.isIso_map_iff (eHom a.U)
      (Prod.mkHom (DerivedCategory.Q.map ε).op (𝟙 E))).mpr (by
        change IsIso (H.map
          (Prod.mkHom (V.map (DerivedCategory.Q.map ε)).op (V.map (𝟙 E))))
        simpa only [F, Functor.flip_obj_map, Functor.curry_obj_map_app, Functor.map_id]
          using hpre)
  exact IsIso.comp_isIso

end CategoryTheory
