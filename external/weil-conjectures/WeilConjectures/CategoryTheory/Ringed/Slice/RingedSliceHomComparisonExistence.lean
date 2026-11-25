/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import all WeilConjectures.Algebra.Homology.ProperBaseChange.RestrictedCoefficientHomComplexSupplement
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Normalized internal-Hom comparison for slice restriction

Source: Stacks Project, Tags 08JB, 08FI and 0A95.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

private abbrev ModuleSheaf := SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)

private theorem ordinaryHomComparison_eq
    (L I : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ) :
    ringedSiteOrdinaryHomComparison.{c, v, u, w} J A L I =
      DerivedCategory.Q.map (((homComplexFunctor (R := A)).obj (op L)).map
        (coefficientHomAugmentation.{c, v, u} J A I)) ≫
        (coefficientHomResolutionIso.{u, c, v, w} J A L I).inv := by
  simp only [ringedSiteOrdinaryHomComparison, ringedSiteHomComplexMap, op_id,
    Functor.map_id, NatTrans.id_app]
  rfl

namespace RingedHomUniverses

private theorem ordinaryComparison_isIso (L M : Complex.{c, v, u} J A)
    [M.IsKInjective] :
    IsIso ((ordinaryComparison.{c, v, u, w} J A).app (op L, M)) := by
  rw [ordinaryComparison_app]
  exact comparison_isIso_of_kInjective.{c, v, u, w} J A L M

end RingedHomUniverses

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor

set_option backward.isDefEq.respectTransparency.types false

private structure ProductHomData
    {D : Type*} [Category D] [Preadditive D] (hObj : D → D → D)
    (hMap : ∀ {A A' B B' : D}, (A' ⟶ A) → (B ⟶ B') → (hObj A B ⟶ hObj A' B'))
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (π : ∀ (L M : CochainComplex D ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj M).X n ⟶ hObj (L.X p) (M.X q))) : Prop where
  isLimit : ∀ L M n, Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
    (fun p : ℤ ↦ π L M n p (p + n) rfl)))
  d_π : ∀ (L M : CochainComplex D ℤ) (n m p q q' p' : ℤ)
    (_hnm : n + 1 = m) (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
    ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ hMap (𝟙 (L.X p)) (M.d q' q) -
        n.negOnePow • (π L M n p' q hp' ≫ hMap (L.d p p') (𝟙 (M.X q)))
  map_π : ∀ {L L' M M' : CochainComplex D ℤ} (f : L' ⟶ L) (g : M ⟶ M')
    (n p q : ℤ) (h : p + n = q),
    (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q h =
      π L M n p q h ≫ hMap (f.f p) (g.f q)

private structure ProductHomInterface (D : Type a) [Category* D] [Preadditive D] where
  obj : D → D → D
  map : ∀ {A A' B B' : D}, (A' ⟶ A) → (B ⟶ B') → (obj A B ⟶ obj A' B')
  complex : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ
  π : ∀ (L M : CochainComplex D ℤ) (n p q : ℤ), p + n = q →
    (((complex.obj (op L)).obj M).X n ⟶ obj (L.X p) (M.X q))
  data : ProductHomData obj map complex π

private theorem productHomRestrictionComparison
    {D E : Type a} [Category* D] [Category* E] [Preadditive D] [Preadditive E]
    (r : D ⥤ E) [r.Additive] [PreservesLimitsOfShape (Discrete ℤ) r]
    (hObj : D → D → D) (hObjU : E → E → E)
    (hMap : ∀ {A A' B B' : D}, (A' ⟶ A) → (B ⟶ B') → (hObj A B ⟶ hObj A' B'))
    (hMapU : ∀ {A A' B B' : E}, (A' ⟶ A) → (B ⟶ B') → (hObjU A B ⟶ hObjU A' B'))
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (FU : (CochainComplex E ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (sπ : ∀ (L M : CochainComplex D ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ hObj (L.X p) (M.X q)))
    (tπ : ∀ (L M : CochainComplex E ℤ) (n p q : ℤ), p + n = q →
      (((FU.obj (op L)).obj M).X n ⟶ hObjU (L.X p) (M.X q)))
    (s : ProductHomData hObj hMap F sπ) (t : ProductHomData hObjU hMapU FU tπ)
    (c : ∀ A B : D, r.obj (hObj A B) ≅ hObjU (r.obj A) (r.obj B))
    (hc : ∀ {A A' B B' : D} (f : A' ⟶ A) (g : B ⟶ B'),
      r.map (hMap f g) ≫ (c A' B').hom =
        (c A B).hom ≫ hMapU (r.map f) (r.map g)) :
    ∃ γ : Functor.uncurry.obj F ⋙ r.mapHomologicalComplex (.up ℤ) ≅
        ((r.mapHomologicalComplex (.up ℤ)).op.prod
          (r.mapHomologicalComplex (.up ℤ))) ⋙ Functor.uncurry.obj FU,
      ∀ (L M : CochainComplex D ℤ) (n p q : ℤ) (h : p + n = q),
        (γ.hom.app (op L, M)).f n ≫
          tπ ((r.mapHomologicalComplex (.up ℤ)).obj L)
            ((r.mapHomologicalComplex (.up ℤ)).obj M) n p q h =
          r.map (sπ L M n p q h) ≫ (c (L.X p) (M.X q)).hom := by
  let rc := r.mapHomologicalComplex (.up ℤ)
  let aπ (L M : CochainComplex D ℤ) (n p q : ℤ) (h : p + n = q) :=
    r.map (sπ L M n p q h) ≫ (c (L.X p) (M.X q)).hom
  have hπr (L M : CochainComplex D ℤ) (n : ℤ) :
      IsLimit (Fan.mk (r.obj (((F.obj (op L)).obj M).X n))
        (fun p ↦ aπ L M n p (p + n) rfl)) := by
    let h := isLimitFanMkObjOfIsLimit r _ _ (s.isLimit L M n).some
    let e : Discrete.functor
        (fun p : ℤ ↦ r.obj (hObj (L.X p) (M.X (p + n)))) ≅
        Discrete.functor
          (fun p : ℤ ↦ hObjU (r.obj (L.X p)) (r.obj (M.X (p + n)))) :=
      Discrete.natIso (fun p : Discrete ℤ ↦ c (L.X p.as) (M.X (p.as + n)))
    exact (IsLimit.postcomposeHomEquiv e _).symm h
  have hE (L M : CochainComplex D ℤ) :
      ∃ e : rc.obj ((F.obj (op L)).obj M) ≅ (FU.obj (op (rc.obj L))).obj (rc.obj M),
        ∀ (n p q : ℤ) (h : p + n = q),
          e.hom.f n ≫ tπ (rc.obj L) (rc.obj M) n p q h = aπ L M n p q h := by
    apply SheafOfModules.productComplexComparison
      (rc.obj ((F.obj (op L)).obj M)) ((FU.obj (op (rc.obj L))).obj (rc.obj M))
      (fun p q ↦ hObjU (r.obj (L.X p)) (r.obj (M.X q)))
      (aπ L M) (tπ (rc.obj L) (rc.obj M)) (hπr L M) (fun n ↦ (t.isLimit _ _ n).some)
      (fun p q q' ↦ hMapU (𝟙 (r.obj (L.X p))) (r.map (M.d q' q)))
      (fun p p' q ↦ hMapU (r.map (L.d p p')) (𝟙 (r.obj (M.X q))))
    · intro n m p q q' p' hnm hpq hq' hp'
      exact SheafOfModules.mapTwoTermDifferential r _ _ _ _ _ _ _ _ _ _ _ _
        (s.d_π L M n m p q q' p' hnm hpq hq' hp')
        (by simpa only [r.map_id] using hc (𝟙 (L.X p)) (M.d q' q))
        (by simpa only [r.map_id] using hc (L.d p p') (𝟙 (M.X q)))
    · exact t.d_π (rc.obj L) (rc.obj M)
  choose e he using hE
  refine ⟨NatIso.ofComponents (fun X ↦ e X.1.unop X.2) ?_, he⟩
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (t.isLimit (rc.obj Y.1.unop) (rc.obj Y.2) n).some
  intro p
  let sourceMap := (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
  let targetMap := (FU.map (rc.map f.1.unop).op).app (rc.obj X.2) ≫
    (FU.obj (op (rc.obj Y.1.unop))).map (rc.map f.2)
  change (r.map (sourceMap.f n) ≫ (e Y.1.unop Y.2).hom.f n) ≫
      tπ (rc.obj Y.1.unop) (rc.obj Y.2) n p (p + n) rfl =
    ((e X.1.unop X.2).hom.f n ≫ targetMap.f n) ≫
      tπ (rc.obj Y.1.unop) (rc.obj Y.2) n p (p + n) rfl
  exact SheafOfModules.projectionIntertwine r (sourceMap.f n)
    (sπ X.1.unop X.2 n p (p + n) rfl)
    (sπ Y.1.unop Y.2 n p (p + n) rfl)
    (hMap (f.1.unop.f p) (f.2.f (p + n)))
    (targetMap.f n)
    (tπ (rc.obj X.1.unop) (rc.obj X.2) n p (p + n) rfl)
    (tπ (rc.obj Y.1.unop) (rc.obj Y.2) n p (p + n) rfl)
    (hMapU (r.map (f.1.unop.f p)) (r.map (f.2.f (p + n))))
    ((e X.1.unop X.2).hom.f n) ((e Y.1.unop Y.2).hom.f n)
    ((c (X.1.unop.X p) (X.2.X (p + n))).hom)
    ((c (Y.1.unop.X p) (Y.2.X (p + n))).hom)
    (s.map_π f.1.unop f.2 n p (p + n) rfl)
    (t.map_π (rc.map f.1.unop) (rc.map f.2) n p (p + n) rfl)
    (he X.1.unop X.2 n p (p + n) rfl) (he Y.1.unop Y.2 n p (p + n) rfl)
    (hc (f.1.unop.f p) (f.2.f (p + n)))

private theorem bundledProductHomRestrictionComparison
    {D E : Type a} [Category* D] [Category* E] [Preadditive D] [Preadditive E]
    (r : D ⥤ E) [r.Additive] [PreservesLimitsOfShape (Discrete ℤ) r]
    (s : ProductHomInterface D) (t : ProductHomInterface E)
    (c : ∀ A B : D, r.obj (s.obj A B) ≅ t.obj (r.obj A) (r.obj B))
    (hc : ∀ {A A' B B' : D} (f : A' ⟶ A) (g : B ⟶ B'),
      r.map (s.map f g) ≫ (c A' B').hom =
        (c A B).hom ≫ t.map (r.map f) (r.map g)) :
    ∃ γ : Functor.uncurry.obj s.complex ⋙ r.mapHomologicalComplex (.up ℤ) ≅
        ((r.mapHomologicalComplex (.up ℤ)).op.prod
          (r.mapHomologicalComplex (.up ℤ))) ⋙ Functor.uncurry.obj t.complex,
      ∀ (L M : CochainComplex D ℤ) (n p q : ℤ) (h : p + n = q),
        (γ.hom.app (op L, M)).f n ≫
          t.π ((r.mapHomologicalComplex (.up ℤ)).obj L)
            ((r.mapHomologicalComplex (.up ℤ)).obj M) n p q h =
          r.map (s.π L M n p q h) ≫ (c (L.X p) (M.X q)).hom :=
  productHomRestrictionComparison r s.obj t.obj
    (fun f g ↦ s.map f g) (fun f g ↦ t.map f g)
    s.complex t.complex s.π t.π s.data t.data c hc

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem nativeHomData : ProductHomData
    (fun M N : ModuleSheaf.{c, v, u} J A ↦
      SheafOfModules.homObj.{max c v u, v, c, max c v u} (R := A) M N)
    (fun {_M _M' _N _N' : ModuleSheaf.{c, v, u} J A} f g ↦
      SheafOfModules.homObjMap.{max c v u, v, c, max c v u} (R := A) f g)
    (homComplexFunctor.{c, v, max c v u, max c v u} (R := A))
    (homComplexπ.{c, v, max c v u, max c v u} (R := A)) :=
  { isLimit := fun L M n ↦ ⟨homComplexIsLimit.{c, v, max c v u, max c v u}
      (R := A) L M n⟩
    d_π := homComplex_d_π.{c, v, max c v u, max c v u} (R := A)
    map_π := fun f g ↦ homComplexFunctor_map_f_π.{c, v, max c v u, max c v u}
      (R := A) f g }

omit [HasDerivedCategory.{w} (ModuleSheaf.{c, v, u} J A)]
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private def nativeHomInterface : ProductHomInterface (ModuleSheaf.{c, v, u} J A) :=
  { obj := fun M N ↦ SheafOfModules.homObj (R := A) M N
    map := fun f g ↦ SheafOfModules.homObjMap (R := A) f g
    complex := homComplexFunctor.{c, v, max c v u, max c v u} (R := A)
    π := homComplexπ.{c, v, max c v u, max c v u} (R := A)
    data := nativeHomData.{c, v, u} J A }

section HomRestriction

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

variable (U : C)

private abbrev nativeRestriction : ModuleSheaf.{c, v, u} J A ⥤
    ModuleSheaf.{max c v, v, u} (J.over U) (A.over U) :=
  SheafOfModules.localizedSystemRestriction.{c, v, u} A U

private def overValIso (F : ModuleSheaf.{c, v, u} J A) :
    ((nativeRestriction.{c, v, u} J A U).obj F).val ≅
      (PresheafOfModules.restrictOver A.obj U).obj F.val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency true in
private def homOverIso (F G : ModuleSheaf.{c, v, u} J A) :
    (nativeRestriction.{c, v, u} J A U).obj ((nativeHomInterface.{c, v, u} J A).obj F G) ≅
      (nativeHomInterface.{max c v, v, u} (J.over U) (A.over U)).obj
        ((nativeRestriction.{c, v, u} J A U).obj F)
        ((nativeRestriction.{c, v, u} J A U).obj G) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    overValIso.{c, v, u} J A U (SheafOfModules.homObj (R := A) F G) ≪≫
    PresheafOfModules.restrictOverHomObjIso (R := A.obj) F.val G.val U ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget U).op ⋙ A.obj)).mapIso
      (overValIso.{c, v, u} J A U F).op).app _ ≪≫
    ((PresheafOfModules.homFunctor ((Over.forget U).op ⋙ A.obj)).obj
      (op ((nativeRestriction.{c, v, u} J A U).obj F).val)).mapIso
        (overValIso.{c, v, u} J A U G).symm

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
set_option backward.isDefEq.respectTransparency true in
private theorem homOverIso_naturality
    {F F' G G' : ModuleSheaf.{c, v, u} J A} (f : F' ⟶ F) (g : G ⟶ G') :
    (nativeRestriction.{c, v, u} J A U).map ((nativeHomInterface.{c, v, u} J A).map f g) ≫
        (homOverIso.{c, v, u} J A U F' G').hom =
      (homOverIso.{c, v, u} J A U F G).hom ≫
        (nativeHomInterface.{max c v, v, u} (J.over U) (A.over U)).map
          ((nativeRestriction.{c, v, u} J A U).map f)
          ((nativeRestriction.{c, v, u} J A U).map g) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro Y
  ext x
  rfl

private theorem homComparison_local
    (L M : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ)
    (γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj
        (homComplex (R := A) L M) ≅
      homComplex (R := A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj M))
    (hγ : ∀ (n p q : ℤ) (h : p + n = q), γ.hom.f n ≫
      homComplexπ (R := A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj M) n p q h =
      (homComplexπ (R := A) L M n p q h).over U ≫
        (homOverIso.{c, v, u} J A U (L.X p) (M.X q)).hom)
    (n p q : ℤ) (h : p + n = q) (X : Over U) (Y : Over X)
    (x : (L.X p).val.obj (op Y.left.left))
    (z : ((homComplex (R := A) L M).X n).val.obj (op X.left)) :
    (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj M) n p q h).val.app (op X)
        ((γ.hom.f n).val.app (op X) z)).app
          (op Y)).hom x =
      (((coefficientHomComponent.{u, c, v} J A L M n p q h).val.app (op X.left) z).app
        (op (Over.mk Y.hom.left))).hom x := by
  have hh := congrArg (fun f :
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj
        (homComplex (R := A) L M)).X n ⟶
          SheafOfModules.homObj (R := A.over U)
            (((ringedSliceComplexRestriction.{c, v, u} J A U).obj L).X p)
            (((ringedSliceComplexRestriction.{c, v, u} J A U).obj M).X q) ↦
      ((f.val.app (op X) z).app (op Y)).hom x) (hγ n p q h)
  exact hh

attribute [local irreducible] homOverIso

set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency.types false in
attribute [local semireducible] homComplexFunctor
set_option backward.isDefEq.respectTransparency.types false in
-- Cache the inferred proof type without elaborating the concrete interface twice.
set_option linter.defProp false in
private def sheafHomRestrictionComparison :=
  let V := nativeRestriction.{c, v, u} J A U
  letI hLim : PreservesLimitsOfSize.{0, 0} V :=
    (SheafOfModules.localizedSystemAdjunction.{c, v, u} A U).rightAdjoint_preservesLimits
  letI hAdd : V.Additive := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  let hShape : PreservesLimitsOfShape (Discrete ℤ) V :=
    hLim.preservesLimitsOfShape
  @bundledProductHomRestrictionComparison
    (ModuleSheaf.{c, v, u} J A)
    (ModuleSheaf.{max c v, v, u} (J.over U) (A.over U))
    inferInstance inferInstance inferInstance inferInstance V hAdd hShape
    (nativeHomInterface.{c, v, u} J A)
    (nativeHomInterface.{max c v, v, u} (J.over U) (A.over U))
    (homOverIso.{c, v, u} J A U)
    (by
      intro F F' G G' f g
      set_option backward.isDefEq.respectTransparency.types false in
        exact homOverIso_naturality.{c, v, u} J A U f g)

end HomRestriction

set_option backward.isDefEq.respectTransparency.types false

private theorem isoDescendByResolution
    {K D E : Type*} [Category K] [Category D] [Category E]
    (W : MorphismProperty K) (Q : K ⥤ D) [Q.IsLocalization W]
    (F G : D ⥤ E) (X : K ⥤ E) (a : X ⟶ Q ⋙ F) (b : X ⟶ Q ⋙ G)
    (I : K ⥤ K) (θ : 𝟭 K ⟶ I)
    [IsIso (Functor.whiskerRight θ (Q ⋙ F))]
    [IsIso (Functor.whiskerRight θ (Q ⋙ G))]
    [IsIso (Functor.whiskerLeft I a)] [IsIso (Functor.whiskerLeft I b)] :
    ∃ e : F ≅ G, a ≫ Functor.whiskerLeft Q e.hom = b := by
  let e₀ : Q ⋙ F ≅ Q ⋙ G :=
    asIso (Functor.whiskerRight θ (Q ⋙ F)) ≪≫
      (asIso (Functor.whiskerLeft I a)).symm ≪≫
      asIso (Functor.whiskerLeft I b) ≪≫
      (asIso (Functor.whiskerRight θ (Q ⋙ G))).symm
  have he₀ : a ≫ e₀.hom = b := by
    ext Z
    have : IsIso (a.app (I.obj Z)) :=
      NatIso.isIso_app_of_isIso (Functor.whiskerLeft I a) Z
    have : IsIso ((Q ⋙ G).map (θ.app Z)) :=
      NatIso.isIso_app_of_isIso (Functor.whiskerRight θ (Q ⋙ G)) Z
    dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [NatIso.isIso_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have ha : X.map (θ.app Z) ≫ a.app (I.obj Z) =
        a.app Z ≫ (Q ⋙ F).map (θ.app Z) := a.naturality (θ.app Z)
    have hb : X.map (θ.app Z) ≫ b.app (I.obj Z) =
        b.app Z ≫ (Q ⋙ G).map (θ.app Z) := b.naturality (θ.app Z)
    rw [← Category.assoc, ← ha]
    rw [Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc,
      hb, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  let e : F ≅ G := ff.preimageIso (X := F) (Y := G) e₀
  refine ⟨e, ?_⟩
  change a ≫ ((Functor.whiskeringLeft K D E).obj Q).map e.hom = b
  change a ≫ ((Functor.whiskeringLeft K D E).obj Q).map (ff.preimage e₀.hom) = b
  rw [ff.map_preimage]
  exact he₀

private theorem isIsoWhiskerRightComp
    {D E F G : Type*} [Category D] [Category E] [Category F] [Category G]
    {A B : D ⥤ E} (θ : A ⟶ B) (Q : E ⥤ F) (H : F ⥤ G)
    [IsIso (Functor.whiskerRight θ Q)] :
    IsIso (Functor.whiskerRight θ (Q ⋙ H)) :=
  Functor.isIso_whiskerRight (Functor.whiskerRight θ Q) H

private theorem homDescentEquation
    {K KU D DU : Type*} [Category K] [Category KU] [Category D] [Category DU]
    (Q : K ⥤ D) (QU : KU ⥤ DU) (r : D ⥤ DU) (RC : K ⥤ KU)
    (HC : Kᵒᵖ × K ⥤ K) (HCU : KUᵒᵖ × KU ⥤ KU)
    (H : Dᵒᵖ × D ⥤ D) (HU : DUᵒᵖ × DU ⥤ DU)
    (loc : Q ⋙ r ≅ RC ⋙ QU) (γ : HC ⋙ RC ≅ (RC.op.prod RC) ⋙ HCU)
    (a : HC ⋙ Q ⟶ (Q.op.prod Q) ⋙ H)
    (aU : HCU ⋙ QU ⟶ (QU.op.prod QU) ⋙ HU)
    (e : H ⋙ r ≅ (r.op.prod r) ⋙ HU)
    (he : Functor.whiskerRight a r ≫ Functor.whiskerLeft (Q.op.prod Q) e.hom =
      (Functor.isoWhiskerLeft HC loc ≪≫ Functor.isoWhiskerRight γ QU).hom ≫
        Functor.whiskerLeft (RC.op.prod RC) aU ≫
        (Functor.isoWhiskerRight (NatIso.prod (NatIso.op loc.symm) loc) HU).inv)
    (L M : K) :
    r.map (a.app (op L, M)) ≫ e.hom.app (op (Q.obj L), Q.obj M) =
      loc.hom.app (HC.obj (op L, M)) ≫ QU.map (γ.hom.app (op L, M)) ≫
        aU.app (op (RC.obj L), RC.obj M) ≫
          HU.map (Prod.mkHom (loc.hom.app L).op (loc.inv.app M)) := by
  have hh := congrArg (fun t ↦ t.app (op L, M)) he
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.prod_obj, Functor.op_obj,
    NatIso.prod, NatIso.op, NatTrans.prod, NatTrans.op, Iso.symm_inv,
    Category.assoc] using hh

private theorem homRestrictionDescent
    {K KU D DU : Type*} [Category K] [Category KU] [Category D] [Category DU]
    (Q : K ⥤ D) (QU : KU ⥤ DU) (r : D ⥤ DU) (RC : K ⥤ KU)
    (W : MorphismProperty (Kᵒᵖ × K)) [(Q.op.prod Q).IsLocalization W]
    (HC : Kᵒᵖ × K ⥤ K) (HCU : KUᵒᵖ × KU ⥤ KU)
    (H : Dᵒᵖ × D ⥤ D) (HU : DUᵒᵖ × DU ⥤ DU)
    (loc : Q ⋙ r ≅ RC ⋙ QU) (γ : HC ⋙ RC ≅ (RC.op.prod RC) ⋙ HCU)
    (cmp : HC ⋙ Q ⟶ (Q.op.prod Q) ⋙ H)
    (cmpU : HCU ⋙ QU ⟶ (QU.op.prod QU) ⋙ HU)
    (I : K ⥤ K) (η : 𝟭 K ⟶ I)
    (hη : ∀ M, IsIso (Q.map (η.app M)))
    (hcmp : ∀ L M, IsIso (cmp.app (op L, I.obj M)))
    (hcmpU : ∀ L M, IsIso (cmpU.app (op (RC.obj L), RC.obj (I.obj M)))) :
    ∃ e : H ⋙ r ≅ (r.op.prod r) ⋙ HU, ∀ L M : K,
      r.map (cmp.app (op L, M)) ≫ e.hom.app (op (Q.obj L), Q.obj M) =
        loc.hom.app (HC.obj (op L, M)) ≫ QU.map (γ.hom.app (op L, M)) ≫
          cmpU.app (op (RC.obj L), RC.obj M) ≫
            HU.map (Prod.mkHom (loc.hom.app L).op (loc.inv.app M)) := by
  let Γ : HC ⋙ Q ⋙ r ≅ (RC.op.prod RC) ⋙ HCU ⋙ QU :=
    Functor.isoWhiskerLeft HC loc ≪≫ Functor.isoWhiskerRight γ QU
  let δ : (Q.op.prod Q) ⋙ (r.op.prod r) ⋙ HU ≅
      (RC.op.prod RC) ⋙ (QU.op.prod QU) ⋙ HU :=
    Functor.isoWhiskerRight (NatIso.prod (NatIso.op loc.symm) loc) HU
  let a := Functor.whiskerRight cmp r
  let b : HC ⋙ Q ⋙ r ⟶ (Q.op.prod Q) ⋙ (r.op.prod r) ⋙ HU :=
    Γ.hom ≫ Functor.whiskerLeft (RC.op.prod RC)
      cmpU ≫ δ.inv
  let θ := NatTrans.prod (𝟙 (𝟭 Kᵒᵖ)) η
  let B := (𝟭 Kᵒᵖ).prod I
  have ht : IsIso (Functor.whiskerRight θ (Q.op.prod Q)) := by
    refine (NatTrans.isIso_iff_isIso_app (Functor.whiskerRight θ (Q.op.prod Q))).2 ?_
    intro X
    have := hη X.2
    change IsIso (Prod.mkHom (Q.map (𝟙 X.1.unop) |>.op) (Q.map (η.app X.2)))
    simp only [Functor.map_id]
    exact (isIso_prod_iff _ _).mpr ⟨inferInstance, hη X.2⟩
  have : IsIso (Functor.whiskerRight θ ((Q.op.prod Q) ⋙ H ⋙ r)) :=
    isIsoWhiskerRightComp θ (Q.op.prod Q) (H ⋙ r)
  have : IsIso (Functor.whiskerRight θ ((Q.op.prod Q) ⋙ (r.op.prod r) ⋙ HU)) :=
    isIsoWhiskerRightComp θ (Q.op.prod Q) ((r.op.prod r) ⋙ HU)
  have : IsIso (Functor.whiskerLeft B a) := by
    refine (NatTrans.isIso_iff_isIso_app (Functor.whiskerLeft B a)).2 ?_
    intro X
    have := hcmp X.1.unop X.2
    exact r.map_isIso (cmp.app (op X.1.unop, I.obj X.2))
  have : IsIso (Functor.whiskerLeft B b) := by
    refine (NatTrans.isIso_iff_isIso_app (Functor.whiskerLeft B b)).2 ?_
    intro X
    change IsIso (Γ.hom.app (B.obj X) ≫
      cmpU.app (op (RC.obj X.1.unop), RC.obj (I.obj X.2)) ≫ δ.inv.app (B.obj X))
    exact IsIso.comp_isIso' (Γ.app (B.obj X)).isIso_hom
      (IsIso.comp_isIso' (hcmpU X.1.unop X.2) (δ.app (B.obj X)).isIso_inv)
  obtain ⟨e, he⟩ := isoDescendByResolution W (Q.op.prod Q)
    (H ⋙ r) ((r.op.prod r) ⋙ HU) (HC ⋙ Q ⋙ r) a b B θ
  refine ⟨e, ?_⟩
  intro L M
  exact homDescentEquation Q QU r RC HC HCU H HU loc γ cmp cmpU e he L M

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  ringedSliceDerivedRestriction

set_option backward.isDefEq.respectTransparency true in
private theorem homDerivedComparison
    (U : C) [HasDerivedCategory.{w'}
      (ModuleSheaf.{max c v, v, u} (J.over U) (A.over U))]
    (γ : RingedHomUniverses.ordinaryBifunctor.{c, v, u} J A ⋙
        ringedSliceComplexRestriction.{c, v, u} J A U ≅
      ((ringedSliceComplexRestriction.{c, v, u} J A U).op.prod
        (ringedSliceComplexRestriction.{c, v, u} J A U)) ⋙
        RingedHomUniverses.ordinaryBifunctor.{max c v, v, u} (J.over U) (A.over U)) :
    ∃ e : derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙
        ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U ≅
      ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).op.prod
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U)) ⋙
          derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U),
      ∀ L M : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ,
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
            (ringedSiteOrdinaryHomComparison.{c, v, u, w} J A L M) ≫
            e.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) =
          (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app
              (homComplex (R := A) L M) ≫
            DerivedCategory.Q.map (γ.hom.app (op L, M)) ≫
            ringedSiteOrdinaryHomComparison.{max c v, v, u, w'} (J.over U) (A.over U)
              ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
              ((ringedSliceComplexRestriction.{c, v, u} J A U).obj M) ≫
            (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).map
              (Prod.mkHom ((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app L).op
                ((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).inv.app M)) := by
  let K := CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ
  let KU := CochainComplex (ModuleSheaf.{max c v, v, u} (J.over U) (A.over U)) ℤ
  let Q : K ⥤ DerivedCategory (ModuleSheaf.{c, v, u} J A) := DerivedCategory.Q
  let QU : KU ⥤ DerivedCategory (ModuleSheaf.{max c v, v, u} (J.over U) (A.over U)) :=
    DerivedCategory.Q
  let H := derivedInternalHomOfUniverses.{c, v, u, w} J A
  let HU := derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)
  let r := ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U
  let RC := ringedSliceComplexRestriction.{c, v, u} J A U
  let loc := ringedSliceLocalizationIso.{c, v, u, w, w'} J A U
  let HC := RingedHomUniverses.ordinaryBifunctor.{c, v, u} J A
  let HCU := RingedHomUniverses.ordinaryBifunctor.{max c v, v, u} (J.over U) (A.over U)
  let : IsGrothendieckAbelian.{max c v u} (ModuleSheaf.{c, v, u} J A) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  let I := coefficientHomResolution.{u, c, v} J A
  have hI (M : K) : (I.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M
  have hIU (M : K) : (RC.obj (I.obj M)).IsKInjective := by
    have := hI M
    exact isKInjective_restrict_localizedOfUniverses.{c, v, u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U inferInstance (I.obj M)
  obtain ⟨e, he⟩ := homRestrictionDescent Q QU r RC
    ((HomologicalComplex.quasiIso _ (.up ℤ)).op.prod
      (HomologicalComplex.quasiIso _ (.up ℤ))) HC HCU H HU loc γ
    (RingedHomUniverses.ordinaryComparison.{c, v, u, w} J A)
    (RingedHomUniverses.ordinaryComparison.{max c v, v, u, w'} (J.over U) (A.over U))
    I (ringedSiteHomAugmentation.{c, v, u} J A)
    (by
      intro M
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2)
    (by
      intro L M
      have := hI M
      exact RingedHomUniverses.ordinaryComparison_isIso.{c, v, u, w} J A L (I.obj M))
    (by
      intro L M
      have := hIU M
      exact RingedHomUniverses.ordinaryComparison_isIso.{max c v, v, u, w'}
        (J.over U) (A.over U) (RC.obj L) (RC.obj (I.obj M)))
  refine ⟨e, ?_⟩
  intro L M
  exact he L M

/-- Cancel the resolution comparison before specializing to the concrete Hom functor. -/
private theorem inverseComparisonModel {D : Type*} [Category D] {X Y Z : D}
    (a : X ≅ Y) (b : Y ≅ Z) (f : X ⟶ Z) (h : a.hom = f ≫ b.inv) :
    a.inv ≫ f = b.hom := by
  apply (cancel_epi a.hom).mp
  rw [Iso.hom_inv_id_assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem kInjectiveModel
    (L I : CochainComplex (ModuleSheaf.{c, v, u} J A) ℤ) [I.IsKInjective] :
    ∃ κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
          DerivedCategory.Q.obj (homComplex (R := A) L I),
      RingedKInjectiveHomModel.{c, v, u, w} J A L I κ ∧
        κ.inv = ringedSiteOrdinaryHomComparison.{c, v, u, w} J A L I := by
  let a := ringedSiteOrdinaryHomComparison.{c, v, u, w} J A L I
  have := RingedHomUniverses.comparison_isIso_of_kInjective.{c, v, u, w} J A L I
  let κ := (asIso a).symm
  refine ⟨κ, ?_, rfl⟩
  exact inverseComparisonModel (asIso a)
    (coefficientHomResolutionIso.{u, c, v, w} J A L I)
    (DerivedCategory.Q.map (((homComplexFunctor (R := A)).obj (op L)).map
      (coefficientHomAugmentation.{c, v, u} J A I)))
    (ordinaryHomComparison_eq.{c, v, u, w} J A L I)

private theorem modelSquare
    {D : Type*} [Category D] {A B C D' E G : D}
    (a : A ≅ B) (e : A ≅ C) (d : C ≅ D') (b : D' ≅ E)
    (l : B ⟶ G) (g : G ⟶ E)
    (h : a.inv ≫ e.hom = l ≫ g ≫ b.inv ≫ d.inv) :
    a.hom ≫ l ≫ g = e.hom ≫ d.hom ≫ b.hom := by
  have hh := congrArg (fun f ↦ a.hom ≫ f ≫ d.hom ≫ b.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using hh.symm

/-- The local-family comparison descends to derived Hom with its fixed augmentations.
Source: Stacks Project, Tags 08JB, 08FI, 0A8X and 0A95
(blueprint: lem-weil-pbc-ringed-slice-hom-comparison-existence).

Proof: relocalization identifies (C/U)/(V/U) with C/V, with identical covering
sieves. In degree n this identifies the product of local maps from L^p to I^(p+n)
on the two sites. The identification is natural in both complexes. The differential
is d_I h - (-1)^n h d_L on either side, so it is a chain isomorphism gamma with the
displayed component formula. Exact slice restriction preserves K-injectivity,
since it has an exact extension-by-zero left adjoint (08FI). Thus these complexes
compute both derived Homs. Localize the comparison using K-injective targets;
quasi-isomorphisms between K-injectives are homotopy equivalences and Hom into a
K-injective inverts quasi-isomorphisms in its first argument. The localization
universal property gives eta and its two-variable naturality. For an already
K-injective I, the map Hom(L,I) to Hom(L,I(I)) induced by the fixed augmentation
is a quasi-isomorphism. Compose the fixed localization factorization with its
inverse to obtain kappa, and do the same on the slice for kappa_U. Naturality of
gamma with respect to these augmentations gives exactly the last displayed
square. Zero complexes and empty covers require no separate hypothesis. -/
theorem ringedSlice_homComparison_exists
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))] :
    ∃ η : derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙
        ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U ≅
      ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).op.prod
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U)) ⋙
          derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U),
  ∀ (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
      u} RingCat.{max c v u})).obj A)) ℤ) [I.IsKInjective],
      ∃ (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
            (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
            DerivedCategory.Q.obj (homComplex (R := A) L I))
        (κU : (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj
          (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)) ≅
          DerivedCategory.Q.obj (homComplex (R := A.over U)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
        (γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj (homComplex (R := A) L I) ≅
          homComplex (R := A.over U) ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)),
        RingedKInjectiveHomModel.{c, v, u, w} J A L I κ ∧
        RingedKInjectiveHomModel.{max c v, v, u, w'} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) κU ∧
        (∀ (n p q : ℤ) (h : p + n = q) (V : Over U)
          (W : Over V) (x : (L.X p).val.obj (op W.left.left))
          (z : ((homComplex (R := A) L I).X n).val.obj (op V.left)),
          (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) n p q h).val.app (op V)
              ((γ.hom.f n).val.app (op V) z)).app (op W)).hom x =
          (((coefficientHomComponent.{u, c, v} J A L I n p q h).val.app (op V.left) z).app
            (op (Over.mk W.hom.left))).hom x) ∧
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map κ.hom ≫
          (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app (homComplex (R := A) L I) ≫
          DerivedCategory.Q.map γ.hom =
        η.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≫
          (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).map
            (X := (op ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
              (DerivedCategory.Q.obj L)), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
              (DerivedCategory.Q.obj I)))
            (Y := (op (DerivedCategory.Q.obj
              ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
              DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
            (((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).inv.app L).op,
              (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app I) ≫ κU.hom := by
  classical
  let M := ModuleSheaf.{c, v, u} J A
  let MU := ModuleSheaf.{max c v, v, u} (J.over U) (A.over U)
  let Q : CochainComplex M ℤ ⥤ DerivedCategory M := DerivedCategory.Q
  let QU : CochainComplex MU ℤ ⥤ DerivedCategory MU := DerivedCategory.Q
  let r := ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U
  let RC := ringedSliceComplexRestriction.{c, v, u} J A U
  let loc := ringedSliceLocalizationIso.{c, v, u, w, w'} J A U
  -- Share the witnesses without rebuilding the large dependent goal for each elimination.
  have hΓ := sheafHomRestrictionComparison.{c, v, u} J A U
  let Γ := hΓ.choose
  have hΓ := hΓ.choose_spec
  have hη := homDerivedComparison.{c, v, u, w, w'} J A U Γ
  let η := hη.choose
  have hη := hη.choose_spec
  refine ⟨η, ?_⟩
  intro L I hI
  have : (RC.obj I).IsKInjective :=
    isKInjective_restrict_localizedOfUniverses.{c, v, u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U inferInstance I
  have hκ := kInjectiveModel.{c, v, u, w} J A L I
  let κ := hκ.choose
  have hκinv := hκ.choose_spec.2
  have hκ := hκ.choose_spec.1
  have hκU := kInjectiveModel.{max c v, v, u, w'}
    (J.over U) (A.over U) (RC.obj L) (RC.obj I)
  let κU := hκU.choose
  have hκUinv := hκU.choose_spec.2
  have hκU := hκU.choose_spec.1
  let gammaIso : RC.obj (homComplex (R := A) L I) ≅
      homComplex (R := A.over U) (RC.obj L) (RC.obj I) := Γ.app (op L, I)
  refine ⟨κ, κU, gammaIso, hκ, hκU, ?_, ?_⟩
  · exact homComparison_local.{c, v, u} J A U L I gammaIso (hΓ L I)
  · have hh := congrArg (fun f ↦ r.map f ≫
      η.hom.app (op (Q.obj L), Q.obj I)) hκinv
    let HU := derivedInternalHomOfUniverses.{max c v, v, u, w'}
      (J.over U) (A.over U)
    let delta := (Functor.isoWhiskerRight
      (NatIso.prod (NatIso.op loc.symm) loc) HU).app (op L, I)
    have ht := congrArg (fun f ↦ loc.hom.app (homComplex (R := A) L I) ≫
      QU.map gammaIso.hom ≫ f ≫ HU.map
        (Prod.mkHom (loc.hom.app L).op (loc.inv.app I))) hκUinv
    have hhs : (r.mapIso κ).inv ≫ (η.app (op (Q.obj L), Q.obj I)).hom =
        loc.hom.app (homComplex (R := A) L I) ≫ QU.map gammaIso.hom ≫
          κU.inv ≫ delta.inv := by
      exact hh.trans ((hη L I).trans ht.symm)
    have hs := modelSquare (r.mapIso κ) (η.app (op (Q.obj L), Q.obj I))
      delta κU (loc.hom.app (homComplex (R := A) L I)) (QU.map gammaIso.hom) hhs
    change (r.mapIso κ).hom ≫ loc.hom.app (homComplex (R := A) L I) ≫
      QU.map gammaIso.hom =
        (η.app (op (Q.obj L), Q.obj I)).hom ≫ delta.hom ≫ κU.hom
    exact hs

end CategoryTheory
