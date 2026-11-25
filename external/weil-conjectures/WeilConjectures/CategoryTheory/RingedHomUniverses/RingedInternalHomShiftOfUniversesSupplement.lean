/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SignedRingedHom.RingedInternalHomSignedCalculus
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteOrdinaryHomComparison
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Tactic.Abel
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Normalized internal-Hom shifts with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 08JA and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
The existing restriction and signed small-site interfaces are reexported. The
normalizations below use the very same Hom complex, its fixed product projections,
and its fixed augmentation to the K-injective localization.

The private arguments first establish reindexing and cone comparisons for an
abstract product Hom complex. They then descend natural transformations through
localization, specialize the fixed sheaf Hom data, and prove normalization and
uniqueness. Keeping this algebra abstract avoids unfolding the concrete sheaf
Hom construction in every chain and triangle identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_neg_left
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (-f) g =
      -SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g := by
  apply SheafOfModules.hom_ext.{max c v r, v, c, max c v r}
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (-f.val) ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val =
    -((PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val)
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (-((f.val.app _).hom x))) =
    -((g.val.app _).hom) ((φ.app W).hom ((f.val.app _).hom x))
  erw [map_neg, map_neg]

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_units_smul_left
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (r : ℤˣ) (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (r • f) g =
      r • SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g := by
  rcases Int.units_eq_one_or r with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    exact homObjMap_neg_left.{c, v, r} f g

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem ordinaryLeftShiftAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hsmul : ∀ {X X' Y Y' : A} (a : ℤˣ) (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap (a • f) g = a • Hmap f g)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (L : CochainComplex A ℤ) (m : ℤ) :
    ∃ iso : ((F.obj (op L)) ⋙ shiftFunctor _ (-m)) ≅ F.obj (op (L⟦m⟧)),
      ∀ (M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
        (iso.app M).hom.f k ≫ π (L⟦m⟧) M k p q h =
          (m * k).negOnePow • (π L M (k + -m) (p + m) q (by omega) ≫
            Hmap
              (L.shiftFunctorObjXIso m p (p + m) rfl).hom (𝟙 (M.X q))) := by
  classical
  have hp (L M : CochainComplex A ℤ) (n : ℤ) := Classical.choice (hπ₁ L M n)
  let S := L⟦m⟧
  let K (M : CochainComplex A ℤ) := ((F.obj (op L)).obj M)⟦-m⟧
  let T (M : CochainComplex A ℤ) := (F.obj (op S)).obj M
  let a (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ⟶ (T M).X n :=
    Fan.IsLimit.lift (hp S M n) (fun p ↦
      (m * n).negOnePow • π L M (n - m) (p + m) (p + n) (by omega))
  have ha (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q) :
      a M n ≫ π S M n p q h =
        (m * n).negOnePow • π L M (n - m) (p + m) q (by omega) := by
    subst q
    exact Fan.IsLimit.fac (hp S M n) _ p
  let b (M : CochainComplex A ℤ) (n : ℤ) : (T M).X n ⟶ (K M).X n :=
    Fan.IsLimit.lift (hp L M (n - m)) (fun p ↦
      (m * n).negOnePow • (π S M n (p - m) (p + (n - m)) (by omega) ≫
        Hmap
          (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)))
  have hb (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + (n - m) = q) :
      b M n ≫ π L M (n - m) p q h =
        (m * n).negOnePow • (π S M n (p - m) q (by omega) ≫
          Hmap
            (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)) := by
    subst q
    exact Fan.IsLimit.fac (hp L M (n - m)) _ p
  have hπeq (Lc M : CochainComplex A ℤ) (n p p' q : ℤ)
      (h : p' = p) (hq : p + n = q) :
      π Lc M n p' q (by omega) ≫
          Hmap (Lc.XIsoOfEq h).inv (𝟙 _) = π Lc M n p q hq := by
    subst p'
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      hid, Category.comp_id]
  have hab (M : CochainComplex A ℤ) (n : ℤ) : a M n ≫ b M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp L M (n - m))
    intro p
    change (a M n ≫ b M n) ≫ π L M (n - m) p (p + (n - m)) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    rw [Category.assoc, hb, Linear.comp_units_smul, ← Category.assoc, ha]
    simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
    change _ = π L M (n - m) p (p + (n - m)) rfl
    exact hπeq L M (n - m) p (p - m + m) (p + (n - m)) (by omega) rfl
  have hba (M : CochainComplex A ℤ) (n : ℤ) : b M n ≫ a M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp S M n)
    intro p
    change (b M n ≫ a M n) ≫ π S M n p (p + n) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    rw [Category.assoc, ha, Linear.comp_units_smul, hb]
    simp only [smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
    change _ = π S M n p (p + n) rfl
    exact hπeq S M n p (p + m - m) (p + n) (by omega) rfl
  let e (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ≅ (T M).X n :=
    ⟨a M n, b M n, hab M n, hba M n⟩
  have hm (Lc M N : CochainComplex A ℤ) (f : M ⟶ N)
      (n p q : ℤ) (h : p + n = q) :
      ((F.obj (op Lc)).map f).f n ≫ π Lc N n p q h =
        π Lc M n p q h ≫ Hmap (𝟙 (Lc.X p)) (f.f q) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ₃ Lc Lc M N (𝟙 Lc) f n p q h
  have hc (M : CochainComplex A ℤ) (n k : ℤ) (h : n + 1 = k) :
      (e M n).hom ≫ (T M).d n k = (K M).d n k ≫ (e M k).hom := by
    subst k
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a ha ⊢
    apply Fan.IsLimit.hom_ext (hp S M (n + 1))
    intro p
    change (a M n ≫ (T M).d n (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl =
      (((-m).negOnePow • ((F.obj (op L)).obj M).d (n - m) (n + 1 - m)) ≫
        a M (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl
    rw [Category.assoc,
      hπ₂ S M n (n + 1) p (p + (n + 1)) (p + n) (p + 1)
        rfl rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
      ha M n p (p + n) rfl, ← Category.assoc,
      ha M n (p + 1) (p + (n + 1)) (by omega), Category.assoc]
    conv_rhs => rw [ha M (n + 1) p (p + (n + 1)) rfl]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
    rw [hπ₂ L M (n - m) (n + 1 - m) (p + m) (p + (n + 1)) (p + n) (p + 1 + m)
        (by omega) (by omega) (by omega) (by omega)]
    simp only [S, CochainComplex.shiftFunctor_obj_d']
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    conv_lhs =>
      rhs
      arg 2
      rhs
      rw [hsmul m.negOnePow
        (L.d (p + m) (p + 1 + m)) (𝟙 (M.X (p + (n + 1))))]
    simp only [Linear.comp_units_smul, smul_sub, smul_smul,
      Int.negOnePow_neg, Int.negOnePow_sub]
    have hs : (m * (n + 1)).negOnePow = (m * n).negOnePow * m.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    simp only [hs, mul_assoc, Int.units_mul_self, mul_one]
    rw [mul_left_comm n.negOnePow (m * n).negOnePow m.negOnePow]
  let iso : ((F).obj (op L) ⋙ shiftFunctor _ (-m)) ≅
      (F).obj (op (L⟦m⟧)) :=
    NatIso.ofComponents (fun M ↦
    HomologicalComplex.Hom.isoOfComponents (e M) (hc M)) (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    change ((F.obj (op L)).map f).f (n - m) ≫ a N n =
      a M n ≫ ((F.obj (op S)).map f).f n
    apply Fan.IsLimit.hom_ext (hp S N n)
    intro p
    change (((F.obj (op L)).map f).f (n - m) ≫ a N n) ≫
        π S N n p (p + n) rfl =
      (a M n ≫ ((F.obj (op S)).map f).f n) ≫ π S N n p (p + n) rfl
    rw [Category.assoc, ha, Linear.comp_units_smul, hm, Category.assoc, hm,
      ← Category.assoc, ha, Linear.units_smul_comp]
    rfl)
  refine ⟨iso, ?_⟩
  intro M k p q h
  change (a M k) ≫ π S M k p q h = _
  simp only [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    hid,
    Category.comp_id]
  exact ha M k p q h

private theorem ordinaryLeftShiftBifunctorAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hsmul : ∀ {X X' Y Y' : A} (a : ℤˣ) (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap (a • f) g = a • Hmap f g)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (m : ℤ) :
    ∃ iso : Functor.uncurry.obj F ⋙ shiftFunctor _ (-m) ≅
      ((shiftFunctor (CochainComplex A ℤ) m).op.prod (𝟭 _)) ⋙
        Functor.uncurry.obj F,
      ∀ (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
        (iso.app (op L, M)).hom.f k ≫ π (L⟦m⟧) M k p q h =
          (m * k).negOnePow • π L M (k + -m) (p + m) q (by omega) := by
  classical
  choose e he using fun L ↦
    ordinaryLeftShiftAux Hobj Hmap hid hsmul F π hπ₁ hπ₂ hπ₃ L m
  have hform (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q) :
      ((e L).hom.app M).f k ≫ π (L⟦m⟧) M k p q h =
        (m * k).negOnePow • π L M (k + -m) (p + m) q (by omega) := by
    simpa only [Iso.app_hom, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      hid,
      Category.comp_id] using he L M k p q h
  refine ⟨NatIso.ofComponents (fun X ↦ (e X.1.unop).app X.2) ?_, ?_⟩
  · intro X Y f
    apply HomologicalComplex.hom_ext
    intro k
    apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ (Y.1.unop⟦m⟧) Y.2 k))
    intro p
    change (((F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2).f (k + -m) ≫
        ((e Y.1.unop).hom.app Y.2).f k) ≫
        π (Y.1.unop⟦m⟧) Y.2 k p (p + k) rfl =
      (((e X.1.unop).hom.app X.2).f k ≫
        ((F.map (((shiftFunctor _ m).map f.1.unop).op)).app X.2 ≫
          (F.obj (op (Y.1.unop⟦m⟧))).map f.2).f k) ≫
          π (Y.1.unop⟦m⟧) Y.2 k p (p + k) rfl
    rw [Category.assoc, hform, Linear.comp_units_smul]
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    erw [hπ₃ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2
      (k + -m) (p + m) (p + k) (by omega)]
    rw [Category.assoc,
      hπ₃ (X.1.unop⟦m⟧) (Y.1.unop⟦m⟧) X.2 Y.2
        ((shiftFunctor _ m).map f.1.unop) f.2 k p (p + k) rfl,
      ← Category.assoc, hform, Linear.units_smul_comp]
    rfl
  · intro L M k p q h
    exact hform L M k p q h

private abbrev ordinaryBifunctor :=
  Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))

private noncomputable def productComparisonIso
    {D : Type*} [Category D] {ι : Type*} {A B : ι → D}
    (s : Limits.Fan A) (t : Limits.Fan B) (hs : Limits.IsLimit s) (ht : Limits.IsLimit t)
    (e : ∀ i, A i ≅ B i) : s.pt ≅ t.pt where
  hom := Limits.Fan.IsLimit.lift ht (fun i ↦ s.proj i ≫ (e i).hom)
  inv := Limits.Fan.IsLimit.lift hs (fun i ↦ t.proj i ≫ (e i).inv)
  hom_inv_id := by
    apply Limits.Fan.IsLimit.hom_ext hs
    intro i
    simp
  inv_hom_id := by
    apply Limits.Fan.IsLimit.hom_ext ht
    intro i
    simp

private lemma productComparisonIso_hom_proj
    {D : Type*} [Category D] {ι : Type*} {A B : ι → D}
    (s : Limits.Fan A) (t : Limits.Fan B) (hs : Limits.IsLimit s) (ht : Limits.IsLimit t)
    (e : ∀ i, A i ≅ B i) (i : ι) :
    (productComparisonIso s t hs ht e).hom ≫ t.proj i = s.proj i ≫ (e i).hom :=
  Limits.Fan.IsLimit.fac ht _ i

private lemma shiftSign_sub {A : Type*} [AddCommGroup A]
    (a b : A) (k n : ℤ) :
    n.negOnePow • a - k.negOnePow • b =
      n.negOnePow • (a - (k + n).negOnePow • b) := by
  rw [smul_sub n.negOnePow a ((k + n).negOnePow • b),
    smul_smul n.negOnePow (k + n).negOnePow b, Int.negOnePow_add,
    mul_left_comm, Int.units_mul_self, mul_one]

private noncomputable def homTargetIsoAux
    {A : Type*} [Category A] (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ (X Y Y' Y'' : A) (g : Y ⟶ Y') (h : Y' ⟶ Y''),
      Hmap (𝟙 X) g ≫ Hmap (𝟙 X) h = Hmap (𝟙 X) (g ≫ h))
    (X Y Y' : A) (e : Y ≅ Y') : Hobj X Y ≅ Hobj X Y' where
  hom := Hmap (𝟙 X) e.hom
  inv := Hmap (𝟙 X) e.inv
  hom_inv_id := by rw [hcomp, e.hom_inv_id, hid]
  inv_hom_id := by rw [hcomp, e.inv_hom_id, hid]

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem ordinaryRightShiftAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ (X Y Y' Y'' : A) (g : Y ⟶ Y') (h : Y' ⟶ Y''),
      Hmap (𝟙 X) g ≫ Hmap (𝟙 X) h = Hmap (𝟙 X) (g ≫ h))
    (hsmul : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y') (a : ℤˣ),
      Hmap f (a • g) = a • Hmap f g)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (n : ℤ) :
    ∃ iso : Functor.uncurry.obj F ⋙ shiftFunctor _ n ≅
      (𝟭 _).prod (shiftFunctor (CochainComplex A ℤ) n) ⋙ Functor.uncurry.obj F,
      ∀ (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
        (iso.app (op L, M)).hom.f k ≫ π L (M⟦n⟧) k p q h =
          π L M (k + n) p (q + n) (by omega) := by
  let e (L M : _) (k : ℤ) :=
    productComparisonIso
      (Limits.Fan.mk (((F.obj (op L)).obj M).X (k + n))
        (fun p ↦ π L M (k + n) p (p + (k + n)) rfl))
      (Limits.Fan.mk (((F.obj (op L)).obj (M⟦n⟧)).X k)
        (fun p ↦ π L (M⟦n⟧) k p (p + k) rfl))
      (hπ₁ L M (k + n)).some (hπ₁ L (M⟦n⟧) k).some
      (fun p ↦ homTargetIsoAux Hobj Hmap hid hcomp (L.X p) _ _
        (M.shiftFunctorObjXIso n (p + k) (p + (k + n)) (by omega)).symm)
  have hπinv (L M : _) (k p q q' : ℤ) (hpq : p + k = q) (h : q' = q) :
      π L M k p q hpq ≫
        Hmap (𝟙 (L.X p)) (M.XIsoOfEq h).inv =
      π L M k p q' (by omega) := by
    subst q'
    simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      hid] using Category.comp_id (π L M k p q hpq)
  have he (L M : _) (k p q : ℤ) (hpq : p + k = q) :
      (e L M k).hom ≫ π L (M⟦n⟧) k p q hpq =
        π L M (k + n) p (q + n) (by omega) := by
    subst q
    dsimp only [e]
    change (productComparisonIso _ _ _ _ _).hom ≫
      (Limits.Fan.mk (((F.obj (op L)).obj (M⟦n⟧)).X k)
        (fun p ↦ π L (M⟦n⟧) k p (p + k) rfl)).proj p = _
    rw [productComparisonIso_hom_proj]
    change π L M (k + n) p (p + (k + n)) rfl ≫
      Hmap (𝟙 (L.X p))
        (M.XIsoOfEq (show (p + k) + n = p + (k + n) by omega)).inv = _
    exact hπinv L M (k + n) p (p + (k + n)) ((p + k) + n) rfl (by omega)
  refine ⟨NatIso.ofComponents (fun X ↦
    HomologicalComplex.Hom.isoOfComponents (e X.1.unop X.2) ?_) ?_, ?_⟩
  · intro k l hkl
    have hkl' : k + 1 = l := hkl
    change (e X.1.unop X.2 k).hom ≫ ((F.obj X.1).obj (X.2⟦n⟧)).d k l =
      (n.negOnePow • ((F.obj X.1).obj X.2).d (k + n) (l + n)) ≫
        (e X.1.unop X.2 l).hom
    apply Limits.Fan.IsLimit.hom_ext (hπ₁ X.1.unop (X.2⟦n⟧) l).some
    intro p
    change ((e X.1.unop X.2 k).hom ≫ ((F.obj X.1).obj (X.2⟦n⟧)).d k l) ≫
      π X.1.unop (X.2⟦n⟧) l p (p + l) rfl =
      ((n.negOnePow • ((F.obj X.1).obj X.2).d (k + n) (l + n)) ≫
        (e X.1.unop X.2 l).hom) ≫ π X.1.unop (X.2⟦n⟧) l p (p + l) rfl
    erw [Category.assoc,
      hπ₂ X.1.unop (X.2⟦n⟧) k l p (p + l) (p + k) (p + 1)
        hkl' rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul]
    conv_lhs =>
      lhs
      erw [← Category.assoc, he X.1.unop X.2 k p (p + k) rfl]
    conv_lhs =>
      rhs
      erw [← Category.assoc, he X.1.unop X.2 k (p + 1) (p + l) (by omega)]
    conv_rhs =>
      erw [Category.assoc, he X.1.unop X.2 l p (p + l) rfl, Linear.units_smul_comp,
        hπ₂ X.1.unop X.2 (k + n) (l + n) p ((p + l) + n) ((p + k) + n) (p + 1)
          (by omega) (by omega) (by omega) (by omega)]
    simp only [CochainComplex.shiftFunctor_obj_d']
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    conv_lhs =>
      lhs
      erw [hsmul (𝟙 (X.1.unop.X p))
        (X.2.d ((p + k) + n) ((p + l) + n)) n.negOnePow, Linear.comp_units_smul]
    let a := π X.1.unop X.2 (k + n) p ((p + k) + n) (by omega) ≫
      Hmap (𝟙 (X.1.unop.X p))
        (X.2.d ((p + k) + n) ((p + l) + n))
    let b := π X.1.unop X.2 (k + n) (p + 1) ((p + l) + n) (by omega) ≫
      Hmap (X.1.unop.d p (p + 1))
        (𝟙 (X.2.X ((p + l) + n)))
    change n.negOnePow • a - k.negOnePow • b =
      n.negOnePow • (a - (k + n).negOnePow • b)
    exact shiftSign_sub a b k n
  · intro X Y f
    apply HomologicalComplex.hom_ext
    intro k
    apply Limits.Fan.IsLimit.hom_ext (hπ₁ Y.1.unop (Y.2⟦n⟧) k).some
    intro p
    change
      (((F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2).f (k + n) ≫
        (e Y.1.unop Y.2 k).hom) ≫ π Y.1.unop (Y.2⟦n⟧) k p (p + k) rfl =
      ((e X.1.unop X.2 k).hom ≫
        ((F.map f.1).app (X.2⟦n⟧) ≫ (F.obj Y.1).map (f.2⟦n⟧')).f k) ≫
        π Y.1.unop (Y.2⟦n⟧) k p (p + k) rfl
    conv_lhs =>
      erw [Category.assoc, he Y.1.unop Y.2 k p (p + k) rfl,
        hπ₃ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 (k + n) p ((p + k) + n)
          (by omega)]
    conv_rhs =>
      erw [Category.assoc,
        hπ₃ X.1.unop Y.1.unop (X.2⟦n⟧) (Y.2⟦n⟧) f.1.unop (f.2⟦n⟧') k p (p + k) rfl,
        ← Category.assoc, he X.1.unop X.2 k p (p + k) rfl]
    rfl
  · intro L M k p q h
    exact he L M k p q h

private theorem ordinaryRightCoherenceAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (e : ∀ n : ℤ, Functor.uncurry.obj F ⋙ shiftFunctor _ n ≅
      (𝟭 _).prod (shiftFunctor (CochainComplex A ℤ) n) ⋙ Functor.uncurry.obj F)
    (he : ∀ (n : ℤ) (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
      ((e n).app (op L, M)).hom.f k ≫ π L (M⟦n⟧) k p q h =
        π L M (k + n) p (q + n) (by omega)) :
    ∃ S : ∀ L : CochainComplex A ℤ, (F.obj (op L)).CommShift ℤ,
      (∀ {L L' : CochainComplex A ℤ} (f : L' ⟶ L),
        letI := S L
        letI := S L'
        NatTrans.CommShift (F.map f.op) ℤ) ∧
      ∀ (L M : CochainComplex A ℤ) (n k p q : ℤ) (h : p + k = q),
        (((S L).commShiftIso n).inv.app M).f k ≫ π L (M⟦n⟧) k p q h =
          π L M (k + n) p (q + n) (by omega) := by
  classical
  have htarget (L M M' : CochainComplex A ℤ) (g : M ⟶ M')
      (k p q : ℤ) (h : p + k = q) :
      ((F.obj (op L)).map g).f k ≫ π L M' k p q h =
        π L M k p q h ≫ Hmap (𝟙 _) (g.f q) := by
    have hh := hπ₃ L L M M' (𝟙 L) g k p q h
    simpa only [op_id, F.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hh
  have hπeq (L M : CochainComplex A ℤ) (k k' p q q' : ℤ)
      (hk : k = k') (hq : q' = q) (h : p + k = q) (h' : p + k' = q') :
      (((F.obj (op L)).obj M).XIsoOfEq hk).hom ≫ π L M k' p q' h' ≫
        Hmap (𝟙 _) (M.XIsoOfEq hq).hom = π L M k p q h := by
    subst k' q'
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, hid,
      Category.id_comp, Category.comp_id]
  let d (L : CochainComplex A ℤ) (n : ℤ) :
      F.obj (op L) ⋙ shiftFunctor _ n ≅ shiftFunctor _ n ⋙ F.obj (op L) :=
    NatIso.ofComponents (fun M ↦ (e n).app (op L, M)) (fun {M M'} f ↦ by
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_map,
        Functor.id_map, Functor.map_id, Functor.uncurry_obj_map,
        NatTrans.id_app, Category.id_comp, Functor.prod_obj, Functor.id_obj,
        Functor.uncurry_obj_obj, Iso.app_hom] using (e n).hom.naturality (Prod.mkHom (𝟙 (op L)) f))
  let S (L : CochainComplex A ℤ) : (F.obj (op L)).CommShift ℤ :=
    { commShiftIso := fun n ↦ (d L n).symm
      commShiftIso_zero := by
        apply Iso.ext_inv
        apply NatTrans.ext
        funext M
        apply HomologicalComplex.hom_ext
        intro k
        apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ L (M⟦(0 : ℤ)⟧) k))
        intro p
        rw [Functor.CommShift.isoZero_inv_app]
        dsimp only [d, Iso.symm_inv, NatIso.ofComponents_hom_app,
          HomologicalComplex.comp_f, Fan.proj, Fan.mk_π_app]
        rw [he 0 L M k p (p + k) rfl]
        simp only [Category.assoc, htarget,
          CochainComplex.shiftFunctorZero_hom_app_f,
          CochainComplex.shiftFunctorZero_inv_app_f]
        exact (hπeq L M (k + 0) k p ((p + k) + 0) (p + k)
          (by omega) (by omega) (by omega) rfl).symm
      commShiftIso_add := by
        intro a b
        apply Iso.ext_inv
        apply NatTrans.ext
        funext M
        apply HomologicalComplex.hom_ext
        intro k
        apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ L (M⟦a + b⟧) k))
        intro p
        rw [Functor.CommShift.isoAdd_inv_app]
        dsimp only [d, Iso.symm_inv, NatIso.ofComponents_hom_app,
          HomologicalComplex.comp_f, Fan.proj, Fan.mk_π_app]
        rw [he (a + b) L M k p (p + k) rfl]
        simp only [Category.assoc, htarget]
        rw [reassoc_of% he b L (M⟦a⟧) k p (p + k) rfl]
        erw [reassoc_of% he a L M (k + b) p ((p + k) + b) (by omega)]
        simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
          CochainComplex.shiftFunctorAdd_inv_app_f]
        exact (hπeq L M (k + (a + b)) ((k + b) + a) p
          ((p + k) + (a + b)) (((p + k) + b) + a)
          (by omega) (by omega) (by omega) (by omega)).symm }
  refine ⟨S, ?_, ?_⟩
  · intro L L' f
    let := S L
    let := S L'
    refine ⟨fun n ↦ ?_⟩
    apply NatTrans.ext
    funext M
    change (d L n).inv.app M ≫ ((F.map f.op).app M)⟦n⟧' =
      (F.map f.op).app (M⟦n⟧) ≫ (d L' n).inv.app M
    apply (cancel_epi ((d L n).hom.app M)).mp
    apply (cancel_mono ((d L' n).hom.app M)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    have hh := (e n).hom.naturality (Prod.mkHom f.op (𝟙 M))
    simpa only [d, NatIso.ofComponents_hom_app, Iso.app_hom,
      Functor.comp_map, Functor.uncurry_obj_map, Functor.comp_obj,
      Functor.prod_map, Functor.id_map, Functor.map_id, Functor.prod_obj,
      Functor.id_obj, Category.comp_id] using hh
  · intro L M n k p q h
    exact he n L M k p q h

open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency true in
private theorem targetShiftDescent
    {K E D : Type*} [Category K] [Category E] [Category D]
    [HasShift K ℤ] [HasShift E ℤ] [HasShift D ℤ]
    (Q : K ⥤ D) (W : MorphismProperty K) [Q.IsLocalization W]
    [W.ContainsIdentities] [Q.CommShift ℤ]
    (ι : E ⥤ K) [ι.CommShift ℤ] (V : MorphismProperty E)
    [(ι ⋙ Q).IsLocalization V] [V.ContainsIdentities]
    (U : Kᵒᵖ ⥤ K ⥤ K)
    [∀ L, (U.obj L).CommShift ℤ]
    [∀ {L L'} (f : L ⟶ L'), NatTrans.CommShift (U.map f) ℤ]
    (H : Dᵒᵖ ⥤ D ⥤ D)
    (α : U ⋙ (whiskeringRight K K D).obj Q ⟶
      Q.op ⋙ H ⋙ (whiskeringLeft K D D).obj Q)
    (hα : ∀ (L : Kᵒᵖ) (F : E), IsIso ((α.app L).app (ι.obj F)))
    (hres : ∀ F : K, ∃ (I : E) (f : F ⟶ ι.obj I), IsIso (Q.map f)) :
    ∃ S : ∀ M : D, (H.obj (op M)).CommShift ℤ,
      ∀ (M : D) (L : K) (eM : Q.obj L ≅ M),
        letI := S M
        NatTrans.CommShift
          (show U.obj (op L) ⋙ Q ⟶ Q ⋙ H.obj (op M) from
            α.app (op L) ≫ Functor.whiskerLeft Q (H.map eM.inv.op)) ℤ := by
  classical
  let F := U ⋙ (whiskeringLeft E K K).obj ι ⋙ (whiskeringRight E K D).obj Q
  let (L : Kᵒᵖ) : (F.obj L).CommShift ℤ := by
    change (ι ⋙ U.obj L ⋙ Q).CommShift ℤ
    infer_instance
  let {L L' : Kᵒᵖ} (f : L ⟶ L') : NatTrans.CommShift (F.map f) ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (Functor.whiskerLeft ι (Functor.whiskerRight (U.map f) Q)) ℤ)
  let β : F ≅ (((whiskeringLeft₂ D).obj Q.op).obj (ι ⋙ Q)).obj H :=
    NatIso.ofComponents (fun L ↦ NatIso.ofComponents
      (fun I ↦ by
        let := hα L I
        exact asIso ((α.app L).app (ι.obj I)))
      (fun f ↦ by
        simpa only [asIso_hom, F, Functor.comp_obj, Functor.comp_map,
          whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
          whiskeringLeft₂] using (α.app L).naturality (ι.map f))) (fun f ↦ by
        ext I
        exact congr_app (α.naturality f) (ι.obj I))
  let : Localization.Lifting₂ Q.op (ι ⋙ Q) W.op V F H := ⟨β.symm⟩
  let S (M : D) : (H.obj (op M)).CommShift ℤ :=
    Functor.CommShift₂OfLocalization.commShiftObj ℤ Q.op (ι ⋙ Q) W.op V F H (op M)
  refine ⟨S, ?_⟩
  intro M L eM
  let := S M
  let := S (Q.obj L)
  have : NatTrans.CommShift
      (Functor.CommShift₂OfLocalization.liftingIsoApp Q.op (ι ⋙ Q) W.op V F H
        (op L)) ℤ :=
    Functor.CommShift₂OfLocalization.commShift_liftingIsoApp
      Q.op (ι ⋙ Q) W.op V F H (op L)
  let αL : U.obj (op L) ⋙ Q ⟶ Q ⋙ H.obj (op (Q.obj L)) := α.app (op L)
  have : NatTrans.CommShift (Functor.whiskerLeft ι αL) ℤ := by
    let : (((((whiskeringLeft₂ D).obj Q.op).obj (ι ⋙ Q)).obj H).obj (op L)).CommShift ℤ := by
      change ((ι ⋙ Q) ⋙ H.obj (op (Q.obj L))).CommShift ℤ
      infer_instance
    have : NatTrans.CommShift ((β.app (op L)).inv) ℤ := by assumption
    have : NatTrans.CommShift (β.app (op L)).symm.hom ℤ := by
      change NatTrans.CommShift ((β.app (op L)).inv) ℤ
      assumption
    have : NatTrans.CommShift ((β.app (op L)).hom) ℤ :=
      NatTrans.CommShift.of_iso_inv (β.app (op L)).symm ℤ
    refine ⟨fun n ↦ ?_⟩
    ext I
    have hh := NatTrans.shift_app_comm ((β.app (op L)).hom) n I
    change (commShiftIso (ι ⋙ U.obj (op L) ⋙ Q) n).hom.app I ≫
      ((α.app (op L)).app (ι.obj I))⟦n⟧' =
      (α.app (op L)).app (ι.obj (I⟦n⟧)) ≫
        (commShiftIso ((ι ⋙ Q) ⋙ H.obj (op (Q.obj L))) n).hom.app I at hh
    simpa only [αL, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
      Functor.map_comp, Functor.comp_obj, Functor.comp_map, Category.assoc] using hh
  have : NatTrans.CommShift αL ℤ :=
    NatTrans.CommShift.of_whiskerLeft αL ι (fun F ↦ by
      obtain ⟨I, f, hf⟩ := hres F
      exact ⟨I, f, by dsimp; infer_instance⟩)
  have : NatTrans.CommShift (H.map eM.inv.op) ℤ :=
    Functor.CommShift₂OfLocalization.commShift_map Q.op (ι ⋙ Q) W.op V F H eM.inv.op
  change NatTrans.CommShift (αL ≫ Functor.whiskerLeft Q (H.map eM.inv.op)) ℤ
  infer_instance

private lemma cone_sum_identity {A : Type*} [AddCommGroup A] (a b c x y : A) :
    -a + b + c - (x + y) = -(a - -x) + (b + (c - y)) := by
  abel

private theorem homConeDifferentialAux
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (_hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ {X X' X'' Y Y' Y'' : A}
      (f : X' ⟶ X) (f' : X'' ⟶ X') (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
      Hmap f g ≫ Hmap f' g' = Hmap (f' ≫ f) (g ≫ g'))
    (hadd : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g h : Y ⟶ Y'),
      Hmap f (g + h) = Hmap f g + Hmap f h)
    (hneg : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap f (-g) = -Hmap f g)
    (U : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((U.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((U.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((U.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((U.map f.op).app M) ≫ (U.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (E G I : CochainComplex A ℤ) (f : G ⟶ I) :
    let hf := (U.obj (op E)).map f
    let K := HomologicalComplex.homotopyCofiber hf
    let cf := HomologicalComplex.homotopyCofiber f
    let H := (U.obj (op E)).obj cf
    ∀ (e : ∀ n : ℤ, K.X n ≅ H.X n),
      (∀ n p : ℤ, (e n).hom ≫ π E cf n p (p + n) rfl =
        (show K.X n ⟶ Hobj (E.X p) (cf.X (p + n)) from
        HomologicalComplex.homotopyCofiber.fstX hf n (n + 1) rfl ≫
          π E G (n + 1) p (p + (n + 1)) rfl ≫
          Hmap (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inlX f (p + (n + 1)) (p + n)
              (by change (p + n) + 1 = p + (n + 1); omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf n ≫ π E I n p (p + n) rfl ≫
          Hmap (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inrX f (p + n)))) →
      ∀ n m : ℤ, n + 1 = m →
        (e n).hom ≫ H.d n m = K.d n m ≫ (e m).hom := by
  classical
  intro hf K cf H e he n m hnm
  subst m
  let F := U.obj (op E)
  let proj (T : CochainComplex A ℤ) (k p : ℤ) := π E T k p (p + k) rfl
  have hd (T : CochainComplex A ℤ)
      (k p q p' : ℤ) (hq : p + (k + 1) = q) (hp' : p' + k = q) :
      (F.obj T).d k (k + 1) ≫ π E T (k + 1) p q hq =
        proj T k p ≫ Hmap (𝟙 (E.X p))
          (T.d (p + k) q) -
        k.negOnePow • (π E T k p' q hp' ≫
          Hmap (E.d p p') (𝟙 (T.X q))) := by
    exact hπ₂ E T k (k + 1) p q (p + k) p' rfl hq rfl hp'
  have hm (k p : ℤ) : (hf.f k) ≫ proj I k p =
      proj G k p ≫ Hmap (𝟙 (E.X p)) (f.f (p + k)) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ₃ E E G I (𝟙 E) f k p (p + k) rfl
  have hc (k p q q' : ℤ) (hq : p + k = q) (hq' : p + (k + 1) = q') :
      (e k).hom ≫ π E cf k p q hq =
        HomologicalComplex.homotopyCofiber.fstX hf k (k + 1) rfl ≫
          π E G (k + 1) p q' hq' ≫
          Hmap (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inlX f q' q (by
              change q + 1 = q'; omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf k ≫ π E I k p q hq ≫
          Hmap (𝟙 (E.X p))
            (HomologicalComplex.homotopyCofiber.inrX f q) := by
    subst q q'
    exact he k p
  apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ E cf (n + 1)))
  intro p
  change ((e n).hom ≫ H.d n (n + 1)) ≫ proj cf (n + 1) p =
    (K.d n (n + 1) ≫ (e (n + 1)).hom) ≫ proj cf (n + 1) p
  rw [Category.assoc, hd cf n p (p + (n + 1)) (p + 1) rfl (by omega),
    Preadditive.comp_sub, Linear.comp_units_smul]
  simp only [← Category.assoc]
  dsimp only [proj]
  simp only [hc n p (p + n) (p + (n + 1)) rfl rfl,
    hc n (p + 1) (p + (n + 1)) (p + ((n + 1) + 1)) (by omega) (by omega)]
  simp only [Category.assoc]
  simp only [hc (n + 1) p (p + (n + 1)) (p + ((n + 1) + 1)) rfl rfl,
    Preadditive.comp_add]
  simp only [Preadditive.add_comp, Category.assoc,
    hcomp, Category.comp_id]
  dsimp only [cf, K, HomologicalComplex.homotopyCofiber_d]
  simp only [HomologicalComplex.homotopyCofiber.inlX_d f (p + n)
      (p + (n + 1)) (p + ((n + 1) + 1)) (by change (p + n) + 1 = _; omega)
      (by change (p + (n + 1)) + 1 = _; omega),
    HomologicalComplex.homotopyCofiber.inrX_d,
    HomologicalComplex.homotopyCofiber.d_fstX_assoc hf n (n + 1) ((n + 1) + 1) rfl rfl,
    HomologicalComplex.homotopyCofiber.d_sndX_assoc hf n (n + 1) rfl,
    hadd, hneg, Preadditive.comp_add,
    Preadditive.add_comp, Preadditive.neg_comp, Preadditive.comp_neg]
  dsimp only [proj] at hd hm
  have hg := congrArg (fun t ↦ t ≫ Hmap (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inlX f (p + ((n + 1) + 1))
      (p + (n + 1)) (by change (p + (n + 1)) + 1 = _; omega)))
    (hd G (n + 1) p (p + ((n + 1) + 1)) (p + 1) rfl (by omega))
  have hi := congrArg (fun t ↦ t ≫ Hmap (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inrX f (p + (n + 1))))
    (hd I n p (p + (n + 1)) (p + 1) rfl (by omega))
  have hmf := congrArg (fun t ↦ t ≫ Hmap (𝟙 (E.X p))
    (HomologicalComplex.homotopyCofiber.inrX f (p + (n + 1)))) (hm (n + 1) p)
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    hcomp, Category.id_comp] at hg hi hmf
  dsimp only [F] at hg hi
  simp only [Category.assoc, hg, hi, hmf, Preadditive.comp_sub,
    Linear.comp_units_smul, Preadditive.comp_neg,
    Int.negOnePow_succ, Units.neg_smul, smul_add]
  have hci {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y') :
      Hmap f (g ≫ 𝟙 _) = Hmap f g := congrArg (Hmap f) (Category.comp_id g)
  simp only [hci]
  exact cone_sum_identity
    (A := (HomologicalComplex.homotopyCofiber hf).X n ⟶
      Hobj (E.X p) ((HomologicalComplex.homotopyCofiber f).X (p + (n + 1))))
    _ _ _ _ _

private theorem homConeIsoAux
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ {X X' X'' Y Y' Y'' : A}
      (f : X' ⟶ X) (f' : X'' ⟶ X') (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
      Hmap f g ≫ Hmap f' g' = Hmap (f' ≫ f) (g ≫ g'))
    (hadd : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g h : Y ⟶ Y'),
      Hmap f (g + h) = Hmap f g + Hmap f h)
    (hneg : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap f (-g) = -Hmap f g)
    (hzero : ∀ {X X' Y Y' : A} (f : X' ⟶ X), Hmap f (0 : Y ⟶ Y') = 0)
    (U : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((U.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((U.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((U.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((U.map f.op).app M) ≫ (U.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (E G I : CochainComplex A ℤ) (f : G ⟶ I) :
    ∃ e : CochainComplex.mappingCone ((U.obj (op E)).map f) ≅
      (U.obj (op E)).obj (CochainComplex.mappingCone f),
      ∀ n p : ℤ, e.hom.f n ≫ π E (CochainComplex.mappingCone f) n p (p + n) rfl =
        HomologicalComplex.homotopyCofiber.fstX ((U.obj (op E)).map f) n (n + 1) rfl ≫
          π E G (n + 1) p (p + (n + 1)) rfl ≫
          Hmap (𝟙 (E.X p)) (HomologicalComplex.homotopyCofiber.inlX f
            (p + (n + 1)) (p + n) (by change (p + n) + 1 = p + (n + 1); omega)) +
        HomologicalComplex.homotopyCofiber.sndX ((U.obj (op E)).map f) n ≫
          π E I n p (p + n) rfl ≫
          Hmap (𝟙 (E.X p)) (HomologicalComplex.homotopyCofiber.inrX f (p + n)) := by
  classical
  let HG := (U.obj (op E)).obj G
  let HI := (U.obj (op E)).obj I
  let cf := HomologicalComplex.homotopyCofiber f
  let H := (U.obj (op E)).obj cf
  let hf := (U.obj (op E)).map f
  let K := HomologicalComplex.homotopyCofiber hf
  let pg (n : ℤ) := HomologicalComplex.homotopyCofiber.fstX hf n (n + 1) rfl
  let pi (n : ℤ) := HomologicalComplex.homotopyCofiber.sndX hf n
  let ig (n p : ℤ) := HomologicalComplex.homotopyCofiber.inlX f
    (p + (n + 1)) (p + n) (by change (p + n) + 1 = p + (n + 1); omega)
  let ii (n p : ℤ) := HomologicalComplex.homotopyCofiber.inrX f (p + n)
  let fg (n p : ℤ) := HomologicalComplex.homotopyCofiber.fstX f
    (p + n) (p + (n + 1)) (by change (p + n) + 1 = p + (n + 1); omega)
  let fi (n p : ℤ) := HomologicalComplex.homotopyCofiber.sndX f (p + n)
  let proj (T : CochainComplex A ℤ) (n p : ℤ) := π E T n p (p + n) rfl
  have hp (T : CochainComplex A ℤ) (n : ℤ) :
      IsLimit (Fan.mk (((U.obj (op E)).obj T).X n) (proj T n)) :=
    Classical.choice (hπ₁ E T n)
  let a (n : ℤ) : K.X n ⟶ H.X n := Fan.IsLimit.lift (hp cf n) (fun p ↦
    pg n ≫ proj G (n + 1) p ≫ Hmap (𝟙 (E.X p)) (ig n p) +
    pi n ≫ proj I n p ≫ Hmap (𝟙 (E.X p)) (ii n p))
  have ha (n p : ℤ) : a n ≫ proj cf n p =
      pg n ≫ proj G (n + 1) p ≫ Hmap (𝟙 (E.X p)) (ig n p) +
      pi n ≫ proj I n p ≫ Hmap (𝟙 (E.X p)) (ii n p) :=
    Fan.IsLimit.fac (hp cf n) _ p
  let bg (n : ℤ) : H.X n ⟶ HG.X (n + 1) := Fan.IsLimit.lift (hp G (n + 1))
    (fun p ↦ proj cf n p ≫ Hmap (𝟙 (E.X p)) (fg n p))
  let bi (n : ℤ) : H.X n ⟶ HI.X n := Fan.IsLimit.lift (hp I n)
    (fun p ↦ proj cf n p ≫ Hmap (𝟙 (E.X p)) (fi n p))
  have hbg (n p : ℤ) : bg n ≫ proj G (n + 1) p =
      proj cf n p ≫ Hmap (𝟙 (E.X p)) (fg n p) :=
    Fan.IsLimit.fac (hp G (n + 1)) _ p
  have hbi (n p : ℤ) : bi n ≫ proj I n p =
      proj cf n p ≫ Hmap (𝟙 (E.X p)) (fi n p) :=
    Fan.IsLimit.fac (hp I n) _ p
  let b (n : ℤ) : H.X n ⟶ K.X n :=
    bg n ≫ HomologicalComplex.homotopyCofiber.inlX hf (n + 1) n rfl +
      bi n ≫ HomologicalComplex.homotopyCofiber.inrX hf n
  have hb₁ (n : ℤ) : b n ≫ pg n = bg n := by
    dsimp only [b, pg]
    simp only [Preadditive.add_comp, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_fstX,
      HomologicalComplex.homotopyCofiber.inrX_fstX, comp_zero, add_zero]
    exact Category.comp_id _
  have hb₂ (n : ℤ) : b n ≫ pi n = bi n := by
    dsimp only [b, pi]
    simp only [Preadditive.add_comp, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_sndX,
      HomologicalComplex.homotopyCofiber.inrX_sndX, comp_zero, zero_add]
    exact Category.comp_id _
  have habg (n : ℤ) : a n ≫ bg n = pg n := by
    apply Fan.IsLimit.hom_ext (hp G (n + 1))
    intro p
    change (a n ≫ bg n) ≫ proj G (n + 1) p = pg n ≫ proj G (n + 1) p
    rw [Category.assoc, hbg, ← Category.assoc, ha]
    simp only [Preadditive.add_comp, Category.assoc,
      hcomp, Category.id_comp]
    dsimp [ig, ii, fg]
    simp only [HomologicalComplex.homotopyCofiber.inlX_fstX,
      HomologicalComplex.homotopyCofiber.inrX_fstX,
      hid, hzero,
      Category.comp_id, comp_zero, add_zero]
  have habi (n : ℤ) : a n ≫ bi n = pi n := by
    apply Fan.IsLimit.hom_ext (hp I n)
    intro p
    change (a n ≫ bi n) ≫ proj I n p = pi n ≫ proj I n p
    rw [Category.assoc, hbi, ← Category.assoc, ha]
    simp only [Preadditive.add_comp, Category.assoc,
      hcomp, Category.id_comp]
    dsimp [ig, ii, fi]
    simp only [HomologicalComplex.homotopyCofiber.inlX_sndX,
      HomologicalComplex.homotopyCofiber.inrX_sndX,
      hid, hzero,
      Category.comp_id, comp_zero, zero_add]
  have hab (n : ℤ) : a n ≫ b n = 𝟙 (K.X n) := by
    apply HomologicalComplex.homotopyCofiber.ext_to_X hf n (n + 1) rfl
    · change (a n ≫ b n) ≫ pg n = (𝟙 _) ≫ pg n
      rw [Category.assoc, hb₁, habg, Category.id_comp]
    · change (a n ≫ b n) ≫ pi n = (𝟙 _) ≫ pi n
      rw [Category.assoc, hb₂, habi, Category.id_comp]
  have hba (n : ℤ) : b n ≫ a n = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext (hp cf n)
    intro p
    change (b n ≫ a n) ≫ proj cf n p = (𝟙 _) ≫ proj cf n p
    rw [Category.assoc, ha, Preadditive.comp_add]
    simp only [← Category.assoc, hb₁, hb₂, hbg, hbi]
    simp only [Category.assoc, hcomp,
      Category.id_comp, ← Preadditive.comp_add, ← hadd]
    have hdecomp : fg n p ≫ ig n p + fi n p ≫ ii n p = 𝟙 (cf.X (p + n)) := by
      apply HomologicalComplex.homotopyCofiber.ext_to_X f (p + n)
        (p + (n + 1)) (by change (p + n) + 1 = p + (n + 1); omega)
      · dsimp only [fg, ig, fi, ii]
        simp only [Preadditive.add_comp, Category.assoc,
          HomologicalComplex.homotopyCofiber.inlX_fstX,
          HomologicalComplex.homotopyCofiber.inrX_fstX,
          Category.comp_id, comp_zero, add_zero]
        exact (Category.id_comp _).symm
      · dsimp only [fg, ig, fi, ii]
        simp only [Preadditive.add_comp, Category.assoc,
          HomologicalComplex.homotopyCofiber.inlX_sndX,
          HomologicalComplex.homotopyCofiber.inrX_sndX,
          Category.comp_id, comp_zero, zero_add]
        exact (Category.id_comp _).symm
    rw [hdecomp]
    have hi := hid (E.X p) (cf.X (p + n))
    rw [hi, Category.comp_id]
  let e (n : ℤ) : K.X n ≅ H.X n := ⟨a n, b n, hab n, hba n⟩
  have comm := homConeDifferentialAux Hobj Hmap hid hcomp hadd hneg U π hπ₁ hπ₂ hπ₃ E G I f e
    (fun n p ↦ ha n p)
  exact ⟨HomologicalComplex.Hom.isoOfComponents e comm, ha⟩

private theorem coneBoundary_f
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    {G I : CochainComplex A ℤ} (f : G ⟶ I) (k : ℤ) :
    (CochainComplex.mappingCone.triangle f).mor₃.f k =
      -(HomologicalComplex.homotopyCofiber.fstX f k (k + 1) rfl) := by
  apply CochainComplex.mappingCone.ext_from f (k + 1) k rfl
  · rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f]
    simp only [Preadditive.comp_neg, CochainComplex.mappingCone.inl,
      CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.homotopyCofiber.inlX_fstX,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv]
  · rw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
    simp only [CochainComplex.mappingCone.inr, HomologicalComplex.homotopyCofiber.inr_f,
      Preadditive.comp_neg, HomologicalComplex.homotopyCofiber.inrX_fstX, neg_zero]

private theorem homConeTriangleAux
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ {X X' X'' Y Y' Y'' : A}
      (f : X' ⟶ X) (f' : X'' ⟶ X') (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
      Hmap f g ≫ Hmap f' g' = Hmap (f' ≫ f) (g ≫ g'))
    (hadd : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g h : Y ⟶ Y'),
      Hmap f (g + h) = Hmap f g + Hmap f h)
    (hneg : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap f (-g) = -Hmap f g)
    (hzero : ∀ {X X' Y Y' : A} (f : X' ⟶ X), Hmap f (0 : Y ⟶ Y') = 0)
    (U : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((U.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((U.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((U.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((U.map f.op).app M) ≫ (U.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (E : CochainComplex A ℤ) (S : (U.obj (op E)).CommShift ℤ)
    (hs : ∀ (G : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
      (((S.commShiftIso (1 : ℤ)).inv.app G).f k) ≫
          π E (G⟦(1 : ℤ)⟧) k p q h =
        π E G (k + 1) p (q + 1) (by omega))
    (G I : CochainComplex A ℤ) (f : G ⟶ I) :
    letI := S
    Nonempty (CochainComplex.mappingCone.triangle ((U.obj (op E)).map f) ≅
      (U.obj (op E)).mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  classical
  let := S
  let F := U.obj (op E)
  let hf := F.map f
  obtain ⟨e, he⟩ := homConeIsoAux Hobj Hmap hid hcomp hadd hneg hzero U π hπ₁ hπ₂ hπ₃ E G I f
  have ht {X Y : CochainComplex A ℤ} (g : X ⟶ Y) (n p q : ℤ) (h : p + n = q) :
      (F.map g).f n ≫ π E Y n p q h = π E X n p q h ≫ Hmap (𝟙 _) (g.f q) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ₃ E E X Y (𝟙 E) g n p q h
  have hc (k p q q' : ℤ) (hq : p + k = q) (hq' : p + (k + 1) = q') :
      e.hom.f k ≫ π E (CochainComplex.mappingCone f) k p q hq =
        HomologicalComplex.homotopyCofiber.fstX hf k (k + 1) rfl ≫
          π E G (k + 1) p q' hq' ≫
          Hmap (𝟙 (E.X p)) (HomologicalComplex.homotopyCofiber.inlX f q' q
            (by change q + 1 = q'; omega)) +
        HomologicalComplex.homotopyCofiber.sndX hf k ≫ π E I k p q hq ≫
          Hmap (𝟙 (E.X p)) (HomologicalComplex.homotopyCofiber.inrX f q) := by
    subst q q'
    exact he k p
  refine ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_⟩
  · change hf ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp only [Category.id_comp, Category.comp_id]
    rfl
  · change CochainComplex.mappingCone.inr hf ≫ e.hom =
      𝟙 _ ≫ F.map (CochainComplex.mappingCone.inr f)
    rw [Category.id_comp]
    apply HomologicalComplex.hom_ext
    intro n
    apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ E (CochainComplex.mappingCone f) n))
    intro p
    change (HomologicalComplex.homotopyCofiber.inrX hf n ≫ e.hom.f n) ≫
        π E (CochainComplex.mappingCone f) n p (p + n) rfl =
      (F.map (CochainComplex.mappingCone.inr f)).f n ≫
        π E (CochainComplex.mappingCone f) n p (p + n) rfl
    rw [Category.assoc, ht]
    dsimp only [CochainComplex.mappingCone] at e he ⊢
    rw [he]
    simp only [Preadditive.comp_add]
    dsimp only [hf, CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.inr_f] at *
    erw [HomologicalComplex.homotopyCofiber.inrX_fstX_assoc,
      HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
    simp only [zero_comp, zero_add]
    rfl
  · change (CochainComplex.mappingCone.triangle hf).mor₃ ≫
        (𝟙 (F.obj G))⟦(1 : ℤ)⟧' =
      e.hom ≫ F.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (S.commShiftIso (1 : ℤ)).hom.app G
    have hi : (shiftFunctor (CochainComplex A ℤ) (1 : ℤ)).map
        (𝟙 (F.obj G)) = 𝟙 _ := Functor.map_id _ _
    erw [hi, Category.comp_id]
    apply (cancel_mono ((S.commShiftIso (1 : ℤ)).inv.app G)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro k
    apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ E (G⟦(1 : ℤ)⟧) k))
    intro p
    change ((CochainComplex.mappingCone.triangle hf).mor₃.f k ≫
        ((S.commShiftIso (1 : ℤ)).inv.app G).f k) ≫
          π E (G⟦(1 : ℤ)⟧) k p (p + k) rfl =
      (e.hom.f k ≫ (F.map (CochainComplex.mappingCone.triangle f).mor₃).f k) ≫
        π E (G⟦(1 : ℤ)⟧) k p (p + k) rfl
    rw [Category.assoc, hs, Category.assoc]
    have htδ := ht (CochainComplex.mappingCone.triangle f).mor₃ k p (p + k) rfl
    erw [htδ]
    rw [← Category.assoc]
    erw [hc k p (p + k) (p + k + 1) rfl (by omega)]
    simp only [Preadditive.add_comp, Category.assoc, hcomp,
      coneBoundary_f, Preadditive.comp_neg, hneg,
      HomologicalComplex.homotopyCofiber.inlX_fstX,
      HomologicalComplex.homotopyCofiber.inrX_fstX,
      hid, hzero, Category.comp_id, comp_zero, add_zero]
    exact Preadditive.neg_comp _ _

private noncomputable def triangleComparisonAux
    {K B : Type*} [Category K] [Category B] [HasShift K ℤ] [HasShift B ℤ]
    (F G : K ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (T : Pretriangulated.Triangle K)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₂)] [IsIso (τ.app T.obj₃)] :
    F.mapTriangle.obj T ≅ G.mapTriangle.obj T := by
  refine Pretriangulated.Triangle.isoMk _ _
    (asIso (τ.app T.obj₁)) (asIso (τ.app T.obj₂)) (asIso (τ.app T.obj₃))
    (τ.naturality T.mor₁) (τ.naturality T.mor₂) ?_
  change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
      (τ.app T.obj₁)⟦(1 : ℤ)⟧' =
    τ.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
  rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, τ.naturality, Category.assoc]

private theorem triangleTransferAux
    {A B E : Type*} [Category A] [Abelian A] [Category B]
    [HasShift B ℤ] [HasZeroObject B] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated B] [IsTriangulated B]
    [Category E]
    (Q : CochainComplex A ℤ ⥤ B) [Q.CommShift ℤ]
    (ι : E ⥤ CochainComplex A ℤ) [(ι ⋙ Q).Full] [(ι ⋙ Q).EssSurj]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ) [F.CommShift ℤ]
    (G : B ⥤ B) [G.CommShift ℤ]
    (τ : F ⋙ Q ⟶ Q ⋙ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ I : E, IsIso (τ.app (ι.obj I)))
    (hcone : ∀ {I J : E} (f : I ⟶ J),
      IsIso (τ.app (CochainComplex.mappingCone (ι.map f))))
    (hQ : ∀ {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ∈ distTriang B)
    (hF : ∀ {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Nonempty (CochainComplex.mappingCone.triangle (F.map f) ≅
        F.mapTriangle.obj (CochainComplex.mappingCone.triangle f))) : G.IsTriangulated := by
  classical
  constructor
  intro T hT
  let V := ι ⋙ Q
  let I := V.objPreimage T.obj₁
  let J := V.objPreimage T.obj₂
  let e₁ := V.objObjPreimageIso T.obj₁
  let e₂ := V.objObjPreimageIso T.obj₂
  let f : I ⟶ J := V.preimage (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  have hf : Q.map (ι.map f) ≫ e₂.hom = e₁.hom ≫ T.mor₁ := by
    change V.map f ≫ e₂.hom = _
    simp only [f, V.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let C := CochainComplex.mappingCone.triangle (ι.map f)
  let eT : Q.mapTriangle.obj C ≅ T :=
    Pretriangulated.isoTriangleOfIso₁₂ _ _ (hQ (ι.map f)) hT e₁ e₂ hf
  let := hτ I
  let := hτ J
  let := hcone f
  have : IsIso (τ.app C.obj₁) := hτ I
  have : IsIso (τ.app C.obj₂) := hτ J
  have : IsIso (τ.app C.obj₃) := hcone f
  let eτ := triangleComparisonAux (F ⋙ Q) (Q ⋙ G) τ C
  obtain ⟨ec⟩ := hF (ι.map f)
  let e : Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (F.map (ι.map f))) ≅
      G.mapTriangle.obj T :=
    Q.mapTriangle.mapIso ec ≪≫ (Functor.mapTriangleCompIso F Q).symm.app C ≪≫
      eτ ≪≫ (Functor.mapTriangleCompIso Q G).app C ≪≫ G.mapTriangle.mapIso eT
  exact Pretriangulated.isomorphic_distinguished _ (hQ (F.map (ι.map f))) _ e.symm

private theorem exactOfDescentAux
    {A B E : Type*} [Category A] [Abelian A] [Category B]
    [HasShift B ℤ] [HasZeroObject B] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    [Category E]
    (Q : CochainComplex A ℤ ⥤ B) [Q.CommShift ℤ] [Q.EssSurj]
    (ι : E ⥤ CochainComplex A ℤ) [(ι ⋙ Q).Full] [(ι ⋙ Q).EssSurj]
    (U : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    [∀ L, (U.obj L).CommShift ℤ]
    (H : Bᵒᵖ ⥤ B ⥤ B)
    (S : ∀ M : B, (H.obj (op M)).CommShift ℤ)
    (α : U ⋙ (Functor.whiskeringRight _ _ _).obj Q ⟶
      Q.op ⋙ H ⋙ (Functor.whiskeringLeft _ _ _).obj Q)
    (hS : ∀ (M : B) (L : CochainComplex A ℤ) (eM : Q.obj L ≅ M),
      letI := S M
      NatTrans.CommShift
        (show U.obj (op L) ⋙ Q ⟶ Q ⋙ H.obj (op M) from
          α.app (op L) ≫ Functor.whiskerLeft Q (H.map eM.inv.op)) ℤ)
    (hα : ∀ (L : (CochainComplex A ℤ)ᵒᵖ) (F : E), IsIso ((α.app L).app (ι.obj F)))
    (hαcone : ∀ (L : (CochainComplex A ℤ)ᵒᵖ) {I J : E} (f : I ⟶ J),
      IsIso ((α.app L).app (CochainComplex.mappingCone (ι.map f))))
    (hQ : ∀ {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ∈ distTriang B)
    (hCone : ∀ (L : CochainComplex A ℤ) {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Nonempty (CochainComplex.mappingCone.triangle ((U.obj (op L)).map f) ≅
        (U.obj (op L)).mapTriangle.obj (CochainComplex.mappingCone.triangle f))) :
    ∀ M : B, letI := S M; (H.obj (op M)).IsTriangulated := by
  classical
  intro M
  let := S M
  let L := Q.objPreimage M
  let eM : Q.obj L ≅ M := Q.objObjPreimageIso M
  let τ : U.obj (op L) ⋙ Q ⟶ Q ⋙ H.obj (op M) :=
    α.app (op L) ≫ Functor.whiskerLeft Q (H.map eM.inv.op)
  have : NatTrans.CommShift τ ℤ := hS M L eM
  have (F : E) : IsIso (τ.app (ι.obj F)) := by
    change IsIso ((α.app (op L)).app (ι.obj F) ≫ (H.map eM.inv.op).app _)
    let := hα (op L) F
    infer_instance
  have {F F' : E} (f : F ⟶ F') :
      IsIso (τ.app (CochainComplex.mappingCone (ι.map f))) := by
    change IsIso ((α.app (op L)).app _ ≫ (H.map eM.inv.op).app _)
    let := hαcone (op L) f
    infer_instance
  exact triangleTransferAux Q ι (U.obj (op L)) (H.obj (op M)) τ
    (fun F ↦ inferInstance) (fun _ ↦ inferInstance) hQ (hCone L)

private theorem normalizedTargetShiftDescentAux
    {A B E : Type*} [Category A] [Abelian A] [Category B]
    [HasShift B ℤ] [HasZeroObject B] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    [Category E] [HasShift E ℤ]
    (Q : CochainComplex A ℤ ⥤ B) (W : MorphismProperty (CochainComplex A ℤ))
    [Q.CommShift ℤ] [Q.EssSurj] [Q.IsLocalization W] [W.ContainsIdentities]
    (ι : E ⥤ CochainComplex A ℤ) [ι.CommShift ℤ]
    (V : MorphismProperty E) [(ι ⋙ Q).IsLocalization V] [V.ContainsIdentities]
    [(ι ⋙ Q).Full] [(ι ⋙ Q).EssSurj]
    (U : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    [∀ L, (U.obj L).CommShift ℤ]
    [∀ {L L'} (f : L ⟶ L'), NatTrans.CommShift (U.map f) ℤ]
    (H : Bᵒᵖ × B ⥤ B)
    (α : Functor.uncurry.obj U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H)
    (hα : ∀ (L : (CochainComplex A ℤ)ᵒᵖ) (F : E),
      IsIso (α.app (L, ι.obj F)))
    (hαcone : ∀ (L : (CochainComplex A ℤ)ᵒᵖ) {I J : E} (f : I ⟶ J),
      IsIso (α.app (L, CochainComplex.mappingCone (ι.map f))))
    (hres : ∀ F : CochainComplex A ℤ, ∃ (I : E) (f : F ⟶ ι.obj I), IsIso (Q.map f))
    (hQ : ∀ {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ∈ distTriang B)
    (hCone : ∀ (L : CochainComplex A ℤ) {I J : CochainComplex A ℤ} (f : I ⟶ J),
      Nonempty (CochainComplex.mappingCone.triangle ((U.obj (op L)).map f) ≅
        (U.obj (op L)).mapTriangle.obj (CochainComplex.mappingCone.triangle f))) :
    ∃ S : ∀ M : B, ((Functor.curry.obj H).obj (op M)).CommShift ℤ,
      (∀ (M : B) (L F : CochainComplex A ℤ) (eM : Q.obj L ≅ M) (s : ℤ),
        Q.map (((U.obj (op L)).commShiftIso s).inv.app F) ≫ α.app (op L, F⟦s⟧) ≫
            H.map (Prod.mkHom eM.inv.op ((Q.commShiftIso s).hom.app F)) ≫
            ((S M).commShiftIso s).hom.app (Q.obj F) =
          (Q.commShiftIso s).hom.app ((U.obj (op L)).obj F) ≫
            (α.app (op L, F) ≫ H.map (Prod.mkHom eM.inv.op (𝟙 _)))⟦s⟧') ∧
      ∀ M : B, letI := S M; ((Functor.curry.obj H).obj (op M)).IsTriangulated := by
  classical
  let G := Functor.curry.obj H
  let α' : U ⋙ (Functor.whiskeringRight _ _ _).obj Q ⟶
      Q.op ⋙ G ⋙ (Functor.whiskeringLeft _ _ _).obj Q :=
    (Functor.isoWhiskerRight (Functor.currying.unitIso.app U)
      ((Functor.whiskeringRight _ _ _).obj Q)).hom ≫
      Functor.curry.map α ≫ (Functor.curryObjProdComp Q.op Q H).hom
  have hα' (L : (CochainComplex A ℤ)ᵒᵖ) (F : CochainComplex A ℤ) :
      (α'.app L).app F = α.app (L, F) := by
    change Q.map (𝟙 _) ≫ α.app (L, F) ≫ 𝟙 _ = _
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  obtain ⟨S, hS⟩ := targetShiftDescent Q W ι V U G α'
    (fun L F ↦ by rw [hα']; exact hα L F) hres
  refine ⟨S, ?_, ?_⟩
  · intro M L F eM s
    let := S M
    have := hS M L eM
    let : ((U ⋙ (Functor.whiskeringRight _ _ _).obj Q).obj (op L)).CommShift ℤ :=
      inferInstanceAs ((U.obj (op L) ⋙ Q).CommShift ℤ)
    have hh := NatTrans.shift_app_comm
      (α'.app (op L) ≫ Functor.whiskerLeft Q (G.map eM.inv.op)) s F
    simp only [Functor.whiskeringRight_obj_obj, Functor.commShiftIso_comp_hom_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, hα', Category.assoc] at hh
    change Q.map (((U.obj (op L)).commShiftIso s).hom.app F) ≫
        (Q.commShiftIso s).hom.app ((U.obj (op L)).obj F) ≫
          (α.app (op L, F) ≫ H.map (Prod.mkHom eM.inv.op (𝟙 _)))⟦s⟧' =
      α.app (op L, F⟦s⟧) ≫ H.map (Prod.mkHom eM.inv.op (𝟙 _)) ≫
        (G.obj (op M)).map ((Q.commShiftIso s).hom.app F) ≫
        ((S M).commShiftIso s).hom.app (Q.obj F) at hh
    apply (cancel_epi (Q.map (((U.obj (op L)).commShiftIso s).hom.app F))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
    simpa only [G, Functor.curry_obj_obj_map, Category.assoc,
      ← Functor.map_comp_assoc, prod_comp, Category.id_comp, Category.comp_id] using hh.symm
  · exact exactOfDescentAux Q ι U G S α' hS
      (fun L F ↦ by rw [hα']; exact hα L F)
      (fun L _ _ f ↦ by rw [hα']; exact hαcone L f) hQ hCone

private theorem natTrans_ext_on_essSurj
    {E B D : Type*} [Category E] [Category B] [Category D]
    (Q : E ⥤ B) [Q.EssSurj] {F G : B ⥤ D} (α β : F ⟶ G)
    (h : ∀ X : E, α.app (Q.obj X) = β.app (Q.obj X)) : α = β := by
  classical
  apply NatTrans.ext
  funext Y
  let e : Q.obj (Q.objPreimage Y) ≅ Y := Q.objObjPreimageIso Y
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, h]

private def RightNormalizationAux
    {K B : Type*} [Category K] [Category B] [HasShift K ℤ] [HasShift B ℤ]
    (Q : K ⥤ B) [Q.CommShift ℤ] (U : Kᵒᵖ ⥤ K ⥤ K) (H : Bᵒᵖ × B ⥤ B)
    (α : Functor.uncurry.obj U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H)
    (P : ∀ (L F : K) (s : ℤ), (((U.obj (op L)).obj F)⟦s⟧ ≅
      (U.obj (op L)).obj (F⟦s⟧)) → Prop)
    (S : ∀ M : B, ((Functor.curry.obj H).obj (op M)).CommShift ℤ) : Prop :=
  ∀ (M : B) (L F : K) (eM : Q.obj L ≅ M) (s : ℤ),
    ∃ e : ((U.obj (op L)).obj F)⟦s⟧ ≅ (U.obj (op L)).obj (F⟦s⟧),
      P L F s e ∧ Q.map e.hom ≫ α.app (op L, F⟦s⟧) ≫
        H.map (Prod.mkHom eM.inv.op ((Q.commShiftIso s).hom.app F)) ≫
        ((S M).commShiftIso s).hom.app (Q.obj F) =
      (Q.commShiftIso s).hom.app ((U.obj (op L)).obj F) ≫
        (α.app (op L, F) ≫ H.map (Prod.mkHom eM.inv.op (𝟙 _)))⟦s⟧'

private theorem rightNormalization_uniqueAux
    {K B E : Type*} [Category K] [Category B] [Category E]
    [HasShift K ℤ] [HasShift B ℤ]
    (Q : K ⥤ B) [Q.CommShift ℤ] [Q.EssSurj]
    (ι : E ⥤ K) [(ι ⋙ Q).EssSurj]
    (U : Kᵒᵖ ⥤ K ⥤ K) (H : Bᵒᵖ × B ⥤ B)
    (α : Functor.uncurry.obj U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H)
    (P : ∀ (L F : K) (s : ℤ), (((U.obj (op L)).obj F)⟦s⟧ ≅
      (U.obj (op L)).obj (F⟦s⟧)) → Prop)
    (hP : ∀ (L F : K) (s : ℤ) (e e' : ((U.obj (op L)).obj F)⟦s⟧ ≅
      (U.obj (op L)).obj (F⟦s⟧)), P L F s e → P L F s e' → e = e')
    (hα : ∀ (L : K) (F : E) (s : ℤ), IsIso (α.app (op L, (ι.obj F)⟦s⟧)))
    (S T : ∀ M : B, ((Functor.curry.obj H).obj (op M)).CommShift ℤ)
    (hS : RightNormalizationAux Q U H α P S)
    (hT : RightNormalizationAux Q U H α P T) : S = T := by
  classical
  funext M
  let L := Q.objPreimage M
  let eM : Q.obj L ≅ M := Q.objObjPreimageIso M
  have key (s : ℤ) : (S M).commShiftIso s = (T M).commShiftIso s := by
    apply Iso.ext
    apply natTrans_ext_on_essSurj (ι ⋙ Q)
    intro F
    obtain ⟨e, he, hSe⟩ := hS M L (ι.obj F) eM s
    obtain ⟨e', he', hTe⟩ := hT M L (ι.obj F) eM s
    have hee' := hP L (ι.obj F) s e e' he he'
    subst e'
    let := hα L F s
    have : IsIso (H.map
        (Prod.mkHom eM.inv.op ((Q.commShiftIso s).hom.app (ι.obj F)))) := by
      change IsIso ((H.mapIso (eM.symm.op.prod ((Q.commShiftIso s).app (ι.obj F)))).hom)
      infer_instance
    exact (cancel_epi (Q.map e.hom ≫ α.app (op L, (ι.obj F)⟦s⟧) ≫ H.map
      (Prod.mkHom eM.inv.op ((Q.commShiftIso s).hom.app (ι.obj F))))).mp
      (by simpa only [Category.assoc, Functor.comp_obj] using hSe.trans hTe.symm)
  cases hSM : S M
  cases hTM : T M
  congr 1
  funext s
  have hh := key s
  rw [hSM, hTM] at hh
  exact hh

private theorem isKInjective_coneAux
    {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex A ℤ} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    (CochainComplex.mappingCone f).IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f) ?_ ?_
  · change (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)
    exact (CochainComplex.isKInjective_iff_rightOrthogonal K).mp inferInstance
  · change (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal
      ((HomotopyCategory.quotient A (.up ℤ)).obj L)
    exact (CochainComplex.isKInjective_iff_rightOrthogonal L).mp inferInstance

private theorem isKInjective_cone_mapAux
    {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex.KInjectives A} (f : K ⟶ L) :
    (CochainComplex.mappingCone (CochainComplex.KInjectives.ι.map f)).IsKInjective := by
  have : K.obj.IsKInjective := K.property
  have : L.obj.IsKInjective := L.property
  exact isKInjective_coneAux f.hom

set_option backward.isDefEq.respectTransparency true in
private theorem hasKInjectiveResolutions :
    Abelian.HasKInjectiveResolutions (Modules.{c, v, r} J R) := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  exact ⟨fun K ↦
    ⟨(WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj K,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ K,
      (ringedSiteHomAugmentation.{c, v, r} J R).app K,
      CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ K⟩⟩

set_option backward.isDefEq.respectTransparency true in
private theorem kInjectiveQ_full
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] :
    (CochainComplex.KInjectives.ι (C := A) ⋙ DerivedCategory.Q).Full :=
  letI : (CochainComplex.KInjectives.toHomotopyCategory (C := A) ⋙
      HomotopyCategory.KInjectives.Qh).Full := inferInstance
  Functor.Full.of_iso (F := CochainComplex.KInjectives.toHomotopyCategory (C := A) ⋙
      HomotopyCategory.KInjectives.Qh) (Functor.isoWhiskerLeft CochainComplex.KInjectives.ι
    (DerivedCategory.quotientCompQhIso A))

set_option backward.isDefEq.respectTransparency true in
private theorem kInjectiveQ_essSurj
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] :
    (CochainComplex.KInjectives.ι (C := A) ⋙ DerivedCategory.Q).EssSurj :=
  letI : (CochainComplex.KInjectives.toHomotopyCategory (C := A) ⋙
      HomotopyCategory.KInjectives.Qh).EssSurj := inferInstance
  Functor.essSurj_of_iso (F := CochainComplex.KInjectives.toHomotopyCategory (C := A) ⋙
      HomotopyCategory.KInjectives.Qh) (Functor.isoWhiskerLeft CochainComplex.KInjectives.ι
    (DerivedCategory.quotientCompQhIso A))

private theorem ordinaryRightShiftsAux
    {A : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hcomp : ∀ {X X' X'' Y Y' Y'' : A}
      (f : X' ⟶ X) (f' : X'' ⟶ X') (g : Y ⟶ Y') (g' : Y' ⟶ Y''),
      Hmap f g ≫ Hmap f' g' = Hmap (f' ≫ f) (g ≫ g'))
    (hsmul : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y') (a : ℤˣ),
      Hmap f (a • g) = a • Hmap f g)
    (hadd : ∀ {X X' Y Y' : A} (f : X' ⟶ X) (g h : Y ⟶ Y'),
      Hmap f (g + h) = Hmap f g + Hmap f h)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
 :
    ∃ S : ∀ L : CochainComplex A ℤ, (F.obj (op L)).CommShift ℤ,
      (∀ {L L' : CochainComplex A ℤ} (f : L' ⟶ L),
        letI := S L
        letI := S L'
        NatTrans.CommShift (F.map f.op) ℤ) ∧
      (∀ (L M : CochainComplex A ℤ) (n k p q : ℤ) (h : p + k = q),
        (((S L).commShiftIso n).inv.app M).f k ≫ π L (M⟦n⟧) k p q h =
          π L M (k + n) p (q + n) (by omega)) ∧
      ∀ (L G I : CochainComplex A ℤ) (f : G ⟶ I),
        letI := S L
        Nonempty (CochainComplex.mappingCone.triangle ((F.obj (op L)).map f) ≅
          (F.obj (op L)).mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  classical
  have hneg {X X' Y Y' : A} (f : X' ⟶ X) (g : Y ⟶ Y') :
      Hmap f (-g) = -Hmap f g := by
    simpa only [Units.neg_smul, one_smul] using hsmul f g (-1)
  have hzero {X X' Y Y' : A} (f : X' ⟶ X) : Hmap f (0 : Y ⟶ Y') = 0 := by
    apply add_eq_left.mp
    simpa only [add_zero] using (hadd f (0 : Y ⟶ Y') 0).symm
  choose e he using ordinaryRightShiftAux Hobj Hmap hid
    (fun X _ _ _ g h ↦ by rw [hcomp, Category.id_comp]) hsmul F π hπ₁ hπ₂ hπ₃
  obtain ⟨S, hS, hform⟩ := ordinaryRightCoherenceAux Hobj Hmap hid F π hπ₁ hπ₃ e he
  refine ⟨S, hS, hform, ?_⟩
  intro L G I f
  exact homConeTriangleAux Hobj Hmap hid hcomp hadd hneg hzero F π hπ₁ hπ₂ hπ₃
    L (S L) (fun G k p q h ↦ hform L G 1 k p q h) G I f

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_units_smul_right
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') (a : ℤˣ) :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (a • g) =
      a • SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    apply SheafOfModules.hom_ext.{max c v r, v, c, max c v r}
    ext X φ : 3
    change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj X.unop).map (-g.val) =
      -((PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj X.unop).map g.val)
    ext W x
    rfl

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_add_right
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (f : A' ⟶ A) (g h : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (g + h) =
      SheafOfModules.homObjMap f g + SheafOfModules.homObjMap f h := by
  apply SheafOfModules.hom_ext.{max c v r, v, c, max c v r}
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map (g.val + h.val) =
    (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj X.unop).map g.val +
      (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj X.unop).map h.val
  ext W x
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryRightShift :
    ∃ S : ∀ L : Complex.{c, v, r} J R,
      ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op L)).CommShift ℤ,
      (∀ {L L' : Complex.{c, v, r} J R} (f : L' ⟶ L),
        letI := S L
        letI := S L'
        NatTrans.CommShift
          ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op) ℤ) ∧
      (∀ (L F : Complex.{c, v, r} J R) (s : ℤ),
        RightFormula.{c, v, r} J R L F s (((S L).commShiftIso s).symm.app F)) ∧
      ∀ (L G I : Complex.{c, v, r} J R) (f : G ⟶ I),
        letI := S L
        Nonempty (CochainComplex.mappingCone.triangle
          (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op L)).map f) ≅
          ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op L)).mapTriangle.obj
            (CochainComplex.mappingCone.triangle f)) := by
  exact ordinaryRightShiftsAux
    (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R))
    (fun {_X _X' _Y _Y'} f g ↦
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f g)
    (fun X Y ↦ SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r}
      (R := R) (M := X) (N := Y))
    (fun {_X _X' _X'' _Y _Y' _Y''} f f' g g' ↦
      SheafOfModules.homObjMap_comp_homObjMap.{max c v r, v, c, max c v r} f f' g g')
    (fun {_X _X' _Y _Y'} f g a ↦ homObjMap_units_smul_right.{c, v, r} f g a)
    (fun {_X _X' _Y _Y'} f g h ↦ homObjMap_add_right.{c, v, r} f g h)
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
    (homComplexπ.{c, v, max c v r, max c v r} (R := R))
    (fun L F k ↦ ⟨homComplexIsLimit.{c, v, max c v r, max c v r} L F k⟩)
    (homComplex_d_π.{c, v, max c v r, max c v r} (R := R))
    (fun _ _ _ _ f g ↦ homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f g)

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryLeftShift (s : ℤ) :
    ∃ iso : ordinaryBifunctor.{c, v, r} J R ⋙ shiftFunctor _ (-s) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) s).op.prod (𝟭 _)) ⋙
        ordinaryBifunctor.{c, v, r} J R,
      ∀ (L F : Complex.{c, v, r} J R),
        LeftFormula.{c, v, r} J R L F s (iso.app (op L, F)) := by
  exact ordinaryLeftShiftBifunctorAux
    (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R))
    (fun {_X _X' _Y _Y'} f g ↦
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f g)
    (fun X Y ↦ SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r}
      (R := R) (M := X) (N := Y))
    (fun {_X _X' _Y _Y'} a f g ↦ homObjMap_units_smul_left.{c, v, r} (R := R) a f g)
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
    (homComplexπ.{c, v, max c v r, max c v r} (R := R))
    (fun L F k ↦ ⟨homComplexIsLimit.{c, v, max c v r, max c v r} L F k⟩)
    (homComplex_d_π.{c, v, max c v r, max c v r} (R := R))
    (fun _ _ _ _ f g ↦ homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f g) s

set_option backward.isDefEq.respectTransparency true in
private theorem sourceShiftDescent
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [W.ContainsIdentities] [Q.IsLocalization W]
    (U : Aᵒᵖ × A ⥤ A) (I : A ⥤ A) (η : 𝟭 A ⟶ I)
    (H : Bᵒᵖ × B ⥤ B)
    (fac : (Q.op.prod Q) ⋙ H ≅ (𝟭 _).prod I ⋙ U ⋙ Q)
    (s : ℤ)
    (e : U ⋙ shiftFunctor A (-s) ≅
      ((shiftFunctor A s).op.prod (𝟭 A)) ⋙ U) :
    let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
      Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Aᵒᵖ)) η) (U ⋙ Q) ≫ fac.inv
    ∃ t : H ⋙ shiftFunctor B (-s) ≅
      ((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H,
      ∀ (L M : A),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, M)) ≫
            (α.app (op L, M))⟦-s⟧' ≫ t.hom.app (op (Q.obj L), Q.obj M) =
          Q.map ((e.app (op L, M)).hom) ≫ α.app (op (L⟦s⟧), M) ≫
            H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _)) := by
  classical
  intro α
  let P := Q.op.prod Q
  let V := W.op.prod W
  let S := (shiftFunctor A s).op.prod (𝟭 A)
  let q : S ⋙ P ≅ P ⋙ ((shiftFunctor B s).op.prod (𝟭 B)) :=
    NatIso.prod (NatIso.op (Q.commShiftIso s).symm) (Iso.refl Q)
  let f : P ⋙ (H ⋙ shiftFunctor B (-s)) ≅
      P ⋙ (((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H) :=
    Functor.isoWhiskerRight fac (shiftFunctor B (-s)) ≪≫
      Functor.isoWhiskerLeft ((𝟭 _).prod I ⋙ U) (Q.commShiftIso (-s)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 _).prod I) e) Q ≪≫
      (Functor.isoWhiskerLeft S fac).symm ≪≫ Functor.isoWhiskerRight q H
  let ff := Localization.fullyFaithfulWhiskeringLeft P V B
  let t := ff.preimageIso f
  refine ⟨t, ?_⟩
  intro L M
  have ht : t.hom.app (P.obj (op L, M)) = f.hom.app (op L, M) :=
    NatTrans.congr_app (ff.map_preimage f.hom) (op L, M)
  dsimp only [P, Functor.prod_obj, Functor.op_obj] at ht
  rw [ht]
  dsimp only [f, α, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  dsimp only [Functor.comp_map, Functor.comp_obj, NatTrans.prod, NatTrans.id_app,
    Functor.id_obj, Functor.prod_obj, Functor.whiskerLeft_app]
  rw [← Functor.commShiftIso_hom_naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  have hn := e.hom.naturality (Prod.mkHom (𝟙 (op L)) (η.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
    Functor.prod_map, Functor.op_map, Functor.id_map, Functor.map_id,
    Functor.op_obj, Functor.id_obj] at hn
  rw [hn]
  simp only [unop_id, Functor.map_id, op_id, Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem normalizedSourceShiftDescent
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [W.ContainsIdentities] [Q.IsLocalization W]
    (U : Aᵒᵖ × A ⥤ A) (I : A ⥤ A) (η : 𝟭 A ⟶ I)
    (H : Bᵒᵖ × B ⥤ B)
    (fac : (Q.op.prod Q) ⋙ H ≅ (𝟭 _).prod I ⋙ U ⋙ Q)
    (s : ℤ)
    (e : U ⋙ shiftFunctor A (-s) ≅
      ((shiftFunctor A s).op.prod (𝟭 A)) ⋙ U) :
    let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
      Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Aᵒᵖ)) η) (U ⋙ Q) ≫ fac.inv
    ∃ S : ∀ P : B,
      (Functor.curry.obj H).obj (op P) ⋙ shiftFunctor B (-s) ≅
        (Functor.curry.obj H).obj (op (P⟦s⟧)),
      ∀ (P : B) (L F : A) (eP : Q.obj L ≅ P),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, F)) ≫
            (α.app (op L, F) ≫ H.map (Prod.mkHom eP.inv.op (𝟙 _)))⟦-s⟧' ≫
              (S P).hom.app (Q.obj F) =
          Q.map ((e.app (op L, F)).hom) ≫ α.app (op (L⟦s⟧), F) ≫
            H.map (Prod.mkHom (((shiftFunctor B s).map eP.inv) ≫
              (Q.commShiftIso s).inv.app L).op (𝟙 _)) := by
  intro α
  obtain ⟨t, ht⟩ := sourceShiftDescent Q W U I η H fac s e
  let S (P : B) : (Functor.curry.obj H).obj (op P) ⋙ shiftFunctor B (-s) ≅
      (Functor.curry.obj H).obj (op (P⟦s⟧)) :=
    NatIso.ofComponents (fun N ↦ t.app (op P, N)) (by
      intro N N' f
      simpa only [Functor.comp_map, Functor.curry_obj_obj_map, Iso.app_hom,
        Functor.prod_map, Functor.op_map, unop_id, Functor.map_id, op_id,
        Functor.id_map] using t.hom.naturality (Prod.mkHom (𝟙 (op P)) f))
  refine ⟨S, ?_⟩
  intro P L F eP
  have hn := t.hom.naturality (Prod.mkHom eP.inv.op (𝟙 (Q.obj F)))
  change (H.map (Prod.mkHom eP.inv.op (𝟙 (Q.obj F))))⟦-s⟧' ≫
      t.hom.app (op P, Q.obj F) =
    t.hom.app (op (Q.obj L), Q.obj F) ≫
      H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) at hn
  change _ ≫ _ ≫ t.hom.app (op P, Q.obj F) = _
  calc
    _ = ((Q.commShiftIso (-s)).hom.app (U.obj (op L, F)) ≫
        (α.app (op L, F))⟦-s⟧' ≫ t.hom.app (op (Q.obj L), Q.obj F)) ≫
          H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hn]
    _ = (Q.map ((e.app (op L, F)).hom) ≫ α.app (op (L⟦s⟧), F) ≫
        H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _))) ≫
          H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) := by
      rw [ht L F]
    _ = _ := by
      simp only [Category.assoc, ← H.map_comp, prod_comp,
        Category.id_comp, ← op_comp]

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

set_option backward.isDefEq.respectTransparency true

private theorem resolutionComparison_naturality
    (p q : (Complex.{c, v, r} J R)ᵒᵖ × Complex.{c, v, r} J R) (f : p ⟶ q) :
    ((DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R).map f ≫
        (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R q.1.unop q.2).hom =
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R p.1.unop p.2).hom ≫
        ((𝟭 _).prod (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
          ordinaryBifunctor.{c, v, r} J R ⋙ DerivedCategory.Q).map f := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let e := Localization.fac _
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun F ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ F).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ F⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)
  exact e.hom.naturality f

private def resolutionComparison :
    (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J R ≅
    (𝟭 _).prod (WeilConjectures.coefficientHomResolution.{r, c, v} J R) ⋙
      ordinaryBifunctor.{c, v, r} J R ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun p ↦ WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R p.1.unop p.2)
    (fun {p q} f ↦ resolutionComparison_naturality.{c, v, r, w} J R p q f)

private def ordinaryComparison :
    ordinaryBifunctor.{c, v, r} J R ⋙ DerivedCategory.Q ⟶
      (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, w} J R :=
  Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _))
    (ringedSiteHomAugmentation.{c, v, r} J R))
    (ordinaryBifunctor.{c, v, r} J R ⋙ DerivedCategory.Q) ≫
      (resolutionComparison.{c, v, r, w} J R).inv

private theorem ordinaryComparison_app (L F : Complex.{c, v, r} J R) :
    (ordinaryComparison.{c, v, r, w} J R).app (op L, F) =
      ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F := rfl

private theorem comparison_isIso_of_kInjective
    (L F : Complex.{c, v, r} J R) [F.IsKInjective] :
    IsIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F) := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  have hI : ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ F
  have hη : QuasiIso ((ringedSiteHomAugmentation.{c, v, r} J R).app F) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ F).2
  exact ringedSiteOrdinaryHomComparison_isIso.{c, v, r, w} J R L F
    (quasiIso_homComplex_mapOfUniverses.{c, v, r}
      (show F ⟶ (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F
        from (ringedSiteHomAugmentation.{c, v, r} J R).app F) (𝟙 L))

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
private theorem leftFormula_unique (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e e' : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅
      complexHom.{c, v, r} J R (L⟦s⟧) F)
    (he : LeftFormula.{c, v, r} J R L F s e)
    (he' : LeftFormula.{c, v, r} J R L F s e') : e = e' := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro k
  apply homComplex_hom_ext
  intro p q hpq
  exact (he k p q hpq).trans (he' k p q hpq).symm

/-- The right shift structure agrees, through the fixed ordinary-to-derived
comparison, with unsigned target reindexing. This pins the shift signs, rather
than choosing an arbitrary shift structure.
Source: Stacks 08JA, 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def RightNormalization
    (S : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ) : Prop :=
  ∀ (M : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eM : DerivedCategory.Q.obj L ≅ M) (s : ℤ),
    letI := S M
    ∃ e : (complexHom.{c, v, r} J R L F)⟦s⟧ ≅ complexHom.{c, v, r} J R L (F⟦s⟧),
      RightFormula.{c, v, r} J R L F s e ∧
      DerivedCategory.Q.map e.hom ≫
          ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L (F⟦s⟧) ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom eM.inv.op ((DerivedCategory.Q.commShiftIso s).hom.app F)) ≫
          ((hom.{c, v, r, w} J R M).commShiftIso s).hom.app
            (DerivedCategory.Q.obj F) =
        (DerivedCategory.Q.commShiftIso s).hom.app (complexHom.{c, v, r} J R L F) ≫
          (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom eM.inv.op (𝟙 _)))⟦s⟧'

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
private theorem rightFormula_unique (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e e' : (complexHom.{c, v, r} J R L F)⟦s⟧ ≅
      complexHom.{c, v, r} J R L (F⟦s⟧))
    (he : RightFormula.{c, v, r} J R L F s e)
    (he' : RightFormula.{c, v, r} J R L F s e') : e = e' := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro k
  apply homComplex_hom_ext
  intro p q hpq
  exact (he k p q hpq).trans (he' k p q hpq).symm

set_option backward.isDefEq.respectTransparency true in
private theorem rightNormalization_iff_aux
    (S : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ) :
    RightNormalization.{c, v, r, w} J R S ↔
      RightNormalizationAux (DerivedCategory.Q (C := Modules.{c, v, r} J R))
        (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
        (derivedInternalHomOfUniverses.{c, v, r, w} J R)
        (ordinaryComparison.{c, v, r, w} J R)
        (fun L F s e ↦ RightFormula.{c, v, r} J R L F s e) S := by
  simp only [RightNormalization, RightNormalizationAux, ordinaryComparison_app,
    hom, complexHom, homComplex, Functor.comp_obj]

set_option backward.isDefEq.respectTransparency true in
private theorem rightNormalization_unique
    (S T : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ)
    (hS : RightNormalization.{c, v, r, w} J R S)
    (hT : RightNormalization.{c, v, r, w} J R T) : S = T := by
  let A := Modules.{c, v, r} J R
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let ι : CochainComplex.KInjectives A ⥤ Complex.{c, v, r} J R :=
    CochainComplex.KInjectives.ι
  let : Abelian.HasKInjectiveResolutions A := hasKInjectiveResolutions.{c, v, r} J R
  let : (ι ⋙ Q).EssSurj := kInjectiveQ_essSurj
  let U := homComplexFunctor.{c, v, max c v r, max c v r} (R := R)
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let α := ordinaryComparison.{c, v, r, w} J R
  let P := fun L F s e ↦ RightFormula.{c, v, r} J R L F s e
  apply rightNormalization_uniqueAux Q ι U H α P
    (fun L F s e e' ↦ rightFormula_unique.{c, v, r} J R L F s e e')
    (fun L F s ↦ by
      have : F.obj.IsKInjective := F.property
      change IsIso ((ordinaryComparison.{c, v, r, w} J R).app (op L, F.obj⟦s⟧))
      rw [ordinaryComparison_app]
      exact comparison_isIso_of_kInjective.{c, v, r, w} J R L (F.obj⟦s⟧)) S T
  · exact (rightNormalization_iff_aux.{c, v, r, w} J R S).mp hS
  · exact (rightNormalization_iff_aux.{c, v, r, w} J R T).mp hT

set_option backward.isDefEq.respectTransparency true in
private theorem rightNormalizedShift_exists :
    ∃ S : ∀ M : D.{c, v, r, w} J R,
      (hom.{c, v, r, w} J R M).CommShift ℤ,
      RightNormalization.{c, v, r, w} J R S ∧
      ∀ M : D.{c, v, r, w} J R,
        letI := S M
        (hom.{c, v, r, w} J R M).IsTriangulated := by
  classical
  let A := Modules.{c, v, r} J R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let η := ringedSiteHomAugmentation.{c, v, r} J R
  let U := homComplexFunctor.{c, v, max c v r, max c v r} (R := R)
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let α := ordinaryComparison.{c, v, r, w} J R
  let P : ObjectProperty (Complex.{c, v, r} J R) := fun K ↦ K.IsKInjective
  let : P.IsStableUnderShift ℤ := {
    isStableUnderShiftBy := fun n ↦ ⟨fun K hK ↦ by
      have : K.IsKInjective := hK
      change (K⟦n⟧).IsKInjective
      infer_instance⟩ }
  let ι : CochainComplex.KInjectives A ⥤ Complex.{c, v, r} J R :=
    CochainComplex.KInjectives.ι
  let : HasShift (CochainComplex.KInjectives A) ℤ :=
    ObjectProperty.hasShift (A := ℤ) P
  let : ι.CommShift ℤ := ObjectProperty.commShiftι (A := ℤ) P
  let : Abelian.HasKInjectiveResolutions A := hasKInjectiveResolutions.{c, v, r} J R
  obtain ⟨S₀, hS₀, hform, hCone⟩ := ordinaryRightShift.{c, v, r} J R
  let (L : (Complex.{c, v, r} J R)ᵒᵖ) : (U.obj L).CommShift ℤ := S₀ L.unop
  let {L L' : (Complex.{c, v, r} J R)ᵒᵖ} (f : L ⟶ L') :
      NatTrans.CommShift (U.map f) ℤ := hS₀ f.unop
  let : (CochainComplex.KInjectives.quasiIso A).ContainsIdentities := ⟨fun X ↦ by
    change QuasiIso (𝟙 X.obj)
    infer_instance⟩
  have hαE (L : (Complex.{c, v, r} J R)ᵒᵖ) (F : CochainComplex.KInjectives A) :
      IsIso (α.app (L, ι.obj F)) := by
    have : F.obj.IsKInjective := F.property
    change IsIso ((ordinaryComparison.{c, v, r, w} J R).app (op L.unop, F.obj))
    rw [ordinaryComparison_app]
    exact comparison_isIso_of_kInjective.{c, v, r, w} J R L.unop F.obj
  have hαcone (L : (Complex.{c, v, r} J R)ᵒᵖ)
      {F F' : CochainComplex.KInjectives A} (f : F ⟶ F') :
      IsIso (α.app (L, CochainComplex.mappingCone (ι.map f))) := by
    have := isKInjective_cone_mapAux f
    change IsIso ((ordinaryComparison.{c, v, r, w} J R).app (op L.unop, _))
    rw [ordinaryComparison_app]
    exact comparison_isIso_of_kInjective.{c, v, r, w} J R L.unop _
  let : (ι ⋙ Q).Full := kInjectiveQ_full
  let : (ι ⋙ Q).EssSurj := kInjectiveQ_essSurj
  obtain ⟨S, hS, hT⟩ := normalizedTargetShiftDescentAux Q
    (HomologicalComplex.quasiIso A (.up ℤ)) ι (CochainComplex.KInjectives.quasiIso A)
    U H α hαE hαcone
    (fun F ↦ by
      have : (I.obj F).IsKInjective :=
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ F
      refine ⟨CochainComplex.KInjectives.mk (I.obj F), η.app F, ?_⟩
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ F).2)
    (fun f ↦ DerivedCategory.mappingCone_triangle_distinguished f)
    (fun L _ _ f ↦ hCone L _ _ f)
  refine ⟨S, (rightNormalization_iff_aux.{c, v, r, w} J R S).mpr ?_, hT⟩
  intro M L F eM s
  refine ⟨((S₀ L).commShiftIso s).symm.app F, hform L F s, ?_⟩
  exact hS M L F eM s

/-- Existence and uniqueness of the ordinary normalized right shift structure.
Source: Stacks 08JA, 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: product projections define the unsigned reindexing chain isomorphism.
The shifted Hom differential and Hom into the shifted target agree. Its naturality
commutes with the fixed K-injective augmentation. Localize this identity; on
K-injective targets the augmentation comparison is invertible. Essential
surjectivity and the localization universal property give a unique natural shift
structure on every derived object. The degreewise reindexings compose and are the
identity at zero, so they satisfy the CommShift coherence identities. -/
theorem rightShift_existsUnique :
    ∃! S : ∀ M : D.{c, v, r, w} J R, (hom.{c, v, r, w} J R M).CommShift ℤ,
      RightNormalization.{c, v, r, w} J R S := by
  obtain ⟨S, hS, hT⟩ := rightNormalizedShift_exists.{c, v, r, w} J R
  exact ⟨S, hS, fun T hT ↦ rightNormalization_unique.{c, v, r, w} J R T S hT hS⟩

/-- The uniquely normalized shift of the recorded Hom functor.
Source: Stacks 08JC (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
instance homCommShift (M : D.{c, v, r, w} J R) : (hom.{c, v, r, w} J R M).CommShift ℤ :=
  (rightShift_existsUnique.{c, v, r, w} J R).exists.choose M

/-- Normalization of the signed source-shift family against the fixed
ordinary-to-derived Hom comparison.
Source: Stacks 0A8X, 08JA
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def LeftNormalization
    (S : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧)) : Prop :=
  ∀ (M : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eM : DerivedCategory.Q.obj L ≅ M) (s : ℤ),
    ∃ e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F,
      LeftFormula.{c, v, r} J R L F s e ∧
      (DerivedCategory.Q.commShiftIso (-s)).hom.app (complexHom.{c, v, r} J R L F) ≫
          (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom eM.inv.op (𝟙 _)))⟦-s⟧' ≫
          (S M s).hom.app (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map e.hom ≫
          ringedSiteOrdinaryHomComparison.{c, v, r, w} J R (L⟦s⟧) F ≫
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (((shiftFunctor _ s).map eM.inv) ≫
              (DerivedCategory.Q.commShiftIso s).inv.app L).op (𝟙 _))

private theorem leftNormalizedShift_exists :
    ∃ S : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅
        hom.{c, v, r, w} J R (M⟦s⟧),
      LeftNormalization.{c, v, r, w} J R S := by
  classical
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := ordinaryBifunctor.{c, v, r} J R
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  choose e he using ordinaryLeftShift.{c, v, r} J R
  have hd (s : ℤ) := normalizedSourceShiftDescent Q
    (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ))
    U I (ringedSiteHomAugmentation.{c, v, r} J R) H
    (resolutionComparison.{c, v, r, w} J R) s (e s)
  choose S hS using hd
  refine ⟨fun M s ↦ S s M, ?_⟩
  intro M L F eM s
  refine ⟨(e s).app (op L, F), he s L F, ?_⟩
  exact hS s M L F eM

private theorem leftNormalization_unique
    (S T : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅
        hom.{c, v, r, w} J R (M⟦s⟧))
    (hS : LeftNormalization.{c, v, r, w} J R S)
    (hT : LeftNormalization.{c, v, r, w} J R T) : S = T := by
  classical
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  funext M s
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let L := Q.objPreimage M
  let eM : Q.obj L ≅ M := Q.objObjPreimageIso M
  have h (F : Complex.{c, v, r} J R) [F.IsKInjective] :
      (S M s).hom.app (Q.obj F) = (T M s).hom.app (Q.obj F) := by
    obtain ⟨e, he, hSe⟩ := hS M L F eM s
    obtain ⟨e', he', hTe⟩ := hT M L F eM s
    have hee' := leftFormula_unique.{c, v, r} J R L F s e e' he he'
    subst e'
    have hc := comparison_isIso_of_kInjective.{c, v, r, w} J R L F
    have hm : IsIso ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom eM.inv.op (𝟙 (Q.obj F)))) := by
      change IsIso (((derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso
        (eM.symm.op.prod (Iso.refl (Q.obj F)))).hom)
      infer_instance
    have hp : IsIso ((ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom eM.inv.op (𝟙 _)))⟦-s⟧') := by infer_instance
    have hh := hSe.trans hTe.symm
    have hh' := (cancel_epi ((DerivedCategory.Q.commShiftIso (-s)).hom.app
      (complexHom.{c, v, r} J R L F))).mp hh
    exact (cancel_epi ((ringedSiteOrdinaryHomComparison.{c, v, r, w} J R L F ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom eM.inv.op (𝟙 _)))⟦-s⟧')).mp hh'
  let ι : CochainComplex.KInjectives (Modules.{c, v, r} J R) ⥤
      Complex.{c, v, r} J R := CochainComplex.KInjectives.ι
  let : Abelian.HasKInjectiveResolutions (Modules.{c, v, r} J R) :=
    hasKInjectiveResolutions.{c, v, r} J R
  let : (ι ⋙ Q).EssSurj := kInjectiveQ_essSurj
  apply Iso.ext
  apply natTrans_ext_on_essSurj (ι ⋙ Q)
  intro F
  have : F.obj.IsKInjective := F.property
  exact h F.obj

/-- The uniquely specified signed source shift.
Source: Stacks 0A8X, 08JA
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: in degree k reindex p to p+s and multiply by (-1)^(s*k).
The ratio between consecutive degrees is (-1)^s, exactly compensating for
the shifted source differential. The inverse reindexes backwards with the same
sign. Projectionwise equality gives naturality and uniqueness. Localize the
chain isomorphism through the fixed K-injective augmentation; K-injective targets
and essential surjectivity determine the unique derived natural isomorphism. -/
theorem leftShift_existsUnique :
    ∃! S : ∀ (M : D.{c, v, r, w} J R) (s : ℤ),
      hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧),
      LeftNormalization.{c, v, r, w} J R S := by
  obtain ⟨S, hS⟩ := leftNormalizedShift_exists.{c, v, r, w} J R
  exact ⟨S, hS, fun T hT ↦ leftNormalization_unique.{c, v, r, w} J R T S hT hS⟩

/-- The signed source shift selected by its full representative normalization.
Source: Stacks 08JA (blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction). -/
def sourceShift (M : D.{c, v, r, w} J R) (s : ℤ) :
    hom.{c, v, r, w} J R M ⋙ shiftFunctor _ (-s) ≅ hom.{c, v, r, w} J R (M⟦s⟧) :=
  (leftShift_existsUnique.{c, v, r, w} J R).exists.choose M s

/-- Exactness for the normalized target shift at independent site universes.
Source: Stacks 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).
Proof: represent a target triangle by a cone of a map of K-injective complexes.
The cone is K-injective, since Hom from an acyclic test complex takes it to a
cone of acyclic complexes. Hom(L,Cone(f)) is the cone of Hom(L,f), with its
inclusion, projection and connecting arrow. The right-shift normalization above
fixes the connecting-arrow sign. Localize and use the ordinary representative
comparison. Independence of K-injective representatives and TR3 transfer the
result to every distinguished triangle. No boundedness assumption is used. -/
theorem hom_isTriangulated (M : D.{c, v, r, w} J R) : (hom.{c, v, r, w} J R M).IsTriangulated := by
  obtain ⟨S, hS, hT⟩ := rightNormalizedShift_exists.{c, v, r, w} J R
  have hEq : S = (rightShift_existsUnique.{c, v, r, w} J R).exists.choose :=
    rightNormalization_unique.{c, v, r, w} J R S _ hS
      (rightShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
  rw [hEq] at hT
  exact hT M

end CategoryTheory.RingedHomUniverses
