/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryCore
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
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
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of normalized coefficient pullback squares

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03CZ and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits

section Mates

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [Category X₀] [Category X₁] [Category X₂]
  [Category Y₀] [Category Y₁] [Category Y₂]
  {Lh : X₁ ⥤ X₀} {Lk : X₂ ⥤ X₁} {Lc : X₂ ⥤ X₀}
  {Rh : X₀ ⥤ X₁} {Rk : X₁ ⥤ X₂} {Rc : X₀ ⥤ X₂}
  {lh : Y₁ ⥤ Y₀} {lk : Y₂ ⥤ Y₁} {lc : Y₂ ⥤ Y₀}
  {rh : Y₀ ⥤ Y₁} {rk : Y₁ ⥤ Y₂} {rc : Y₀ ⥤ Y₂}
  (ah : Lh ⊣ Rh) (ak : Lk ⊣ Rk) (ac : Lc ⊣ Rc)
  (bh : lh ⊣ rh) (bk : lk ⊣ rk) (bc : lc ⊣ rc)
  (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁) (F₂ : X₂ ⥤ Y₂)
  (a : Lk ⋙ Lh ≅ Lc) (b : lk ⋙ lh ≅ lc)
  (d : Rh ⋙ Rk ≅ Rc) (e : rh ⋙ rk ≅ rc)
  (ch : Lh ⋙ F₀ ≅ F₁ ⋙ lh) (ck : Lk ⋙ F₁ ≅ F₂ ⋙ lk)
  (cc : Lc ⋙ F₀ ≅ F₂ ⋙ lc)
  (sh : Rh ⋙ F₁ ≅ F₀ ⋙ rh) (sk : Rk ⋙ F₂ ≅ F₁ ⋙ rk)
  (sc : Rc ⋙ F₂ ≅ F₀ ⋙ rc)

private theorem mate_composition
    (ha : ∀ P Q (f : Lc.obj P ⟶ Q),
      ak.homEquiv _ _ (ah.homEquiv _ _ (a.hom.app P ≫ f)) =
        ac.homEquiv _ _ f ≫ d.inv.app Q)
    (hb : ∀ P Q (f : lc.obj P ⟶ Q),
      bk.homEquiv _ _ (bh.homEquiv _ _ (b.hom.app P ≫ f)) =
        bc.homEquiv _ _ f ≫ e.inv.app Q)
    (hh : ∀ P, bh.homEquiv _ _ (ch.inv.app P) =
      F₁.map (ah.unit.app P) ≫ sh.hom.app (Lh.obj P))
    (hk : ∀ P, bk.homEquiv _ _ (ck.inv.app P) =
      F₂.map (ak.unit.app P) ≫ sk.hom.app (Lk.obj P))
    (hc : ∀ P, bc.homEquiv _ _ (cc.inv.app P) =
      F₂.map (ac.unit.app P) ≫ sc.hom.app (Lc.obj P))
    (hs : ∀ Q, F₂.map (d.hom.app Q) ≫ sc.hom.app Q =
      sk.hom.app (Rh.obj Q) ≫ rk.map (sh.hom.app Q) ≫ e.hom.app (F₀.obj Q))
    (P : X₂) :
    F₀.map (a.hom.app P) ≫ cc.hom.app P =
      ch.hom.app (Lk.obj P) ≫ lh.map (ck.hom.app P) ≫ b.hom.app (F₂.obj P) := by
  dsimp only [Functor.comp_obj] at hh hk hc
  have hi : b.hom.app (F₂.obj P) ≫ cc.inv.app P =
      lh.map (ck.inv.app P) ≫ ch.inv.app (Lk.obj P) ≫ F₀.map (a.hom.app P) := by
    apply (bh.homEquiv _ _).injective
    apply (bk.homEquiv _ _).injective
    rw [hb]
    dsimp only [Functor.comp_obj]
    rw [hc]
    rw [bh.homEquiv_naturality_left, bh.homEquiv_naturality_right]
    rw [hh, bk.homEquiv_naturality_right, hk]
    simp only [Functor.map_comp, Category.assoc]
    have hη := sk.hom.naturality (ah.unit.app (Lk.obj P))
    have hα := sh.hom.naturality (a.hom.app P)
    have hβ := sk.hom.naturality (Rh.map (a.hom.app P))
    dsimp only [Functor.comp_map, Functor.comp_obj] at hη hα hβ
    rw [← reassoc_of% hη, ← rk.map_comp, ← hα]
    simp only [Functor.map_comp]
    rw [← reassoc_of% hβ]
    simp only [← Functor.map_comp_assoc]
    have hu := ha P (Lc.obj P) (𝟙 _)
    simp only [Adjunction.homEquiv_apply, Category.comp_id, CategoryTheory.Functor.map_id,
      Functor.map_comp, Category.assoc] at hu
    erw [Category.id_comp] at hu
    rw [hu]
    simp only [Functor.map_comp, Category.assoc]
    apply congrArg (F₂.map (ac.unit.app P) ≫ ·)
    apply (cancel_mono (e.hom.app (F₀.obj (Lc.obj P)))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hs]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono (cc.inv.app P)).mp
  apply (cancel_epi (ch.inv.app (Lk.obj P))).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [hi, ← lh.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [lh.map_id]
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

end Mates

section Localization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategoryFactors

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [Category X₀] [Category X₁] [Category X₂]
  [Category Y₀] [Category Y₁] [Category Y₂]
  [Abelian X₀] [Abelian X₁] [Abelian X₂]
  [Abelian Y₀] [Abelian Y₁] [Abelian Y₂]
  [HasDerivedCategory X₀] [HasDerivedCategory X₁] [HasDerivedCategory X₂]
  [HasDerivedCategory Y₀] [HasDerivedCategory Y₁] [HasDerivedCategory Y₂]

private theorem square_fac {R : X₀ ⥤ X₁} {S : Y₀ ⥤ Y₁}
    {F : X₀ ⥤ Y₀} {G : X₁ ⥤ Y₁}
    [R.Additive] [S.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : R ⋙ G ≅ F ⋙ S) (P : CochainComplex X₀ ℤ) :
    (Functor.mapDerivedCategorySquareIso a).hom.app (DerivedCategory.Q.obj P) ≫
        S.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R G).inv.app
    (DerivedCategory.Q.obj P))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

variable (Rh : X₀ ⥤ X₁) (Rk : X₁ ⥤ X₂) (Rc : X₀ ⥤ X₂)
  (rh : Y₀ ⥤ Y₁) (rk : Y₁ ⥤ Y₂) (rc : Y₀ ⥤ Y₂)
  (F₀ : X₀ ⥤ Y₀) (F₁ : X₁ ⥤ Y₁) (F₂ : X₂ ⥤ Y₂)
  [Rh.Additive] [Rk.Additive] [Rc.Additive]
  [rh.Additive] [rk.Additive] [rc.Additive]
  [F₀.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits Rh] [PreservesFiniteColimits Rh]
  [PreservesFiniteLimits Rk] [PreservesFiniteColimits Rk]
  [PreservesFiniteLimits Rc] [PreservesFiniteColimits Rc]
  [PreservesFiniteLimits rh] [PreservesFiniteColimits rh]
  [PreservesFiniteLimits rk] [PreservesFiniteColimits rk]
  [PreservesFiniteLimits rc] [PreservesFiniteColimits rc]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

end Localization

namespace WeilConjectures.SemilinearSections

attribute [local irreducible] hasDerived HasDerivedCategory.standard
  Functor.mapDerivedCategory systemRing ringPresheaf rings
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

private abbrev ordinaryComposition {s m n : ℕ} (h : n ≤ m) (k : m ≤ s) :=
  (restrictionComposition_existsUnique.{c, v, max c v r} J B τ h k).exists.choose

end WeilConjectures.SemilinearSections
