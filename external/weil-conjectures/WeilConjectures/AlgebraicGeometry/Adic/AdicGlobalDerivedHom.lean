/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor

/-! # Global derived Hom with completed adic coefficients

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12;
Stacks Project, Tag 08JA (blueprint: def-weil-pbc-adic-global-derived-hom).

## Main definitions

* `adicGlobalSections`: evaluation at the final object, with the canonical A action.
* `adicGlobalDerivedHom`: derived global sections of the recorded internal derived Hom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The constant residue section of the finite coefficient sheaf. Source: Bhatt--Scholze,
6.8.2(1) (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicFiniteConstant (n : ℕ) (U : T.ProEtᵒᵖ) :
    A →+* ((pbcAdicRings T d).obj (op n)).obj.obj U :=
  letI := d.quotientFinite n
  ((toSheafify (ProEt.topology T)
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app U).hom.comp
    (((AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1))).app U).hom.comp
      (Ideal.Quotient.mk (d.ideal ^ (n + 1))))

private theorem adicFiniteConstant_compat (U : T.ProEtᵒᵖ) (n : ℕ) :
    CommRingCat.ofHom (adicFiniteConstant T d (n + 1) U) ≫
        ((pbcAdicRings T d).map (homOfLE (n.le_add_right 1)).op).hom.app U =
      CommRingCat.ofHom (adicFiniteConstant T d n U) := by
  let : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite
  let φ := Ideal.Quotient.factorPowSucc d.ideal (n + 1)
  have h := congr_app (toSheafify_naturality (ProEt.topology T)
    (AdicCoefficients.functionPresheafMap T φ)) U
  dsimp only [pbcAdicRings, AdicCoefficients.ringSystem]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  change CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1))) ≫
      (AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1 + 1))).app U ≫
      (toSheafify (ProEt.topology T) _).app U ≫
      (sheafifyMap (ProEt.topology T) (AdicCoefficients.functionPresheafMap T φ)).app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ≫
      (AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1))).app U ≫
      (toSheafify (ProEt.topology T) _).app U
  rw [← NatTrans.comp_app, ← h, NatTrans.comp_app]
  ext a
  rfl

/-- The canonical scalar homomorphism is uniquely specified by all its finite residues.
Source: Bhatt--Scholze, 6.8.2(1)
(blueprint: def-weil-pbc-adic-global-derived-hom).
Proof: the constant residue homomorphisms commute with each quotient map, since
both routes send a to its constant residue class. They form a cone on the evaluated
inverse system. Limits of ring sheaves are evaluated sectionwise, so the limit
universal property supplies the homomorphism. The projections are jointly injective,
which proves uniqueness. This argument includes the empty scheme and zero rings. -/
theorem adicScalar_exists (U : T.ProEtᵒᵖ) :
    ∃! ρ : A →+* (pbcAdicCompletion T d).obj.obj U,
      ∀ n : ℕ, ((pbcAdicProjection T d n).hom.app U).hom.comp ρ =
        adicFiniteConstant T d n U := by
  let E := sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
    (CategoryTheory.evaluation T.ProEtᵒᵖ CommRingCat.{u + 1}).obj U
  let c : Cone (pbcAdicRings T d ⋙ E) :=
    { pt := CommRingCat.of A
      π := NatTrans.ofOpSequence
        (fun n ↦ CommRingCat.ofHom (adicFiniteConstant T d n U)) (by
          intro n
          change 𝟙 _ ≫ CommRingCat.ofHom (adicFiniteConstant T d n U) = _
          rw [Category.id_comp]
          exact (adicFiniteConstant_compat T d U n).symm) }
  let hc := isLimitOfPreserves E (limit.isLimit (pbcAdicRings T d))
  refine ⟨(hc.lift c).hom, ?_, ?_⟩
  · intro n
    exact congrArg CommRingCat.Hom.hom (hc.fac c (op n))
  · intro ρ hρ
    have h : CommRingCat.ofHom ρ = hc.lift c := by
      apply hc.hom_ext
      intro n
      exact (congrArg CommRingCat.ofHom (hρ n.unop)).trans (hc.fac c n).symm
    exact congrArg CommRingCat.Hom.hom h

/-- The scalar map into completed sections, determined by its actual finite residues.
Source: Bhatt--Scholze, 6.8.2(1)
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicScalar (U : T.ProEtᵒᵖ) : A →+* (pbcAdicCompletion T d).obj.obj U :=
  (adicScalar_exists T d U).exists.choose

/-- Global sections as A-modules: evaluation at the final pro-etale object followed
by restriction along the constant completed scalar map. Source: Stacks Project,
Tag 08JA (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalSections : pbcModules T (pbcAdicCompletion T d) ⥤ ModuleCat.{u + 1} A :=
  SheafOfModules.evaluation _ (op (⊤_ T.ProEt)) ⋙
    ModuleCat.restrictScalars (adicScalar T d (op (⊤_ T.ProEt)))

/-- Evaluation and scalar restriction are additive. Source: Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
instance adicGlobalSections_additive : (adicGlobalSections T d).Additive := by
  dsimp [adicGlobalSections, SheafOfModules.evaluation]
  infer_instance

/-- The unbounded right derived functor of global sections, with its A-module action.
Source: Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicDerivedGlobalSections :
    DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology T) (pbcAdicCompletion T d)).1
  (adicGlobalSections T d).rightDerivedFunctor

/-- Global derived Hom is RΓ of internal derived Hom, in the derived category of
A-modules, without replacing the completed coefficient sheaf by a constant sheaf.
Source: Bhatt--Scholze, Lemma 6.8.12; Stacks Project, Tag 08JA
(blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalDerivedHom :
    (DerivedCategory (pbcModules T (pbcAdicCompletion T d)))ᵒᵖ ×
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
        DerivedCategory (ModuleCat.{u + 1} A) :=
  derivedInternalHomOfUniverses.{u + 1, u, u + 1} (ProEt.topology T) (pbcAdicCompletion T d) ⋙
    adicDerivedGlobalSections T d

/-- Fix the contravariant argument of global derived Hom. Source: Bhatt--Scholze,
Lemma 6.8.12 (blueprint: def-weil-pbc-adic-global-derived-hom). -/
def adicGlobalRHom (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :
    DerivedCategory (pbcModules T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (ModuleCat.{u + 1} A) :=
  (Functor.curry.obj (adicGlobalDerivedHom T d)).obj (op K)

end AlgebraicGeometry.Scheme
