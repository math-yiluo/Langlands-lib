/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # A lower bound for pro-etale derived internal Hom

## References

* Bhatt--Scholze, Lemma 6.3.14, boundedness argument
* Stacks Project, Tag 08JA
* Bhatt--Scholze, Lemma 6.3.14
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.Scheme

private theorem homObj_zero_left (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (hL : IsZero L) :
    IsZero (SheafOfModules.homObj (R := R) L M) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := L) (N := M),
    hL.eq_of_src (𝟙 L) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 M.val) = 0
  ext W x
  change ((φ.app W).hom) 0 = 0
  exact map_zero _

private theorem homObj_zero_right (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (L M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (hM : IsZero M) :
    IsZero (SheafOfModules.homObj (R := R) L M) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := R) (M := L) (N := M),
    hM.eq_of_tgt (𝟙 M) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

/-- Internal Hom from an object bounded above by b to one bounded below by N is
bounded below by N-b. The coefficient ring sheaf is arbitrary. -/
theorem proEtale_internalHom_isGE (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    [HasDerivedCategory (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (K M : DerivedCategory (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (b N : ℤ) [K.IsLE b] [M.IsGE N] :
    ((derivedInternalHomOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology T) R).obj (op K, M)).IsGE (N - b) := by
  let C := SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : IsGrothendieckAbelian.{u + 1} C :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
        (ProEt.topology T) R).1
  obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K b
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE M N
  obtain ⟨I, f, hf, hI, hIN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective P N
  have : QuasiIso f := hf
  have : I.IsStrictlyGE N := hIN
  have : ∀ n, Injective (I.X n) := hI
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  obtain ⟨e⟩ := derivedInternalHomOfUniverses_obj_iso.{u + 1, u, u + 1}
    (ProEt.topology T) R K M L I eL.symm
      ((asIso (DerivedCategory.Q.map f)).symm ≪≫ eP.symm)
  have : (homComplex (R := R) L I).IsStrictlyGE (N - b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    apply (homComplexIsLimit (R := R) L I n).isZero_pt
    apply Functor.isZero
    intro p
    by_cases hp : b < p.as
    · exact homObj_zero_left T R _ _ (L.isZero_of_isStrictlyLE b p.as hp)
    · exact homObj_zero_right T R _ _ (I.isZero_of_isStrictlyGE N (p.as + n) (by omega))
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (N - b)

end AlgebraicGeometry.Scheme
