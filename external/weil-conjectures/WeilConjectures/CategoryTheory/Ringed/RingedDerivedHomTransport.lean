/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
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
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Prod
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
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

/-! # Natural transport of derived internal Hom

Source: Stacks Project, Tags 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-derived-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c d vc vd r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

-- The unbounded derived comparisons require elaborating several functor structures.
/-- An exact additive module equivalence with a natural Hom-complex comparison
transports the actual derived internal Hom bifunctors naturally.
Source: Stacks Project, Tags 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-derived-hom-transport).

Proof: precompose with the product of the two derived localization functors.
Compute derived Hom using the canonical functorial K-injective replacements.
Transport the source replacement through the equivalence and use the given
natural cochain comparison. An additive equivalence preserves K-injectives.
The transported replacement and the target replacement compare naturally through
the target replacement of the transported replacement. Both comparison maps are
quasi-isomorphisms between K-injectives, so Hom followed by localization inverts
them. This gives a natural isomorphism before localization. The product
localization has fully faithful precomposition, so the isomorphism descends. -/
theorem derivedHom_transport
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{max c d vc vd r})
    (S : Sheaf K CommRingCat.{max c d vc vd r})
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc} R)]
    [HasDerivedCategory.{w'} (NativeModules.{max c d vc vd r, d, vd} S)]
    (E : NativeModules.{max c d vc vd r, c, vc} R ≌
      NativeModules.{max c d vc vd r, d, vd} S) [E.functor.Additive]
    (γ : Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ complexMap E.functor ≅
      ((complexMap E.functor).op.prod (complexMap E.functor)) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := S))) :
    Nonempty (derivedInternalHomOfUniverses.{c, vc, max d vd r, w} J R ⋙
      E.functor.mapDerivedCategory ≅
      (E.functor.mapDerivedCategory.op.prod E.functor.mapDerivedCategory) ⋙
        derivedInternalHomOfUniverses.{d, vd, max c vc r, w'} K S) := by
  let A := NativeModules.{max c d vc vd r, c, vc} R
  let B := NativeModules.{max c d vc vd r, d, vd} S
  let : IsGrothendieckAbelian.{max c d vc vd r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      c, vc, max d vd r} J R).1
  let : IsGrothendieckAbelian.{max c d vc vd r} B :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
      d, vd, max c vc r} K S).1
  let T := complexMap E.functor
  let IR := CochainComplex.kInjectiveResolutionFunctor.{max c d vc vd r} A
  let IS := CochainComplex.kInjectiveResolutionFunctor.{max c d vc vd r} B
  let ηR := CochainComplex.toKInjectiveResolution.{max c d vc vd r} A
  let ηS := CochainComplex.toKInjectiveResolution.{max c d vc vd r} B
  let H : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ DerivedCategory B :=
    Functor.uncurry.obj (homComplexFunctor (R := S)) ⋙ DerivedCategory.Q.{w'}
  let α : T.op.prod (IR ⋙ T) ⋙ H ⟶ T.op.prod (IR ⋙ T ⋙ IS) ⋙ H :=
    Functor.whiskerRight (NatTrans.prod (𝟙 T.op)
      (Functor.whiskerLeft (IR ⋙ T) ηS)) H
  let β : T.op.prod (T ⋙ IS) ⋙ H ⟶ T.op.prod (IR ⋙ T ⋙ IS) ⋙ H :=
    Functor.whiskerRight (NatTrans.prod (𝟙 T.op)
      (Functor.whiskerRight (Functor.whiskerRight ηR T) IS)) H
  have hIR (M : CochainComplex A ℤ) : (IR.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj A M
  have hIS (M : CochainComplex B ℤ) : (IS.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj B M
  have hηR (M : CochainComplex A ℤ) : QuasiIso (ηR.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A M).2
  have hηS (M : CochainComplex B ℤ) : QuasiIso (ηS.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app B M).2
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have := hIR X.2
    have : CochainComplex.IsKInjective (T.obj (IR.obj X.2)) :=
      inferInstanceAs (CochainComplex.IsKInjective
        ((E.functor.mapHomologicalComplex (.up ℤ)).obj (IR.obj X.2)))
    have := hIS (T.obj (IR.obj X.2))
    have := hηS (T.obj (IR.obj X.2))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{d, vd, max c vc r}
      (I' := T.obj (IR.obj X.2)) (I := IS.obj (T.obj (IR.obj X.2)))
      (L' := T.obj X.1.unop) (L := T.obj X.1.unop) (ηS.app _) (𝟙 _)
  have : IsIso β := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have := hηR X.2
    have := hηS (T.obj X.2)
    have := hηS (T.obj (IR.obj X.2))
    have := hIS (T.obj X.2)
    have := hIS (T.obj (IR.obj X.2))
    have : QuasiIso (IS.map (T.map (ηR.app X.2))) := by
      apply (quasiIso_iff_comp_left (ηS.app (T.obj X.2)) _).mp
      have hn := ηS.naturality (T.map (ηR.app X.2))
      dsimp at hn
      rw [← hn]
      infer_instance
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{d, vd, max c vc r}
      (IS.map (T.map (ηR.app X.2))) (𝟙 _)
  obtain ⟨eR⟩ := derivedInternalHomOfUniverses_comparison.{c, vc, max d vd r, w}
    J R IR ηR (fun M ↦ ⟨hηR M, hIR M⟩)
  obtain ⟨eS⟩ := derivedInternalHomOfUniverses_comparison.{d, vd, max c vc r, w'}
    K S IS ηS (fun M ↦ ⟨hηS M, hIS M⟩)
  let l : (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
      (derivedInternalHomOfUniverses.{c, vc, max d vd r, w} J R ⋙
        E.functor.mapDerivedCategory) ≅ T.op.prod (IR ⋙ T) ⋙ H :=
    Functor.isoWhiskerRight eR E.functor.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft
        (((𝟭 _).prod IR) ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)))
        E.functor.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft ((𝟭 _).prod IR)
        (Functor.isoWhiskerRight γ DerivedCategory.Q)
  let r : (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
      ((E.functor.mapDerivedCategory.op.prod E.functor.mapDerivedCategory) ⋙
        derivedInternalHomOfUniverses.{d, vd, max c vc r, w'} K S) ≅
      T.op.prod (T ⋙ IS) ⋙ H :=
    Functor.isoWhiskerRight
      (NatIso.prod
        ((Functor.opComp DerivedCategory.Q E.functor.mapDerivedCategory).symm ≪≫
          (NatIso.op E.functor.mapDerivedCategoryFactors).symm ≪≫
          Functor.opComp T DerivedCategory.Q)
        E.functor.mapDerivedCategoryFactors)
      (derivedInternalHomOfUniverses.{d, vd, max c vc r, w'} K S) ≪≫
      Functor.isoWhiskerLeft (T.op.prod T) eS
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
    ((HomologicalComplex.quasiIso A (.up ℤ)).op.prod
      (HomologicalComplex.quasiIso A (.up ℤ))) (DerivedCategory B)).preimageIso
      (l ≪≫ asIso α ≪≫ (asIso β).symm ≪≫ r.symm)⟩

end CategoryTheory.NativeRestriction
