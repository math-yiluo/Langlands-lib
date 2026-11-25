/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
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
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

set_option linter.privateModule false

/-! # Quasi-isomorphism invariance of the Hom complex with smaller coefficient rings

Source: Stacks Project, Tags 03DI, 03DJ, 08FI, 0A8Y, 0A94 and 0A95.
(blueprint: lem-pur-rhom-well-defined-mixed-universes).
The sectionwise proof uses rings in r and module sections in max u v r throughout.
The private helpers generalize the existing independent-universe proofs without changing
any existing interface or replacing the ring sheaf.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace MixedHom
attribute [local irreducible] homComplexFunctor

private theorem fan_projection_bijective.{t} {ι : Type} {X : ι → Type t}
    {P : Type t} (π : ∀ i, P ⟶ X i) (h : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (fun x i ↦ π i x) := by
  let e := h.conePointUniqueUpToIso (Limits.Types.productLimitCone X).isLimit
  have he (x : P) (i : ι) : e.hom x i = π i x :=
    ConcreteCategory.congr_hom (h.conePointUniqueUpToIso_hom_comp
      (Limits.Types.productLimitCone X).isLimit ⟨i⟩) x
  have hf : (fun x i ↦ π i x) = e.toEquiv := by
    funext x i
    exact (he x i).symm
  rw [hf]
  exact e.toEquiv.bijective

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 100000 in
-- Chosen products and section evaluation require extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 100000 in
-- Evaluating chosen Hom-complex projections requires extra elaboration heartbeats.
set_option maxHeartbeats 100000 in
-- Elaborating chosen products through section evaluation requires extra heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 100000 in
-- Projection comparisons involve several composed functors and chosen product objects.
/-- Sectionwise quasi-isomorphisms induce quasi-isomorphisms of module sheaves.
Source: Stacks Project, sites-cohomology.tex, proof of Lemma 0A95

Proof: forget the module structure and view the complexes as complexes of presheaves of
abelian groups. Evaluation at each site object is exact and jointly detects their cohomology
isomorphisms. Sheafification is exact, so the presheaf quasi-isomorphism remains one after
sheafification. The counit of sheafification identifies the resulting complexes naturally
with the original abelian-sheaf complexes. Finally the exact forgetful functor from module
sheaves to abelian sheaves reflects isomorphisms, hence reflects quasi-isomorphisms. -/
private theorem quasiIso_of_sectionsOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J RingCat.{r}}
    {K L : CochainComplex (SheafOfModules.{max u v r} R) ℤ} (f : K ⟶ L)
    (h : ∀ U : C, QuasiIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.evaluation R.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R.obj.obj (op U)))
        AddCommGrpCat.{max u v r}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let T := SheafOfModules.toSheaf R
  let V := sheafToPresheaf J AddCommGrpCat.{max u v r}
  let A := presheafToSheaf J AddCommGrpCat.{max u v r}
  let g := ((T ⋙ V).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  have hg : QuasiIso g := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro U
    let ec := Functor.mapHomologicalComplexCompIso
      (F := T ⋙ V) (G := (evaluation Cᵒᵖ AddCommGrpCat.{max u v r}).obj U)
      (H := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U ⋙
        forget₂ (ModuleCat.{max u v r} (R.obj.obj U)) AddCommGrpCat.{max u v r})
      (Iso.refl _) (ComplexShape.up ℤ)
    have hh := h U.unop
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec.symm (Arrow.mk f))).mp hh
  have hg' : QuasiIso ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    infer_instance
  let e : (T ⋙ V) ⋙ A ≅ T :=
    Functor.associator T V A ≪≫
    Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction J
      AddCommGrpCat.{max u v r}).counit) ≪≫ T.rightUnitor
  let ec := Functor.mapHomologicalComplexCompIso
    (F := T ⋙ V) (G := A) (Iso.refl ((T ⋙ V) ⋙ A)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  have ht : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec (Arrow.mk f))).mp hg'
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f T).mp ht

end MixedHom

end CategoryTheory
