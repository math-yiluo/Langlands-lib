/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.SiteModuleExtensionByZeroExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Scalar-restriction acyclicity for sections on an arbitrary slice

Source: Stacks Project, Tag 0D6E and Modules on Sites, Tags 03DI and 03DJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

universe a v r
variable {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max a v r} RingCat.{max a v r})]
  [HasSheafify J AddCommGrpCat.{max a v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a v r}]

private theorem scalar_section_quasiIso
    {B D : Sheaf J CommRingCat.{max a v r}} (b : B ⟶ D)
    (I : CochainComplex (SheafOfModules.{max a v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj D)) ℤ)
    (K : CochainComplex (SheafOfModules.{max a v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
    (j : ((SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] (U : C) :
    QuasiIso (((SheafOfModules.toSheaf _ ⋙
      sheafToPresheaf J AddCommGrpCat.{max a v r} ⋙
      (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map j) := by
  let : EssentiallySmall.{max a v r} (Over U) := essentiallySmallSelf.{r, v, max a v} _
  let : HasSheafify (J.over U) AddCommGrpCat.{max a v r} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max a v r} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let BR := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let DR := (sheafCompose J (forget₂ CommRingCat RingCat)).obj D
  let q := J.overPullback CommRingCat.{max a v r} U
  let resB := SheafOfModules.overFunctor.{max a v r} BR U
  let resD := SheafOfModules.overFunctor.{max a v r} DR U
  have : resB.Additive := ⟨fun {_ _} f g ↦ by ext V x; rfl⟩
  have : resD.Additive := ⟨fun {_ _} f g ↦ by ext V x; rfl⟩
  have hB := SheafOfModules.overFunctor_exact_ofUniverses.{a, v, max a v r} BR U
  have := hB.1
  have := hB.2
  have : resB.PreservesKInjectiveComplexes :=
    overFunctor_preservesKInjectiveComplexes_ofUniverses.{a, v, max a v r} BR U
  have : resD.PreservesKInjectiveComplexes :=
    overFunctor_preservesKInjectiveComplexes_ofUniverses.{a, v, max a v r} DR U
  let forgetSlice := sheafCompose (J.over U)
    (forget₂ CommRingCat.{max a v r} RingCat.{max a v r})
  let I' : CochainComplex (SheafOfModules.{max a v r} (forgetSlice.obj (q.obj D))) ℤ :=
    (resD.mapHomologicalComplex (.up ℤ)).obj I
  let K' : CochainComplex (SheafOfModules.{max a v r} (forgetSlice.obj (q.obj B))) ℤ :=
    (resB.mapHomologicalComplex (.up ℤ)).obj K
  let j' : ((SheafOfModules.restrictScalars (forgetSlice.map (q.map b))).mapHomologicalComplex
      (.up ℤ)).obj I' ⟶ K' := (resB.mapHomologicalComplex (.up ℤ)).map j
  have : CochainComplex.IsKInjective I' := inferInstanceAs
    (CochainComplex.IsKInjective ((resD.mapHomologicalComplex (.up ℤ)).obj I))
  have : CochainComplex.IsKInjective K' := inferInstanceAs
    (CochainComplex.IsKInjective ((resB.mapHomologicalComplex (.up ℤ)).obj K))
  have : QuasiIso j' := inferInstanceAs
    (QuasiIso ((resB.mapHomologicalComplex (.up ℤ)).map j))
  have hq := coefficientRestrictionSections_quasiIso.{max a v, v, max a v r} (q.map b) I' K' j'
  let Γ := SheafOfModules.toSheaf (BR.over U) ⋙
    sheafToPresheaf (J.over U) AddCommGrpCat.{max a v r} ⋙ lim
  let ev := SheafOfModules.toSheaf (BR.over U) ⋙
    (sheafSections (J.over U) AddCommGrpCat.{max a v r}).obj (op (Over.mk (𝟙 U)))
  let e : Γ ≅ ev := Functor.isoWhiskerLeft (SheafOfModules.toSheaf (BR.over U))
    ((Sheaf.ΓNatIsoLim _ _).symm ≪≫ Sheaf.ΓNatIsoSheafSections _ _ Over.mkIdTerminal)
  have ht : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map j') :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex e (.up ℤ)) (Arrow.mk j'))).mp hq
  exact ht

omit [HasSheafify J AddCommGrpCat.{max a v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max a v r}] in
private theorem commutativeRingLift (B : Sheaf J RingCat.{max a v r})
    (hB : ∀ (U : Cᵒᵖ) (x y : B.obj.obj U), x * y = y * x) :
    ∃ O : Sheaf J CommRingCat.{max a v r},
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj O = B := by
  let obj (U : Cᵒᵖ) : CommRingCat.{max a v r} :=
    { carrier := B.obj.obj U
      commRing := { (inferInstance : Ring (B.obj.obj U)) with mul_comm := hB U } }
  let Oc : Cᵒᵖ ⥤ CommRingCat.{max a v r} :=
    { obj := obj
      map := fun {U V} g ↦
        @CommRingCat.ofHom (obj U) (obj V) (obj U).commRing (obj V).commRing
          (B.obj.map g).hom
      map_id := fun U ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (B.obj.map_id U)
      map_comp := fun g h ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (B.obj.map_comp g h) }
  have hO : Presheaf.IsSheaf J Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp J Oc (forget₂ CommRingCat RingCat)
    exact B.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

/-- A scalar-restriction resolution is a quasi-isomorphism on sections over every object.
Source: Stacks Project, Cohomology on Sites, Tag 0D6E, applied on the slice over U;
Modules on Sites, Tags 03DI and 03DJ, for exact extension by zero and slice restriction.
(blueprint: lem-coef-restriction-sections-evaluation-acyclic).

Proof: retain commutativity on B and D without changing the underlying ring sheaves.
Restrict I, K and j to the slice over U. Exact slice restriction preserves the
quasi-isomorphism, and its exact left adjoint shows that it preserves K-injectives.
Apply scalar-restriction acyclicity for global sections on this slice. The identity
of U is terminal in the slice, so its global-sections functor is naturally isomorphic
to evaluation at that identity. This identifies the resulting map with sections of j
on U. Zero coefficient rings and the empty site require no additional hypotheses. -/
theorem coefficientRestrictionSectionsEvaluation_quasiIso
    (B D : Sheaf J RingCat.{max a v r})
    (hB : ∀ (U : Cᵒᵖ) (x y : B.obj.obj U), x * y = y * x)
    (hD : ∀ (U : Cᵒᵖ) (x y : D.obj.obj U), x * y = y * x)
    (b : B ⟶ D)
    (I : CochainComplex (SheafOfModules.{max a v r} D) ℤ)
    (K : CochainComplex (SheafOfModules.{max a v r} B) ℤ)
    (j : ((SheafOfModules.restrictScalars b).mapHomologicalComplex (.up ℤ)).obj I ⟶ K)
    [I.IsKInjective] [K.IsKInjective] [QuasiIso j] (U : C) :
    QuasiIso (((SheafOfModules.toSheaf _ ⋙
      sheafToPresheaf J AddCommGrpCat.{max a v r} ⋙
      (CategoryTheory.evaluation _ _).obj (op U)).mapHomologicalComplex (.up ℤ)).map j) := by
  obtain ⟨B, rfl⟩ := commutativeRingLift.{a, v, r} B hB
  obtain ⟨D, rfl⟩ := commutativeRingLift.{a, v, r} D hD
  obtain ⟨b, rfl⟩ := (sheafCompose J (forget₂ CommRingCat RingCat)).map_surjective b
  exact scalar_section_quasiIso.{a, v, r} b I K j U

end SheafOfModules
