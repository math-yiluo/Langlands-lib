/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Constructibility under a surjective coefficient restriction
Source: Stacks Project, Tag 09AJ, definition-constructible; Tag 09BR, scalar restriction
in the coefficient-filtration argument.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
universe u v w
open CategoryTheory CategoryTheory.ConstantCompletion CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

section
variable {C E : Type w} [SmallCategory C] [SmallCategory E]
    (T : GrothendieckTopology C) (V : GrothendieckTopology E)
    (A B : Type w) [CommRing A] [CommRing B] (f : A →+* B)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance (priority := 20000) restrictionModuleSheafify
    {D : Type w} [SmallCategory D] (J : GrothendieckTopology D)
    (R : Type w) [CommRing R] : HasSheafify J (ModuleCat.{w} R) := by
  let : PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget (ModuleCat.{w} R)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := R)
  infer_instance

private instance (priority := 20000) restrictionWeakModuleSheafify
    {D : Type w} [SmallCategory D] (J : GrothendieckTopology D)
    (R : Type w) [CommRing R] : HasWeakSheafify J (ModuleCat.{w} R) :=
  (restrictionModuleSheafify J R).isRightAdjoint

-- Restriction preserves the Kan extension and the subsequent sheafification.
private noncomputable def restrictionPullback (G : C ⥤ E) [G.IsContinuous T V]
    (F : Sheaf T (ModuleCat.{w} B)) :
    (Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} A) T V).obj
        ((sheafCompose T (ModuleCat.restrictScalars f)).obj F) ≅
      (sheafCompose V (ModuleCat.restrictScalars f)).obj
        ((Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} B) T V).obj F) :=
  (presheafToSheaf V (ModuleCat.{w} A)).mapIso
    (Functor.leftKanExtensionCompIsoOfPreserves
      (ModuleCat.restrictScalars f) F.obj G.op).symm ≪≫
    (sheafComposeNatIso V (ModuleCat.restrictScalars f)
      (sheafificationAdjunction V (ModuleCat.{w} B))
      (sheafificationAdjunction V (ModuleCat.{w} A))).app (G.op.lan.obj F.obj)

-- The two actions agree by naturality of the constant-ring unit.
private noncomputable def restrictionFixed
    (F : Mod (constant T B)) :
    (coefficientModelFixedScalars T A).obj ((res (adicFiniteConstantMap f T)).obj F) ≅
      (sheafCompose T (ModuleCat.restrictScalars f)).obj
        ((coefficientModelFixedScalars T B).obj F) := by
  have hunit (U : Cᵒᵖ) (a : A) :
      ((adicFiniteConstantMap f T).hom.app U)
          (((SheafOfModules.constantCoefficientUnit T A).app U) a) =
        ((SheafOfModules.constantCoefficientUnit T B).app U) (f a) := by
    exact (ConcreteCategory.congr_hom
      (congrArg (fun t ↦ t.app U)
        (toSheafify_naturality T
          ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))) a).symm
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun U ↦ ?_) ?_
  · apply ModuleCat.isoMk
      (M := ((coefficientModelFixedScalars T A).obj
        ((res (adicFiniteConstantMap f T)).obj F)).obj.obj U)
      (N := ((sheafCompose T (ModuleCat.restrictScalars f)).obj
        ((coefficientModelFixedScalars T B).obj F)).obj.obj U)
      (Iso.refl _)
    intro a
    ext m
    let : Module ((SheafOfModules.constantCoefficientRing T B).obj.obj U)
        (F.val.obj U) := (F.val.obj U).isModule
    change (((SheafOfModules.constantCoefficientUnit T B).app U) (f a)) •
        (show F.val.obj U from m) =
      (((adicFiniteConstantMap f T).hom.app U)
        (((SheafOfModules.constantCoefficientUnit T A).app U) a)) •
          (show F.val.obj U from m)
    rw [hunit]
  · intro U W g
    ext x
    rfl

-- The same generators work after a surjective change of coefficient ring.
private theorem restrictionFinite [IsNoetherianRing A] (hf : Function.Surjective f)
    (M : ModuleCat.{w} B) [Module.Finite B M] :
    Module.FinitePresentation A ((ModuleCat.restrictScalars f).obj M) := by
  let : Algebra A B := f.toAlgebra
  let : Module A M := Module.compHom M f
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hfg : (⊤ : Submodule A M).FG := by
    simpa using (Module.Finite.fg_top (R := B) (M := M)).restrictScalars_of_surjective hf
  have : Module.Finite A M := ⟨hfg⟩
  change Module.FinitePresentation A M
  exact Module.finitePresentation_of_finite A M
end

-- Reuse the strata and covering sieves, changing only their constant module models.
private theorem restrictionConstructible (X : Scheme.{u})
    (A B : Type (max v (u + 1))) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    (F : Mod (constant (coefficientProEtaleModelTopology.{u, v} X) B))
    (G : Mod (constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (e : G ≅ (res (adicFiniteConstantMap f
      (coefficientProEtaleModelTopology.{u, v} X))).obj F)
    (hF : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X B F) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A G := by
  intro U hU
  obtain ⟨S, hc, hs⟩ := hF U hU
  refine ⟨S, hc, ?_⟩
  intro a V
  obtain ⟨T, hT, ht⟩ := hs a V
  refine ⟨T, hT, ?_⟩
  intro W g hg
  obtain ⟨M, hM, ⟨i⟩⟩ := ht W g hg
  have := hM
  refine ⟨(ModuleCat.restrictScalars.{max v (u + 1)} f).obj M, restrictionFinite A B f hf M, ⟨?_⟩⟩
  let j := (coefficientProEtaleFixedModulePullback (S.immersion a ≫ U.ι) A).mapIso
    ((coefficientModelFixedScalars _ A).mapIso e ≪≫ restrictionFixed _ A B f F) ≪≫
    restrictionPullback _ _ A B f
      (coefficientProEtaleModelBaseChange (S.immersion a ≫ U.ι))
      ((coefficientModelFixedScalars _ B).obj F)
  exact ((coefficientProEtaleModelTopology (S.domain a)).overPullback
      (ModuleCat.{max v (u + 1)} A) W).mapIso j ≪≫
    (sheafCompose ((coefficientProEtaleModelTopology (S.domain a)).over W)
      (ModuleCat.restrictScalars.{max v (u + 1)} f)).mapIso i ≪≫
    (constantCommuteCompose ((coefficientProEtaleModelTopology (S.domain a)).over W)
      (ModuleCat.restrictScalars.{max v (u + 1)} f)).app M

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Exact restriction along a surjective map of Noetherian coefficient rings preserves
constructibility of each cohomology sheaf. No boundedness is required.

Source: Stacks Project, proetale.tex, Tag 09AJ, definition-constructible;
Tag 09BR, lemma-compare-truncations-constructible, scalar restriction in the induction.
(auxiliary; not a blueprint node).

Proof: Exact scalar restriction commutes with cohomology, stratum inverse image and
slice restriction through their canonical comparisons. A finite B-module restricts
to a finite A-module because A -> B is surjective, with the same generators; over
the Noetherian ring A it is finitely presented. Constant realization commutes with
restriction, retaining the same strata. Apply this sheaf assertion to the canonical
exact cohomology comparison. This argument also applies to a zero coefficient ring and
the empty scheme. -/
theorem coefficientSurjectiveRestriction_constructible (X : Scheme.{u})
    (A B : Type (max v (u + 1))) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    (K : adicFiniteAmbient.{u, v} X B) (q : ℤ)
    (hK : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X B
      ((coefficientModelCohomology _ q).obj K)) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X A
      ((coefficientModelCohomology _ q).obj
        ((dres (adicFiniteConstantMap f
          (coefficientProEtaleModelTopology.{u, v} X))).obj K)) := by
  let φ := adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)
  let := HasDerivedCategory.standard (Mod (constant
    (coefficientProEtaleModelTopology.{u, v} X) A))
  let := HasDerivedCategory.standard (Mod (constant
    (coefficientProEtaleModelTopology.{u, v} X) B))
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  exact restrictionConstructible X A B f hf _ _
    (((res φ).mapDerivedCategoryHomologyFunctorIso q).app K).symm hK

end AlgebraicGeometry.Scheme
