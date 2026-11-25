/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicConstructibleFiniteReductions
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedStalk
public import WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Scalar extension at the explicit coefficient-sized geometric stalk

Source: Stacks Project, Tags 03EL, 05V7, 05V8, 07A6 and 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem skyscraper_colimits
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (p : GrothendieckTopology.Point.{u} J)
    {A : Type*} [Category A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [HasFiniteColimits A] [AB4StarOfSize.{u} A] :
    PreservesFiniteColimits (p.skyscraperSheafFunctor (A := A)) := by
  have hp (U : Cᵒᵖ) : PreservesFiniteColimits
      (p.skyscraperPresheafFunctor ⋙ (CategoryTheory.evaluation Cᵒᵖ A).obj U) := by
    let α := p.fiber.obj U.unop
    let F : A ⥤ Discrete α ⥤ A := Functor.const (Discrete α)
    have : PreservesFiniteColimits F := by
      apply preservesFiniteColimits_of_evaluation
      intro a
      exact preservesFiniteColimits_of_natIso
        (show 𝟭 A ≅ F ⋙ (CategoryTheory.evaluation (Discrete α) A).obj a from
          NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp [F]))
    have : PreservesFiniteColimits (F ⋙ lim) := comp_preservesFiniteColimits _ _
    exact preservesFiniteColimits_of_natIso
      (show F ⋙ lim ≅ p.skyscraperPresheafFunctor ⋙ (CategoryTheory.evaluation Cᵒᵖ A).obj U from
        NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
          intro M N f
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          apply (limit.isLimit (F.obj N)).hom_ext
          intro a
          change limMap (F.map f) ≫ limit.π (F.obj N) a =
            Limits.Pi.map (fun _ : α ↦ f) ≫ Pi.π (fun _ : α ↦ N) a.as
          rw [limMap_π, Pi.map_π]
          rfl))
  have : PreservesFiniteColimits (p.skyscraperSheafFunctor ⋙ sheafToPresheaf J A) :=
    preservesFiniteColimits_of_evaluation _ hp
  have : ReflectsColimitsOfSize.{0, 0} (sheafToPresheaf J A) :=
    fullyFaithful_reflectsColimits _
  have : ReflectsFiniteColimits (sheafToPresheaf J A) :=
    ReflectsColimitsOfSize.reflectsFiniteColimits.{0, 0} _
  exact preservesFiniteColimits_of_reflects_of_preserves _ (sheafToPresheaf J A)

private theorem coefficient_unit_naturality
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    {B R : Type w} [CommRing B] [CommRing R] (f : B →+* R) (U : Cᵒᵖ) (b : B) :
    ((adicFiniteConstantMap f J).hom.app U)
        ((SheafOfModules.constantCoefficientUnit J B).app U b) =
      (SheafOfModules.constantCoefficientUnit J R).app U (f b) := by
  exact (ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.app U)
      (toSheafify_naturality J
        ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f)))) b).symm

private def fixed_restriction
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    {B R : Type w} [CommRing B] [CommRing R] (f : B →+* R) :
    ConstantCompletion.res (adicFiniteConstantMap f J) ⋙ coefficientModelFixedScalars J B ≅
      coefficientModelFixedScalars J R ⋙ sheafCompose J (ModuleCat.restrictScalars f) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun b ↦ by
      ext m
      exact congrArg (fun a ↦ @SMul.smul _ (M.val.obj U)
        (M.val.obj U).isModule.toSMul a m) (coefficient_unit_naturality J f U b).symm))
      (by intros; ext m; rfl))) (by intros; ext U m; rfl)

private def skyscraper_restriction
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (p : GrothendieckTopology.Point.{u} J)
    {A D : Type*} [Category A] [Category D]
    [HasProducts.{u} A] [HasProducts.{u} D]
    (V : A ⥤ D) [PreservesLimitsOfSize.{u, u} V] [J.HasSheafCompose V] :
    p.skyscraperSheafFunctor (A := A) ⋙ sheafCompose J V ≅
      V ⋙ p.skyscraperSheafFunctor (A := D) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦
      PreservesProduct.iso V (fun _ : p.fiber.obj U.unop ↦ M)) ?_)) ?_
  · intro U W g
    apply Pi.hom_ext
    intro a
    simp only [PreservesProduct.iso_hom, Category.assoc]
    change V.map (Pi.map' (p.fiber.map g.unop) (fun _ ↦ 𝟙 M)) ≫
        piComparison V (fun _ : p.fiber.obj W.unop ↦ M) ≫ Pi.π _ a =
      piComparison V (fun _ : p.fiber.obj U.unop ↦ M) ≫
        Pi.map' (p.fiber.map g.unop) (fun _ ↦ 𝟙 (V.obj M)) ≫ Pi.π _ a
    simp only [piComparison_comp_π, ← V.map_comp, Pi.map'_comp_π, Category.comp_id]
  · intro M N g
    ext U
    apply Pi.hom_ext
    intro a
    change (V.map (Limits.Pi.map (fun _ : p.fiber.obj U.unop ↦ g)) ≫
        piComparison V (fun _ : p.fiber.obj U.unop ↦ N)) ≫ Pi.π _ a =
      (piComparison V (fun _ : p.fiber.obj U.unop ↦ M) ≫
        Limits.Pi.map (fun _ : p.fiber.obj U.unop ↦ V.map g)) ≫ Pi.π _ a
    simp only [Category.assoc]
    rw [Pi.map_π, piComparison_comp_π, ← V.map_comp]
    rw [Pi.map_π, V.map_comp, piComparison_comp_π_assoc]

private def stalk_presentation (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B] :
    ConstantCompletion.Mod
        (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) ≌
      Sheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  have := ProEtale.scalars_equivalence J B
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.IsDenseSubsite
      J X.smallEtaleTopology := by
    change (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      (AsSmall.down.inducedTopology X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  exact (coefficientModelFixedScalars J B).asEquivalence.trans
    ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).sheafCongr
      X.smallEtaleTopology J (ModuleCat.{max v (u + 1)} B)).symm

private def presentation_restriction (X : Scheme.{u})
    {B R : Type (max v (u + 1))} [CommRing B] [CommRing R] (f : B →+* R) :
    ConstantCompletion.res
        (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        (stalk_presentation X B).functor ≅
      (stalk_presentation X R).functor ⋙
        sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars f) :=
  Functor.isoWhiskerRight
      (fixed_restriction (smallModelComparisonEtaleTopology.{u, v} X) f)
      ((AsSmall.up : X.Etale ⥤ smallModelComparisonEtaleSite.{u, v} X).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} B)
          X.smallEtaleTopology (smallModelComparisonEtaleTopology.{u, v} X)) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def inverse_presentation_restriction (X : Scheme.{u})
    {B R : Type (max v (u + 1))} [CommRing B] [CommRing R] (f : B →+* R) :
    sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars f) ⋙
        (stalk_presentation X B).inverse ≅
      (stalk_presentation X R).inverse ⋙ ConstantCompletion.res
        (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) :=
  by
    let E := stalk_presentation X B
    let F := stalk_presentation X R
    let U := ConstantCompletion.res
      (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
    let V := sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars f)
    let i : U ⋙ E.functor ≅ F.functor ⋙ V := presentation_restriction X f
    let j : F.inverse ⋙ (U ⋙ E.functor) ≅ V :=
      Functor.isoWhiskerLeft F.inverse i ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.counitIso V ≪≫ V.leftUnitor
    exact (j.isoCompInverse).symm

private theorem scalar_adjunction
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    {B R : Sheaf J CommRingCat.{w}} (f : B ⟶ R) :
    Nonempty (ConstantCompletion.extend f ⊣ ConstantCompletion.dres f) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  obtain ⟨E, hobj, hmap, _, hpres, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients f
  have hE : E = ConstantCompletion.change f :=
    CategoryTheory.Functor.ext hobj (fun _ _ a ↦ hmap a)
  have hpres' : ∀ {P Q : ConstantCompletion.Cx B} (a : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
        QuasiIso a → QuasiIso
          (((ConstantCompletion.change f).mapHomologicalComplex (.up ℤ)).map a) := by
    cases hE
    exact hpres
  obtain ⟨_, L, ε, hu, _, adj, _⟩ :=
    Adjunction.exists_leftDerived_adjunction
      (ConstantCompletion.change f) (ConstantCompletion.res f)
      (SheafOfModules.tensorAdjunction f)
      (CochainComplex.IsKFlatIndependentCoefficients (R := B))
      (fun P ↦ by
        obtain ⟨Y, t, hY, _, ht, _⟩ :=
          CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
        exact ⟨Y, t, hY, ht⟩) hpres'
  let : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod B) (.up ℤ)) := hu
  let : (ConstantCompletion.extend f).IsLeftDerivedFunctor
      (ConstantCompletion.extendComparison f)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod B) (.up ℤ)) :=
    (ConstantCompletion.derivedExtension f).universal
  exact ⟨adj.ofNatIsoLeft
    (Functor.leftDerivedUnique (ConstantCompletion.extend f) L ε
      (ConstantCompletion.extendComparison f)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod B) (.up ℤ)))⟩

private def stalk_right (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ModuleCat.{max v (u + 1)} B ⥤ ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  exact (pointSmallEtale x).skyscraperSheafFunctor (A := ModuleCat.{max v (u + 1)} B) ⋙
    (stalk_presentation X B).inverse

private def stalk_adjunction (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    coefficientEtaleModuleStalk X B x ⊣ stalk_right X B x := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  exact (stalk_presentation X B).toAdjunction.comp
    ((pointSmallEtale x).skyscraperSheafAdjunction (A := ModuleCat.{max v (u + 1)} B))

attribute [local irreducible] stalk_presentation

private theorem stalk_right_colimits (X : Scheme.{u})
    (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    PreservesFiniteColimits (stalk_right X B x) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  have : AB4StarOfSize.{u} (ModuleCat.{max v (u + 1)} B) :=
    AB4StarOfSize_shrink.{u, max v (u + 1)} _
  have := skyscraper_colimits (pointSmallEtale x) (A := ModuleCat.{max v (u + 1)} B)
  exact comp_preservesFiniteColimits
    ((pointSmallEtale x).skyscraperSheafFunctor (A := ModuleCat.{max v (u + 1)} B))
    (stalk_presentation X B).inverse

private def stalk_right_restriction (X : Scheme.{u})
    {B R : Type (max v (u + 1))} [CommRing B] [CommRing R] (f : B →+* R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ModuleCat.restrictScalars.{max v (u + 1)} f ⋙ stalk_right X B x ≅
      stalk_right X R x ⋙ ConstantCompletion.res
        (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  let V := ModuleCat.restrictScalars.{max v (u + 1)} f
  let T := sheafCompose X.smallEtaleTopology V
  let U := ConstantCompletion.res
    (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
  let E := stalk_presentation X B
  let F := stalk_presentation X R
  let pB := (pointSmallEtale x).skyscraperSheafFunctor
    (A := ModuleCat.{max v (u + 1)} B)
  let pR := (pointSmallEtale x).skyscraperSheafFunctor
    (A := ModuleCat.{max v (u + 1)} R)
  let α : pR ⋙ T ≅ V ⋙ pB := skyscraper_restriction (pointSmallEtale x) V
  let β : T ⋙ E.inverse ≅ F.inverse ⋙ U := inverse_presentation_restriction X f
  change V ⋙ (pB ⋙ E.inverse) ≅ (pR ⋙ F.inverse) ⋙ U
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α.symm E.inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft pR β ≪≫
    (Functor.associator _ _ _).symm

/-- Exact geometric stalks commute with arbitrary derived extension of constant scalars.
Both functors here are the previously constructed functors, not unspecified scalar
extensions. No boundedness, constructibility or nilpotence is required.
Source: Stacks Project, Modules on Sites, Tags 03EL, 05V7 and 05V8;
Cohomology on Sites, Tag 07A6; Derived Categories, Tag 015F.
(auxiliary; not a blueprint node).

Proof: combine the fixed-scalar equivalence with the AsSmall equivalence, retaining
its actual continuous direct-image functor. The ordinary stalk is left adjoint to the
usual product-valued skyscraper functor followed by the inverse of this presentation.
Products of modules are exact, so this right adjoint is exact (Modules on Sites,
Tags 05V7 and 05V8). Both sides of the stalk adjunction therefore localize termwise.
Naturality of the constant-ring sheafification unit identifies intrinsic restriction
with fixed-scalar restriction through the presentation. Restriction of modules
preserves products, giving a natural isomorphism between the two ordinary composite
right adjoints. Localize this exact square. Derived scalar extension of sheaves is
left adjoint to the existing exact restriction: resolve by K-flat complexes, derive
the ordinary tensor adjunction, then identify its left derived functor with the
specified ConstantCompletion.extend by its universal property. The module scalar
adjunction is already provided. Compose each scalar adjunction with the appropriate
derived stalk adjunction. Their right adjoints are isomorphic by the localized square;
uniqueness of left adjoints gives the desired isomorphism at K. This argument requires
no flatness or boundedness, and applies also to zero coefficient rings. -/
theorem coefficientEtale_stalk_scalarExtension
    (X : Scheme.{u}) {B R : Type (max v (u + 1))} [CommRing B] [CommRing R]
    (f : B →+* R) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (K : ConstantCompletion.D
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B)) :
    Nonempty
      ((ConstantScalarRealization.moduleDerivedExtension f).obj
          ((coefficientEtaleDerivedStalk X B x).obj K) ≅
        (coefficientEtaleDerivedStalk X R x).obj
          ((adicFiniteExtension (smallModelComparisonEtaleTopology.{u, v} X) f).obj K)) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let φ := adicFiniteConstantMap f J
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J B))
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J R))
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  have := (stalk_adjunction X B x).isRightAdjoint
  have := (stalk_adjunction X R x).isRightAdjoint
  have := (stalk_adjunction X B x).right_adjoint_additive
  have := (stalk_adjunction X R x).right_adjoint_additive
  have := stalk_right_colimits X B x
  have := stalk_right_colimits X R x
  let aB := (stalk_adjunction X B x).mapExactDerivedCategory
  let aR := (stalk_adjunction X R x).mapExactDerivedCategory
  obtain ⟨aS⟩ := scalar_adjunction φ
  let aM := ConstantScalarRealization.moduleDerivedAdjunction f
  let e := Functor.mapDerivedCategorySquareIso (stalk_right_restriction X f x)
  exact ⟨(((aB.comp aM).ofNatIsoRight e).leftAdjointUniq (aS.comp aR)).app K⟩

end AlgebraicGeometry.Scheme
