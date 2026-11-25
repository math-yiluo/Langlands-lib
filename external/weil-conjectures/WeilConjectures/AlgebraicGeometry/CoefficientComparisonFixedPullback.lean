/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-! # Constant scalars and comparison commute with scheme inverse image
Source: Stacks Project, Tags 099Y, 099R and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.ProEtale

section Scalars
universe w
variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type w) [CommRing A]

private theorem scalars_equivalence : (coefficientModelFixedScalars J A).IsEquivalence := by
  let α := SheafOfModules.constantCoefficientUnit J A
  let Q := SheafOfModules.forget (SheafOfModules.constantCoefficientRing J A) ⋙
    PresheafOfModules.restrictScalars α
  let lift {M N : SheafOfModules.{w} (SheafOfModules.constantCoefficientRing J A)}
      (f : (coefficientModelFixedScalars J A).obj M ⟶
        (coefficientModelFixedScalars J A).obj N) : Q.obj M ⟶ Q.obj N :=
    { app := f.hom.app
      naturality := fun {_ _} g ↦ by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  let ff : (coefficientModelFixedScalars J A).FullyFaithful :=
    { preimage := fun f ↦ Q.preimage (lift f)
      map_preimage := fun f ↦ by
        ext U x
        exact congrArg (fun k ↦ k.app U x) (Q.map_preimage (lift f))
      preimage_map := fun f ↦ by
        apply Q.map_injective
        exact (Q.map_preimage (lift ((coefficientModelFixedScalars J A).map f))) }
  have := ff.full
  have := ff.faithful
  have : (coefficientModelFixedScalars J A).EssSurj := by
    constructor
    intro F
    let P : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) :=
      { obj := F.obj.obj
        map := fun f ↦ F.obj.map f
        map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (F.obj.map_id U) x
        map_comp := fun f g ↦ by
          ext x
          exact ConcreteCategory.congr_hom (F.obj.map_comp f g) x }
    let M := PresheafOfModules.sheafify α (M₀ := P)
      (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F) (𝟙 _)
    let t := PresheafOfModules.toSheafify α (M₀ := P)
      (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F) (𝟙 _)
    let e : F ≅ (coefficientModelFixedScalars J A).obj M :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
        (LinearEquiv.ofBijective (t.app U).hom (Function.bijective_id)).toModuleIso)
        (by intro U V f; ext x; rfl))
    exact ⟨M, ⟨e.symm⟩⟩
  exact {}
end Scalars

private theorem comparison_unit_scalar (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (U : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) (a : A) :
    (constructibleComparisonRingMap X A).hom.app U
        ((SheafOfModules.constantCoefficientUnit
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).app U a) =
      (SheafOfModules.constantCoefficientUnit
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).app
          ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) a := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  have h := ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
    ((Functor.const _).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj
      (ConstantCompletion.constant K A))).apply_symm_apply
        (Functor.whiskerLeft F.op (toSheafify K
          ((Functor.const _).obj (CommRingCat.of A))))
  exact congrArg (fun k ↦ k.app U a) h

private def comparison_direct_scalars (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.pushforward (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A) ⋙
        coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
        (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      exact congrArg (fun b ↦
        @SMul.smul _
          (M.val.obj ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U))
          (M.val.obj ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U)).isModule.toSMul
          b x) (comparison_unit_scalar X A U a).symm))
      (by intro U V f; ext x; rfl))) (by intro M N f; ext U x; rfl)

private def comparison_scalars (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    constructibleComparisonPullback.{u, v} X A ⋙
        coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have := scalars_equivalence (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalars_equivalence (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let E := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let P := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  let adjM := SheafOfModules.pullbackPushforwardAdjunction
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)
  let adjF := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let adj := E.symm.toAdjunction.comp (adjM.comp P.toAdjunction)
  let eR := Functor.isoWhiskerLeft P.inverse (comparison_direct_scalars X A) ≪≫
    Functor.isoWhiskerRight P.counitIso
      ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X))
  let eL := (adj.ofNatIsoRight eR).leftAdjointUniq adjF
  exact Functor.isoWhiskerRight E.unitIso
      (constructibleComparisonPullback X A ⋙ P.functor) ≪≫
    Functor.isoWhiskerLeft E.functor eL

private def comparison_baseChange {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) ⋙
        Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A ≅
      Scheme.coefficientEtaleFixedPullback.{u, v} f A ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} Y) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} Y)
          (Scheme.coefficientProEtaleModelTopology.{u, v} Y) := by
  let C := Scheme.smallModelComparisonInclusion.{u, v} X
  let D := Scheme.smallModelComparisonInclusion.{u, v} Y
  let F := Scheme.coefficientProEtaleModelBaseChange.{u, v} f
  let G := Scheme.coefficientEtaleBaseChange.{u, v} f
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let L := Scheme.smallModelComparisonEtaleTopology.{u, v} Y
  let M := Scheme.coefficientProEtaleModelTopology.{u, v} Y
  have : (C ⋙ F).IsContinuous J M := Functor.isContinuous_comp C F J K M
  have : (G ⋙ D).IsContinuous J M := Functor.isContinuous_comp G D J L M
  let e : C ⋙ F ≅ G ⋙ D :=
    Functor.isoWhiskerLeft AsSmall.down
      (Functor.isoWhiskerRight (toProEtCompOverPullbackIso f) AsSmall.up)
  let adj₁ := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous C
    (ModuleCat A) J K).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (ModuleCat A) K M)
  let adj₂ := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat A) J L).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous D (ModuleCat A) L M)
  let eR := Functor.sheafPushforwardContinuousComp C F (ModuleCat A) J K M ≪≫
    Functor.sheafPushforwardContinuousIso e (ModuleCat A) J M ≪≫
    (Functor.sheafPushforwardContinuousComp G D (ModuleCat A) J L M).symm
  exact (adj₁.ofNatIsoRight eR).leftAdjointUniq adj₂

/-- For schemes X and Y and a morphism f : Y → X, and any commutative ring A in the independent
coefficient universe, the canonical intrinsic-module comparison inverse image on X followed by
constant-scalar restriction and pro-etale inverse image along f is naturally isomorphic to
constant-scalar restriction on X followed by etale inverse image along f and fixed-scalar
comparison inverse image on Y. All sites and functors are the recorded coefficient-sized models
[lem-pe-coefficient-comparison-data], [def-pe-etale-constructible-module], and [def-sfb-affine-
locally-constructible-proetale-modules]. No constructibility or Noetherianity hypothesis is
used.

Source: Stacks Project, Tags 099R, 00VC and 03CY
(auxiliary; not a blueprint node).

Proof: The constant-ring unit is locally bijective. Scalar restriction is fully faithful by
the Mathlib locally-surjective scalar-restriction Hom equivalence. To construct an antecedent
of a fixed-
scalar sheaf, apply module sheafification to the identity of its underlying abelian sheaf. The
sheafification unit extends the scalar action; identity maps give its inverse isomorphism. Thus
the literal coefficientModelFixedScalars functor is an equivalence.
The ring-map adjunction equation states that constructibleComparisonRingMap sends each constant
scalar to the same constant scalar. This identifies module direct image followed by scalar
restriction with scalar restriction followed by fixed-scalar comparison direct image, by
identity linear maps on sections. Conjugate through the two scalar equivalences and use
uniqueness of left adjoints to identify the two comparison inverse images.
On site objects comparison and scheme base change commute: both are the same fibre product.
Whisker the original site natural isomorphism by AsSmall.down and AsSmall.up. Its isomorphism on
continuous direct images identifies the right adjoints of the two inverse-image composites.
Uniqueness of left adjoints gives their inverse-image isomorphism. Whisker and compose it with
the scalar comparison of the preceding step. -/
theorem coefficientComparison_fixedPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty
      (constructibleComparisonPullback.{u, v} X A ⋙
          coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
          Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A ≅
        coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ⋙
          Scheme.coefficientEtaleFixedPullback.{u, v} f A ⋙
          Functor.sheafPullbackConstruction.sheafPullback
            (Scheme.smallModelComparisonInclusion.{u, v} Y) (ModuleCat.{max v (u + 1)} A)
            (Scheme.smallModelComparisonEtaleTopology.{u, v} Y)
            (Scheme.coefficientProEtaleModelTopology.{u, v} Y))  := by
  exact ⟨Functor.isoWhiskerRight (comparison_scalars X A)
      (Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A) ≪≫
    Functor.isoWhiskerLeft
      (coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)
      (comparison_baseChange f A)⟩

end AlgebraicGeometry.ProEtale
