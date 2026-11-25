/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap

/-! # Local strict-henselian stalk criterion for exchange

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_local
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) [IsLocalRing (Scheme.strictHenselizationRing y)] :
    IsLocalHom (Scheme.strictHenselizationRingPointEvaluation y) := by
  let : Algebra (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo y)).hom.toAlgebra
  let e := Scheme.smallStrictHenselizationColimitIso y
  let ψ : Scheme.strictHenselizationRing y →+* _ :=
    (Scheme.strictHenselizationPointEvaluationToSep y rfl).comp e.hom.hom
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    ((Scheme.strictHenselizationPointEvaluationToSep_surjective y rfl).comp
      e.commRingCatIsoToRingEquiv.surjective)
  let ι : separableClosure (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω →+* Ω :=
    (IntermediateField.val _).toRingHom
  have : IsLocalHom ι := inferInstance
  change IsLocalHom (ι.comp ψ)
  infer_instance

private theorem localization_model_transport
    {Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s t : Spec (.of Ω) ⟶ Y) (h : s = t)
    (e : Z ≅ Scheme.strictLocalization s) :
    ∃ e' : Z ≅ Scheme.strictLocalization t,
      e'.hom ≫ Scheme.strictLocalizationToBase t =
        e.hom ≫ Scheme.strictLocalizationToBase s := by
  subst t
  exact ⟨e, rfl⟩

private theorem bijective_conjugate
    {A B C D : Type*} (f : A → B) (g : C → D)
    (e : A ≃ C) (e' : B ≃ D) (h : ∀ x, e' (f x) = g (e x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hh : e' ∘ f = g ∘ e := funext h
  rw [← Function.Bijective.of_comp_iff' e'.bijective f, hh]
  exact Function.Bijective.of_comp_iff g e.bijective

theorem isIso_exchange_stalk_iff_strictLocalCohomology
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (α : (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (f)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((pullback.snd f g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst f g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (hα : α = (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g).toCommSq.flip).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
    (heval : Scheme.strictHenselizationRingPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationRingPointEvaluation x).comp a.hom)
    (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map α) ↔
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q) := by
  classical
  subst α
  obtain ⟨hA, hsA⟩ := strictHenselizationLocalStructure (x ≫ f)
  obtain ⟨hB, hsB⟩ := strictHenselizationLocalStructure x
  let := hA
  let := hB
  have := hsA
  have := hsB
  have : IsSepClosed (IsLocalRing.ResidueField (Scheme.strictHenselizationRing (x ≫ f))) :=
    @IsStrictlyHenselianLocalRing.isSepClosed_residueField _ _ hsA
  have : IsSepClosed (IsLocalRing.ResidueField (Scheme.strictHenselizationRing x)) :=
    @IsStrictlyHenselianLocalRing.isSepClosed_residueField _ _ hsB
  have := evaluation_local (x ≫ f)
  have := evaluation_local x
  have : IsLocalHom ((Scheme.strictHenselizationRingPointEvaluation x).comp a.hom) :=
    heval ▸ evaluation_local (x ≫ f)
  have : IsLocalHom a.hom :=
    isLocalHom_of_comp a.hom (Scheme.strictHenselizationRingPointEvaluation x)
  let jA := Scheme.strictHenselizationStructuralMap (x ≫ f)
  let jB := Scheme.strictHenselizationStructuralMap x
  let eA : Spec (Scheme.strictHenselizationRing (x ≫ f)) ≅
      Scheme.strictLocalization (x ≫ f) :=
    asIso (Spec.map (Scheme.smallStrictHenselizationColimitIso (x ≫ f)).inv)
  let eB : Spec (Scheme.strictHenselizationRing x) ≅ Scheme.strictLocalization x :=
    asIso (Spec.map (Scheme.smallStrictHenselizationColimitIso x).inv)
  have heA : eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f) = jA :=
    Scheme.smallStrictHenselizationColimitIso_toBase (x ≫ f)
  have heB : eB.hom ≫ Scheme.strictLocalizationToBase x = jB :=
    Scheme.smallStrictHenselizationColimitIso_toBase x
  let ρA := Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.lift (Scheme.strictHenselizationRingPointEvaluation (x ≫ f))))
  let ρB := Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.lift (Scheme.strictHenselizationRingPointEvaluation x)))
  have hρA : ρA ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Scheme.strictHenselizationRing (x ≫ f)))) ≫
      eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f) = x ≫ f := by
    rw [heA, ← Spec.map_comp_assoc]
    exact Scheme.strictHenselizationClosedLift_over (x ≫ f)
  have hρB : ρB ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Scheme.strictHenselizationRing x))) ≫
      eB.hom ≫ Scheme.strictLocalizationToBase x = x := by
    rw [heB, ← Spec.map_comp_assoc]
    exact Scheme.strictHenselizationClosedLift_over x
  have hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map a.hom)) =
      𝟙 (Spec (.of Ω)) ≫ ρA := by
    rw [Category.id_comp]
    dsimp only [ρA, ρB]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact heval.symm
  let p₀ := pullback.snd jA g
  let f₀ := pullback.fst jA g
  let p₁ := pullback.map (jB ≫ f) g jA g (Spec.map a) (𝟙 T) (𝟙 S)
    ((Category.comp_id _).trans ha.symm)
    ((Category.comp_id g).trans (Category.id_comp g).symm)
  let f₁ := pullback.fst (jB ≫ f) g
  have sq₀ : IsPullback p₀ f₀ g (eA.hom ≫ Scheme.strictLocalizationToBase (x ≫ f)) := by
    rw [heA]
    exact (IsPullback.of_hasPullback jA g).flip
  have sq₁ : IsPullback p₁ f₁ f₀ (Spec.map a) := by
    refine IsPullback.of_right ?_ (by simp [p₁, f₁, f₀])
      (IsPullback.of_hasPullback jA g).flip
    have hp : p₁ ≫ pullback.snd jA g = pullback.snd (jB ≫ f) g := by simp [p₁]
    rw [hp, ha]
    exact (IsPullback.of_hasPullback (jB ≫ f) g).flip
  obtain ⟨eA', heA'⟩ := localization_model_transport (x ≫ f)
    (𝟙 (Spec (.of Ω)) ≫ 𝟙 (Spec (.of Ω)) ≫ (x ≫ f)) (by simp) eA
  obtain ⟨eB', heB'⟩ := localization_model_transport x
    (𝟙 (Spec (.of Ω)) ≫ x) (by simp) eB
  have hA' : eA'.hom ≫ Scheme.strictLocalizationToBase
      (𝟙 (Spec (.of Ω)) ≫ 𝟙 (Spec (.of Ω)) ≫ (x ≫ f)) = jA := heA'.trans heA
  have hB' : eB'.hom ≫ Scheme.strictLocalizationToBase
      (𝟙 (Spec (.of Ω)) ≫ x) = jB := heB'.trans heB
  obtain ⟨c₁, c₂, hc⟩ := exists_addEquiv_strictHenselization_abelian_stalkExchange
    (A := Scheme.strictHenselizationRing (x ≫ f))
    (B := Scheme.strictHenselizationRing x)
    (IsPullback.of_hasPullback f g).flip (x ≫ f) x (𝟙 _) (by simp) (𝟙 _)
    eA' eB' a.hom ρA ρB
    (by simpa only [Category.assoc, hA', reassoc_of% hB', jA, jB] using! ha)
    (by rw [hA']; simpa only [heA] using hρA)
    (by rw [hB']; simpa only [heB] using hρB)
    hρ p₀ f₀ (by rw [hA']; simpa only [heA] using sq₀) p₁ f₁ sq₁ F q
  obtain ⟨b₁, b₂, hb⟩ := exists_addEquiv_strictLocal_abelian_total_exchange
    a.hom f₀ f₁ p₁ sq₁ ((upperStar AddCommGrpCat.{u + 1} p₀).obj F) q
  rw [ConcreteCategory.isIso_iff_bijective]
  apply bijective_conjugate _ _ (c₁.trans b₁).toEquiv (c₂.trans b₂).toEquiv
  intro z
  change b₂ (c₂ _) = cohomologyMap p₁ _ q (b₁ (c₁ z))
  rw [hc]
  exact hb (c₁ z)

end AlgebraicGeometry.Etale
