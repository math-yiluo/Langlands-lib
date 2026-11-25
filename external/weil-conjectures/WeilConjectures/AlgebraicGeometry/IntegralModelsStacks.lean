/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelCriterion
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBasic
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.SixFunctors.ProEtale.InternalResidueStacksComparison

/-! # Integral models and Stacks adic constructibility

This file proves `lemma-integral-models--2` along the blueprint route: restriction of
scalars along the map from the constant coefficient ring, the integral constructibility
criterion `proposition-integral-constructibility-criterion`, part (2) of
`lemma-integral-models--1` and the pro-étale/étale comparison of
constructible complexes. The criterion is stated in the internal presentation over
`DerivedNakayama.integerRing` (`internal_integral_criterion_forward`,
`internal_integral_criterion_reverse`), where completeness is the Roos condition
`IsDerivedComplete` and the residue is `AdicCompletion.derivedReduction`.

Here `Dᵇc(X, 𝒪_E)` is `constantModelBoundedConstructible`, the finite-constant-model form of
`definition-constructible-sheaves`. For this form the reverse implication of the criterion needs the
local structure theorem `proposition-local-structure-integral-constructible-complexes`; it is
supplied by the adic stratified perfect models through `integral_models_stacks_criterion`.

## Main statements

* `internal_integral_criterion_forward`, `internal_integral_criterion_reverse`: the two
  directions of `proposition-integral-constructibility-criterion`.
* `integral_models_stacks`: `K ∈ Dᵇc(X, 𝒪_E)` iff `Res K` is Stacks adic constructible
  (`integral_models_stacks_criterion`), and `Res` restricts to an equivalence of the two full
  subcategories.

Source: blueprint lemma-integral-models--2; Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Local derived completeness for the first residue map, transported to the small site:
the completeness clause of `stacksConstructible`.
Source: Stacks Tag 09C1 (auxiliary; not a blueprint node). -/
def stacksComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
    (smallDerivedObject X _ L)

/-- The complexes over the continuous integers whose restriction to the constant integers is
complete in the sense of `stacksComplete`.
Source: blueprint lemma-integral-models--2
(auxiliary; not a blueprint node). -/
def restrictionComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :=
  fun K ↦ stacksComplete l E X ((restriction l E X).obj K)

/-- Transport along `IntegralConstantModel.pointComparison` from the internal presentation
over `DerivedNakayama.integerRing` to the continuous integers `integersObj` preserves and
reflects bounded constant-model constructibility.
Source: blueprint lemma-integral-models--2 (auxiliary; not a blueprint node).

Proof: restriction of scalars along an isomorphism of coefficient rings is an exact
equivalence, so it preserves and reflects boundedness, commutes with cohomology, and
`constantModel_comap_iff` transports the finite constant models. -/
theorem constantModelBoundedConstructible_pointComparison_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
      constantModelBoundedConstructible (integersObj l E) X
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
          ).mapDerivedCategory.obj K) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  have hF : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  apply and_congr
  · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
  · apply forall_congr'
    intro q
    have h := constantModel_comap_iff (IntegralConstantModel.pointComparison l E).inv.hom
      X ((DerivedCategory.homologyFunctor _ q).obj K)
    have hi' := (constantModelConstructibleFiniteTor_wellDefined (integersObj l E) X).1
    let := hi'
    exact h.symm.trans
      ⟨fun h ↦ ObjectProperty.prop_of_iso _
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K) h,
      fun h ↦ ObjectProperty.prop_of_iso _
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm h⟩

/-- Integral constructibility criterion, direction (1) to (2), in the internal presentation:
a bounded constructible complex over the continuous integers is derived complete, and its
first derived reduction is bounded constructible of finite Tor amplitude. This is the
implication (1) ⇒ (2) of `proposition-integral-constructibility-criterion` (Bhatt–Scholze,
Proposition 6.8.11), together with finite Tor amplitude of the reduction over the residue field, as
used in the proof of `lemma-integral-models--2`.
Source: Bhatt–Scholze 6.8.11; Stacks Tag 09C7
(blueprint: proposition-integral-constructibility-criterion).

Proof: transport `K` to the continuous integers
(`constantModelBoundedConstructible_pointComparison_iff`),
apply `integral_models_stacks_criterion`, and read the two clauses of
`stacksConstructible` back by `internal_completion_stacks_comparison` and
`internal_residue_stacks_comparison`. -/
theorem internal_integral_criterion_forward
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K) :
    IsDerivedComplete l E X K ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  have h := (integral_models_stacks_criterion l E X _).mp
    ((constantModelBoundedConstructible_pointComparison_iff l E X K).mp hK)
  exact ⟨(internal_completion_stacks_comparison l E X K).mpr h.1,
    (internal_residue_stacks_comparison l E X K).mp h.2⟩

/-- Integral constructibility criterion, direction (2) to (1), in the internal presentation:
a derived complete complex whose first derived reduction is bounded constructible is bounded
constructible over the continuous integers. This is the implication (2) ⇒ (1) of
`proposition-integral-constructibility-criterion` (Bhatt–Scholze, Proposition 6.8.11); its proof
goes through (3) by `proposition-local-structure-integral-constructible-complexes`.
Source: Bhatt–Scholze 6.8.11; Stacks Tag 09C7
(blueprint: proposition-integral-constructibility-criterion).

Proof: the reduction has finite Tor amplitude, `𝒪_E/ϖ_E` being a field
(`finiteTorAmplitude_of_constantModelBoundedConstructible_residue`).
`internal_completion_stacks_comparison` and `internal_residue_stacks_comparison` then show
that the restriction of the transported complex is Stacks adic constructible; conclude by
`integral_models_stacks_criterion` and `constantModelBoundedConstructible_pointComparison_iff`. -/
theorem internal_integral_criterion_reverse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hc : IsDerivedComplete l E X K)
    (hr : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K)) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K :=
  (constantModelBoundedConstructible_pointComparison_iff l E X K).mpr
    ((integral_models_stacks_criterion l E X _).mpr
      ⟨(internal_completion_stacks_comparison l E X K).mp hc,
        (internal_residue_stacks_comparison l E X K).mpr
          ⟨hr, finiteTorAmplitude_of_constantModelBoundedConstructible_residue l E X hr⟩⟩)

/-- Restriction of scalars along the map from the constant integer ring is an equivalence from
the complexes whose restriction is complete onto the complete complexes, with the inclusion
functors identified with restriction. This is part (2) of
`lemma-integral-models--1` (restriction of scalars is an equivalence
on derived complete objects), transported to the small-site presentation of
`stacksConstructible`; completeness of `K` is read on its restriction as in part (3).
Source: Stacks Tags 0999 and 09C1
(blueprint: lemma-integral-models--1).

Proof: this is `completion_transport`, whose first clause identifies its source property
with `restrictionComplete` and whose target property is `stacksComplete`. -/
theorem restriction_complete_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : (restrictionComplete l E X).FullSubcategory ≌ (stacksComplete l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksComplete l E X).ι ≅
        (restrictionComplete l E X).ι ⋙ restriction l E X) := by
  obtain ⟨h, e, α⟩ := completion_transport l E X
  have hA : (fun K ↦ Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K)) = restrictionComplete l E X :=
    funext fun K ↦ propext (h K)
  exact hA ▸ ⟨e, α⟩

/-- Restriction of scalars identifies the bounded constant-model constructible category
with the Stacks adic constructible category, and reflects membership for every complex.
Source: blueprint lemma-integral-models--2; Stacks Tag 09C1
(blueprint: lemma-integral-models--2).

Proof: the criterion is `integral_models_stacks_criterion`. Restriction is an equivalence
from the complexes with complete restriction onto the complete complexes
(`restriction_complete_equivalence`); bounded constructible complexes have complete
restriction and Stacks adic constructible complexes are complete, so the equivalence
restricts to the selected full subcategories with the same functor. -/
theorem integral_models_stacks (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  have hm := integral_models_stacks_criterion l E X
  refine ⟨hm, ?_⟩
  obtain ⟨e, ⟨α⟩⟩ := restriction_complete_equivalence l E X
  let : (stacksConstructible l E X).IsClosedUnderIsomorphisms :=
    ⟨fun ε h ↦ stacksConstructible_iso l E X ε h⟩
  exact ObjectProperty.exists_equivalence_of_le
    (constantModelBoundedConstructible (integersObj l E) X)
    (restrictionComplete l E X) (stacksConstructible l E X) (stacksComplete l E X)
    (restriction l E X) e α
    (fun K hK ↦ ((hm K).mp hK).1) (fun _ h ↦ h.1) (fun K _ ↦ hm K)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
