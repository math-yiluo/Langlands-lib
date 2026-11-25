/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer

/-!
# Corepresentability from covering sheaf generators

This is the representability part of the covering-generator criterion.  It is
the intermediate step used to construct the left adjoint in the main theorem.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Covering corepresentability makes every sheaf lie in the domain of the
partial left adjoint.  The proof combines the covering representable
coequalizer presentation with stability of corepresentability under coproducts
and coequalizers.

Source: Stacks Project, Sites, Tag 09YX, together with Tag 00WS.
(auxiliary; not a blueprint node)
-/
theorem leftAdjointObjIsDefined_of_covering_corepresentable_evaluations
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (K : Precoverage D) [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (R : Sheaf J.toGrothendieck (Type (max u v w)) ⥤
      Sheaf K.toGrothendieck (Type (max u v w)))
    (E : Set D)
    (hcover : ∀ V : D, ∃ S : Presieve V, S ∈ K V ∧
      ∀ (W : D) (g : W ⟶ V), S g → W ∈ E)
    (hrep : ∀ V ∈ E, ∃ G : Sheaf J.toGrothendieck (Type (max u v w)),
      Nonempty (coyoneda.obj (op G) ≅
        R ⋙ (sheafSections K.toGrothendieck (Type (max u v w))).obj (op V))) :
    ∀ H : Sheaf K.toGrothendieck (Type (max u v w)),
      R.leftAdjointObjIsDefined H := by
  classical
  have hgen (V : E) : R.leftAdjointObjIsDefined
      ((presheafToSheaf K.toGrothendieck (Type (max u v w))).obj
        (uliftYoneda.{max u w}.obj V.val)) := by
    obtain ⟨G, ⟨e⟩⟩ := hrep V.val V.property
    let adj := sheafificationAdjunction K.toGrothendieck (Type (max u v w))
    refine Functor.CorepresentableBy.isCorepresentable (X := G) ?_
    refine
      { homEquiv := fun {F} ↦ (e.app F).toEquiv.trans
          (uliftYonedaEquiv.{max u w}.symm.trans
            (adj.homEquiv (uliftYoneda.{max u w}.obj V.val) (R.obj F)).symm)
        homEquiv_comp := ?_ }
    intro F F' g f
    dsimp
    apply (adj.homEquiv (uliftYoneda.{max u w}.obj V.val) (R.obj F')).injective
    have ht := (adj.homEquiv (uliftYoneda.{max u w}.obj V.val)
      (R.obj F')).apply_symm_apply (uliftYonedaEquiv.{max u w}.symm (e.hom.app F' (f ≫ g)))
    refine ht.trans ?_
    rw [Adjunction.homEquiv_naturality_right]
    refine Eq.trans ?_ (congrArg
      (fun a ↦ a ≫ (sheafToPresheaf K.toGrothendieck (Type (max u v w))).map (R.map g))
      ((adj.homEquiv (uliftYoneda.{max u w}.obj V.val) (R.obj F)).apply_symm_apply
        (uliftYonedaEquiv.{max u w}.symm (e.hom.app F f)))).symm
    apply uliftYonedaEquiv.{max u w}.injective
    rw [uliftYonedaEquiv_comp]
    refine (uliftYonedaEquiv.{max u w}.apply_symm_apply _).trans ?_
    refine (e.hom.naturality_apply g f).trans ?_
    exact congrArg ((R.map g).hom.app (op V.val))
      (uliftYonedaEquiv.{max u w}.apply_symm_apply _).symm
  have hE : ∀ V : D, ∃ S : Precoverage.ZeroHypercover.{max u v w} K V,
      ∀ i : S.I₀, S.X i ∈ E := by
    intro V
    obtain ⟨S, hS, hSE⟩ := hcover V
    let T := S.preZeroHypercover.reindex
      (Equiv.ulift : ULift.{max u w} S.preZeroHypercover.I₀ ≃ _)
    refine ⟨⟨T, ?_⟩, ?_⟩
    · simpa only [T, PreZeroHypercover.presieve₀_reindex,
        Presieve.presieve₀_preZeroHypercover] using hS
    · intro i
      exact hSE _ _ i.down.property
  intro H
  obtain ⟨I₀, I₁, V₀, V₁, P₀, P₁, ι₀, ι₁, ⟨hP₀⟩, ⟨hP₁⟩,
    d₀, d₁, q, hq, ⟨hc⟩⟩ := exists_coveringRepresentable_coequalizer.{v, max u w} K E hE H
  have h₀ : R.leftAdjointObjIsDefined P₀ :=
    Functor.leftAdjointObjIsDefined_of_isColimit hP₀ (fun i ↦ hgen (V₀ i.as))
  have h₁ : R.leftAdjointObjIsDefined P₁ :=
    Functor.leftAdjointObjIsDefined_of_isColimit hP₁ (fun i ↦ hgen (V₁ i.as))
  exact Functor.leftAdjointObjIsDefined_of_isColimit hc (fun j ↦ by
    cases j
    · exact h₁
    · exact h₀)

end CategoryTheory
