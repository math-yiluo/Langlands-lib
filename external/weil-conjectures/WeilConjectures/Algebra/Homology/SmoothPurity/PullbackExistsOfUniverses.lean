/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Existence of module pullback in a universe containing the sites

Source: Stacks Project, Modules on Sites, Tag 03D7, and Mathlib's free-representable
presentation construction in `ModuleCat.Presheaf.Pullback`.
(blueprint: lem-pur-ringed-site-module-pullback-exists-universes)
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

private noncomputable def freeRep (R : Cᵒᵖ ⥤ RingCat.{max u v w}) (X : C) :
    PresheafOfModules.{max u v w} R :=
  (PresheafOfModules.free R).obj (uliftYoneda.{max u v w}.obj X)

private noncomputable def repEquiv {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    {M : PresheafOfModules.{max u v w} R} {X : C} :
    (freeRep R X ⟶ M) ≃ M.obj (op X) :=
  PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv

private theorem repEquiv_comp {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    {M N : PresheafOfModules.{max u v w} R} {X : C}
    (f : freeRep R X ⟶ M) (g : M ⟶ N) :
    repEquiv (f ≫ g) = g.app _ (repEquiv f) := rfl

private noncomputable def presentationFree {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) : PresheafOfModules.{max u v w} R :=
  ∐ fun x : (Σ X : Cᵒᵖ, M.obj X) ↦ freeRep R x.1.unop

private noncomputable def presentationEpi {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) : presentationFree M ⟶ M :=
  Sigma.desc (fun x ↦ repEquiv.symm x.2)

private theorem presentationEpi_epi {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) : Epi (presentationEpi M) := by
  apply PresheafOfModules.epi_of_surjective
  intro X m
  let ι : freeRep R X.unop ⟶ presentationFree M :=
    Sigma.ι (fun x : (Σ X : Cᵒᵖ, M.obj X) ↦ freeRep R x.1.unop) ⟨X, m⟩
  refine ⟨ι.app X (ModuleCat.freeMk (ULift.up (𝟙 X.unop))), ?_⟩
  have h := congrArg (fun f ↦ repEquiv f)
    (Sigma.ι_comp_desc (fun x : (Σ X : Cᵒᵖ, M.obj X) ↦ repEquiv.symm x.2) ⟨X, m⟩)
  exact h.trans (repEquiv.apply_symm_apply m)

private noncomputable def presentationMap {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) :
    presentationFree (kernel (presentationEpi M)) ⟶ presentationFree M :=
  presentationEpi (kernel (presentationEpi M)) ≫ kernel.ι _

private theorem presentation_condition {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) :
    presentationMap M ≫ presentationEpi M = 0 := by
  simp [presentationMap]

private noncomputable def presentation_isColimit {R : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (M : PresheafOfModules.{max u v w} R) :
    IsColimit (CokernelCofork.ofπ (presentationEpi M) (presentation_condition M)) := by
  have := presentationEpi_epi M
  have := presentationEpi_epi (kernel (presentationEpi M))
  let S := ShortComplex.mk _ _ (presentation_condition M)
  let T := ShortComplex.mk _ _ (kernel.condition (presentationEpi M))
  let φ : S ⟶ T :=
    { τ₁ := presentationEpi _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

private noncomputable def repCorepresentable
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{max u v w}} {S : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (a : S ⟶ F.op ⋙ R) (X : C) :
    (PresheafOfModules.pushforward a ⋙ coyoneda.obj (op (freeRep S X))).CorepresentableBy
      (freeRep R (F.obj X)) where
  homEquiv {M} := (repEquiv (M := M) (X := F.obj X)).trans
    (repEquiv (M := (PresheafOfModules.pushforward a).obj M) (X := X)).symm
  homEquiv_comp g f := by
    apply repEquiv.injective
    dsimp
    erw [Equiv.apply_symm_apply, repEquiv_comp]
    conv_rhs => erw [repEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl

private theorem presheaf_pushforward_isRightAdjoint
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{max u v w}} {S : Cᵒᵖ ⥤ RingCat.{max u v w}}
    (a : S ⟶ F.op ⋙ R) : (PresheafOfModules.pushforward.{max u v w} a).IsRightAdjoint := by
  apply Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply Functor.leftAdjointObjIsDefined_of_isColimit (presentation_isColimit M)
  rintro (_ | _)
  all_goals
    apply Functor.leftAdjointObjIsDefined_colimit
    intro x
    exact (repCorepresentable a _).isCorepresentable

/-- Abelian sheafification exists in any universe in which the site is essentially small.
Source: Mathlib `hasSheafifyEssentiallySmallSite` and
`GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`.
(blueprint: lem-pur-ringed-site-module-pullback-exists-universes). -/
theorem coefficientSheafification {C : Type u} [Category.{v} C]
    [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{w} ∧ J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  have : PreservesFilteredColimitsOfSize.{w, w}
      (CategoryTheory.forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} := inferInstance
  have : HasSheafify J AddCommGrpCat.{w} :=
    hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
      J (A := AddCommGrpCat.{w})
  exact ⟨inferInstance, inferInstance⟩

/-- Module direct image has a left adjoint when the module universe contains the sites.
Source: Stacks Project, Modules on Sites, Tag 03D7,
`lemma-adjoint-pullback-pushforward-modules`; the free-representable presentation
construction of Mathlib `PresheafOfModules.pullbackObjIsDefined_eq_top`.
(blueprint: lem-pur-ringed-site-module-pullback-exists-universes).

Proof: The free module presheaf on the lifted representable at X corepresents
sections at X. Direct image therefore has a left adjoint on this free presheaf,
with value the free presheaf at U(X). Every module presheaf is the quotient of
the coproduct of these free presheaves indexed by its sections. Present its
kernel in the same way to express it as a cokernel between two such coproducts.
The domain of a partial left adjoint is closed under these colimits, which proves
existence on all presheaves. All section and relation indices lie in max u v w.
Abelian sheafification exists in that universe by passage to a small model of
the site. Compose presheaf pullback with sheafification; Mathlib's
`PullbackConstruction.adjunction` identifies its right adjoint with direct image.
No preservation of finite limits or coverings by U is needed for existence. -/
theorem module_pushforward_isRightAdjoint_of_universes
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {U : C ⥤ D} [U.IsContinuous J K]
    {R : Sheaf J RingCat.{max u v w}} {S : Sheaf K RingCat.{max u v w}}
    (a : R ⟶ (U.sheafPushforwardContinuous RingCat J K).obj S) :
    (SheafOfModules.pushforward.{max u v w} a).IsRightAdjoint := by
  obtain ⟨hSheaf, hW⟩ := coefficientSheafification.{u, v, max u v w} K
  let := hSheaf
  let := hW
  have := presheaf_pushforward_isRightAdjoint a.hom
  infer_instance

end SheafOfModules
