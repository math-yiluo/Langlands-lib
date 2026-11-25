/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Detection of filtered colimits on the affine etale basis

Source: Stacks Project, Tag 09Z1 and Tag 03Q8.
(blueprint: sbc-lem-small-etale-affine-colimit-detection).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Affine etale evaluation detects a colimit cocone of module sheaves.
Source: Stacks Project, Tag 09Z1, final affine-basis sheafification step, and
Sites, comparison lemma for a dense subsite (Tag 03A0).
(blueprint: sbc-lem-small-etale-affine-colimit-detection).

Proof: Restrict the cocone to the dense affine etale site. For each affine etale
object, the hypothesis says that its evaluation is a colimit. Evaluation jointly
reflects colimits of presheaves, so the restricted presheaf cocone is a colimit.
The fully faithful inclusion of sheaves into presheaves reflects colimits, and the
restriction to the dense affine etale site is an equivalence of sheaf categories.
Reflecting successively through these two functors gives the desired universal
property. This works for every indexing category; no filteredness is needed.
The empty affine scheme causes no issue: its sections form the zero module. -/
theorem nonempty_isColimit_of_affine_etale
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u})
    {J : Type u} [Category.{u} J]
    (K : J ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Cocone K)
    (h : ∀ (V : S.Etale) [IsAffine V.left], Nonempty (IsColimit
      ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation S.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op V)).mapCocone B))) :
    Nonempty (IsColimit B) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let R := (Scheme.AffineEtale.Spec S).sheafPushforwardContinuous
    (ModuleCat.{u + 1} Λ) (Scheme.AffineEtale.topology S) S.smallEtaleTopology
  have : R.IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} (Scheme.AffineEtale.Spec S)
      (Scheme.AffineEtale.topology S) S.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let U := sheafToPresheaf (Scheme.AffineEtale.topology S) (ModuleCat.{u + 1} Λ)
  refine ⟨isColimitOfReflects R (isColimitOfReflects U ?_)⟩
  apply evaluationJointlyReflectsColimits
  intro V
  have : IsAffine ((Scheme.AffineEtale.Spec S).obj V.unop).left := by
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  exact (h ((Scheme.AffineEtale.Spec S).obj V.unop)).some

end AlgebraicGeometry.Etale
