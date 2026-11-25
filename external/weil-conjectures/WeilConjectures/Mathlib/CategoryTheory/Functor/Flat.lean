/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.Flat

/-!
# Left exactness of left Kan extension along a flat functor, without smallness

`CategoryTheory.Functor.lanEvaluationIsoColim` in Mathlib identifies the evaluation of the
left Kan extension functor `F.lan` at `X` with the colimit over the comma category
`CostructuredArrow F X`, but only for small categories. This file provides the same
isomorphism assuming only that the pointwise left Kan extensions along `F` exist and that
the colimits of shape `CostructuredArrow F X` exist in the target
(`CategoryTheory.Functor.lanEvaluationIsoColim'`).

The consequence we are after is `CategoryTheory.preservesFiniteLimits_op_lan_of_flat`: left
Kan extension along the opposite of a representably flat functor is left exact as soon as
the pointwise left Kan extensions exist and filtered colimits of the relevant size are exact
in the target. This is the variant of `CategoryTheory.lan_preservesFiniteLimits_of_flat`
that replaces smallness of the categories and concreteness of the target by AB5 at the
relevant size.

`lanEvaluationIsoColim'` is taken verbatim from the `proetale` dependency
(`Proetale.Topology.Comparison.CohomologyComparison`), which is not otherwise imported here;
the import direction would be the wrong way round and that file is heavy.

The comma categories `CostructuredArrow L X` of a representably coflat functor `L` are
filtered, hence sifted (`CategoryTheory.Functor.isSifted_costructuredArrow`). This is what
makes left Kan extension along `L` strong monoidal (`CategoryTheory.Functor.isIso_lan_δ`).

TODO: upstream `lanEvaluationIsoColim'` to `Mathlib/CategoryTheory/Functor/Flat.lean`,
deriving Mathlib's `lanEvaluationIsoColim` from it (and renaming: the prime is only kept
here to match the copy in `proetale`), then drop this copy and the one in `proetale`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved: the evaluation of `F.lan` at `X` is the colimit
over the costructured arrows over `X`.

```
                            F.lan
       (C ⥤ H) ───────────────────────────────▶ (D ⥤ H)
          │                                        │
  whisker │                                        │ evaluation at `X`
  by proj │                                        │
          ▼                                        ▼
(CostructuredArrow F X ⥤ H) ────────colim────────▶ H
```

Here `whisker by proj` is restriction along `CostructuredArrow.proj F X`.
-/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (X : D)
    [∀ G : C ⥤ H, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F X) H] :
    F.lan ⋙ (evaluation D H).obj X ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ H) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- The comma categories `CostructuredArrow L X` of a representably coflat functor `L` are
sifted, being filtered. -/
instance isSifted_costructuredArrow (L : C ⥤ D) [RepresentablyCoflat L] (X : D) :
    IsSifted (CostructuredArrow L X) :=
  IsFiltered.isSifted

end Functor

/-- Left Kan extension along the opposite of a representably flat functor `F` is left
exact, provided the pointwise left Kan extensions along `F.op` exist and filtered colimits
of shape the comma categories `CostructuredArrow F.op K` are exact in the target.

This is the variant of `CategoryTheory.lan_preservesFiniteLimits_of_flat` that assumes AB5
at the relevant size instead of smallness of `C` and `D` and concreteness of `H`. -/
instance preservesFiniteLimits_op_lan_of_flat (F : C ⥤ D) [RepresentablyFlat F]
    [∀ G : Cᵒᵖ ⥤ H, F.op.HasPointwiseLeftKanExtension G]
    [HasFiniteLimits H] [HasFilteredColimitsOfSize.{v₁, max u₁ v₂} H]
    [AB5OfSize.{v₁, max u₁ v₂} H] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)) := by
  constructor
  intro J _ _
  refine preservesLimitsOfShape_of_evaluation _ _ fun K ↦ ?_
  -- flatness of `F` makes `StructuredArrow (unop K) F` cofiltered, hence
  -- `CostructuredArrow F.op K` filtered, and the Kan extension is pointwise a filtered
  -- colimit, which is exact by AB5
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (Functor.lanEvaluationIsoColim' F.op K).symm

end CategoryTheory

namespace CategoryTheory

open Limits

/-- **Presheaf pullback of presheaves of sets.** For a functor `b : C ⥤ D` between small
categories, the left Kan extension `b.op.lan` along `bᵒᵖ` (the presheaf pullback
`b_p F (Y) = colim_{(X, Y ⟶ b X)} F X`) is left adjoint to precomposition with `bᵒᵖ`; if moreover
`C` has finite limits and `b` preserves them, then `b.op.lan` preserves finite limits.
(blueprint: `situation-conventions`) -/
theorem nonempty_lan_adjunction_and_preservesFiniteLimits {C D : Type u₁} [SmallCategory C]
    [SmallCategory D] (b : C ⥤ D) :
    Nonempty (b.op.lan ⊣ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u₁)).obj b.op) ∧
      ∀ [HasFiniteLimits C] [PreservesFiniteLimits b],
        PreservesFiniteLimits (b.op.lan : (Cᵒᵖ ⥤ Type u₁) ⥤ _) :=
  ⟨⟨b.op.lanAdjunction _⟩, by intros; infer_instance⟩


end CategoryTheory
