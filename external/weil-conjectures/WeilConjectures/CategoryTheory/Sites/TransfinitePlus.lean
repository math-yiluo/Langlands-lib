/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Localization.BousfieldTransfiniteComposition
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.SetTheory.Cardinal.Regular
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Localization
public import WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The transfinite plus construction

Let `J` be a Grothendieck topology on a small category `C` and `κ` a cardinal such that
`κ.ord.ToType` has a least element (e.g. `κ` regular). Iterating the plus construction
`P ↦ P⁺` transfinitely along the well-order `κ.ord.ToType`, taking colimits at limit stages,
gives an endofunctor `J.transfinitePlus A κ` of the category of `A`-valued presheaves,
together with a natural transformation
`J.toTransfinitePlus A κ : 𝟭 _ ⟶ J.transfinitePlus A κ`.

We show that this functor preserves finite limits when `A` has finite limits and filtered
colimits and satisfies axiom AB5 (e.g. `A` is Grothendieck abelian), and that for every
presheaf `P`, the map `P ⟶ P^{(κ)}` is inverted by every sheaf, i.e. lies in `J.W`. That
`P^{(κ)}` is itself a sheaf for large enough `κ` is a separate matter (convergence) not
treated here.

## Main definitions

* `CategoryTheory.GrothendieckTopology.plusSuccStruct`: the successor structure on the
  endofunctors of `Cᵒᵖ ⥤ A` given by composing with the plus construction.
* `CategoryTheory.GrothendieckTopology.transfinitePlus`: the transfinite plus construction.
* `CategoryTheory.GrothendieckTopology.toTransfinitePlus`: the unit `𝟭 _ ⟶ J.transfinitePlus A κ`.
* `CategoryTheory.GrothendieckTopology.transfinitePlusStage`: the stages of the construction.

## Main results

* `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_transfinitePlus`
* `CategoryTheory.GrothendieckTopology.W_toTransfinitePlus_app`

-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [Category.{v} A]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]

/-- The successor structure on the endofunctors of `Cᵒᵖ ⥤ A` whose successor map is
`F ⟶ F ⋙ J.plusFunctor A`, induced by `J.toPlusNatTrans A`, starting at the identity. -/
noncomputable def plusSuccStruct : SmallObject.SuccStruct ((Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)) :=
  SmallObject.SuccStruct.ofNatTrans (J.toPlusNatTrans A)

variable (κ : Cardinal.{v}) [OrderBot κ.ord.ToType]
  [HasIterationOfShape κ.ord.ToType A]

/-- The diagram of the stages of the transfinite plus construction, indexed by
`κ.ord.ToType`. -/
noncomputable def transfinitePlusDiagram : κ.ord.ToType ⥤ (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iterationFunctor κ.ord.ToType

/-- The `j`-th stage `P ↦ P^{(j)}` of the transfinite plus construction. -/
noncomputable abbrev transfinitePlusStage (j : κ.ord.ToType) : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.transfinitePlusDiagram A κ).obj j

/-- The transfinite plus construction `P ↦ P^{(κ)}`: the colimit of the iterates of the plus
construction along `κ.ord.ToType`. -/
noncomputable def transfinitePlus : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iteration κ.ord.ToType

/-- The canonical map `P ⟶ P^{(κ)}` from a presheaf to its transfinite plus construction. -/
noncomputable def toTransfinitePlus : 𝟭 (Cᵒᵖ ⥤ A) ⟶ J.transfinitePlus A κ :=
  (J.plusSuccStruct A).ιIteration κ.ord.ToType

/-- The stage at the least element is the identity functor. -/
noncomputable def transfinitePlusStageBotIso : J.transfinitePlusStage A κ ⊥ ≅ 𝟭 (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iterationFunctorObjBotIso κ.ord.ToType

variable [Fact κ.IsRegular] in
/-- The successor stage is obtained from the previous one by applying the plus construction. -/
noncomputable def transfinitePlusStageSuccIso (j : κ.ord.ToType) :
    J.transfinitePlusStage A κ (Order.succ j) ≅ J.transfinitePlusStage A κ j ⋙ J.plusFunctor A :=
  have := Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le
  (J.plusSuccStruct A).iterationFunctorObjSuccIso j (not_isMax j)

variable [Fact κ.IsRegular] in
/-- The transition map from a stage to the next is given by `J.toPlusNatTrans A`:
```
P^{(j)} ──toPlus──▶ (P^{(j)})⁺
   │                     │
  map              (succIso).inv
   ▼                     ▼
P^{(j+1)} ═══════════ P^{(j+1)}
```
-/
@[reassoc]
lemma transfinitePlusDiagram_map_succ (j : κ.ord.ToType) :
    (J.transfinitePlusDiagram A κ).map (homOfLE (Order.le_succ j)) =
      Functor.whiskerLeft (J.transfinitePlusStage A κ j) (J.toPlusNatTrans A) ≫
        (J.transfinitePlusStageSuccIso A κ j).inv :=
  have := Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le
  (J.plusSuccStruct A).iterationFunctor_map_succ j (not_isMax j)

variable [Fact κ.IsRegular] in
/-- The transition map from a stage to the next, evaluated at a presheaf `P`, is
`J.toPlus` followed by the identification `(P^{(j)})⁺ ≅ P^{(j+1)}`. -/
@[reassoc]
lemma transfinitePlusDiagram_map_succ_app (j : κ.ord.ToType) (P : Cᵒᵖ ⥤ A) :
    ((J.transfinitePlusDiagram A κ).map (homOfLE (Order.le_succ j))).app P =
      J.toPlus ((J.transfinitePlusStage A κ j).obj P) ≫
        (J.transfinitePlusStageSuccIso A κ j).inv.app P :=
  NatTrans.congr_app (J.transfinitePlusDiagram_map_succ A κ j) P

/-- The cocone exhibiting `J.transfinitePlus A κ` as the colimit of its stages. -/
noncomputable def transfinitePlusCocone : Cocone (J.transfinitePlusDiagram A κ) :=
  (J.plusSuccStruct A).iterationCocone κ.ord.ToType

/-- The cocone point of `J.transfinitePlusCocone A κ` is `J.transfinitePlus A κ`. (This is
stated by hand: `@[simps]` would unfold the point to the underlying colimit.) -/
@[simp]
lemma transfinitePlusCocone_pt : (J.transfinitePlusCocone A κ).pt = J.transfinitePlus A κ :=
  rfl

/-- `J.transfinitePlus A κ` is the colimit of its stages. -/
noncomputable def isColimitTransfinitePlusCocone : IsColimit (J.transfinitePlusCocone A κ) :=
  (J.plusSuccStruct A).isColimitIterationCocone κ.ord.ToType

/-- For a presheaf `P`, `(J.transfinitePlus A κ).obj P` is the colimit of the stages
evaluated at `P`. -/
noncomputable def isColimitTransfinitePlusObj (P : Cᵒᵖ ⥤ A) :
    IsColimit (((evaluation _ _).obj P).mapCocone (J.transfinitePlusCocone A κ)) :=
  isColimitOfPreserves _ (J.isColimitTransfinitePlusCocone A κ)

section LeftExact

variable [HasFiniteLimits A] [HasFilteredColimitsOfSize.{v, v} A] [AB5OfSize.{v, v} A]

/-- Every stage of the transfinite plus construction preserves finite limits, provided
`A` has finite limits and filtered colimits and satisfies axiom AB5. -/
instance preservesFiniteLimits_transfinitePlusStage (j : κ.ord.ToType) :
    PreservesFiniteLimits (J.transfinitePlusStage A κ j) :=
  (J.plusSuccStruct A).prop_iterationFunctor_obj κ.ord.ToType
    ObjectProperty.preservesFiniteLimits (inferInstanceAs (PreservesFiniteLimits (𝟭 _)))
    (fun F (_ : PreservesFiniteLimits F) ↦
      inferInstanceAs (PreservesFiniteLimits (F ⋙ J.plusFunctor A)))
    (fun j hj ↦ have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩; inferInstance) j

/-- The transfinite plus construction preserves finite limits, provided `A` has finite
limits and filtered colimits and satisfies axiom AB5 (e.g. `A` is Grothendieck abelian). -/
instance preservesFiniteLimits_transfinitePlus :
    PreservesFiniteLimits (J.transfinitePlus A κ) :=
  (J.plusSuccStruct A).prop_iteration κ.ord.ToType
    ObjectProperty.preservesFiniteLimits (inferInstanceAs (PreservesFiniteLimits (𝟭 _)))
    (fun F (_ : PreservesFiniteLimits F) ↦
      inferInstanceAs (PreservesFiniteLimits (F ⋙ J.plusFunctor A)))
    (fun j hj ↦ have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩; inferInstance)

end LeftExact

/-- The map `P ⟶ P^{(κ)}` is inverted by every sheaf: it is a transfinite composition of the
maps `J.toPlus`, which lie in `J.W`. -/
lemma W_toTransfinitePlus_app (P : Cᵒᵖ ⥤ A) : J.W ((J.toTransfinitePlus A κ).app P) := by
  have h : (J.W.inverseImage ((evaluation _ _).obj P)).TransfiniteCompositionOfShape
      κ.ord.ToType (J.toTransfinitePlus A κ) :=
    ((J.plusSuccStruct A).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE
      (by rintro _ _ _ ⟨F⟩; exact J.W_toPlus _)
  exact J.W.transfiniteCompositionsOfShape_le κ.ord.ToType _ h.map.mem

/-- The natural transformation `𝟭 _ ⟶ J.transfinitePlus A κ` lies in `J.W` objectwise. -/
lemma functorCategory_W_toTransfinitePlus :
    J.W.functorCategory (Cᵒᵖ ⥤ A) (J.toTransfinitePlus A κ) :=
  J.W_toTransfinitePlus_app A κ


end CategoryTheory.GrothendieckTopology
