/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
/-! # Free abelian sheaves for a two-open cover

Source: Stacks Project, Tag 01EB.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- The free abelian sheaf represented by an open. -/
noncomputable def H.openFreeSheaf {X : Scheme.{u}} (W : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj W ⋙ AddCommGrpCat.free)

/-- The map of free abelian sheaves induced by inclusion. -/
noncomputable def H.openFreeSheafMap {X : Scheme.{u}} {W Z : X.Opens} (h : W ≤ Z) :
    H.openFreeSheaf W ⟶ H.openFreeSheaf Z :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map (homOfLE h)) AddCommGrpCat.free)

private lemma openFreeSheafMap_comp {X : Scheme.{u}} {W Z T : X.Opens}
    (h : W ≤ Z) (k : Z ≤ T) :
    H.openFreeSheafMap h ≫ H.openFreeSheafMap k = H.openFreeSheafMap (h.trans k) := by
  unfold H.openFreeSheafMap
  rw [← Functor.map_comp, ← Functor.whiskerRight_comp, ← Functor.map_comp]
  rfl

/-- The actual free-sheaf Mayer--Vietoris short complex, with its difference sign. -/
noncomputable def H.openFreeShortComplex {X : Scheme.{u}} (U V : X.Opens) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (biprod.lift (H.openFreeSheafMap inf_le_left) (-H.openFreeSheafMap inf_le_right))
    (biprod.desc (H.openFreeSheafMap (le_top : U ≤ ⊤))
      (H.openFreeSheafMap (le_top : V ≤ ⊤))) (by
        rw [biprod.lift_desc, Preadditive.neg_comp, openFreeSheafMap_comp,
          openFreeSheafMap_comp]
        exact add_neg_cancel _)

private def openSquare {X : Scheme.{u}} (U V : X.Opens) : Square X.Opens where
  X₁ := U ⊓ V
  X₂ := U
  X₃ := V
  X₄ := ⊤
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_top
  f₃₄ := homOfLE le_top
  fac := Subsingleton.elim _ _

private lemma openSquare_cover {X : Scheme.{u}} (U V : X.Opens) (hc : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (openSquare U V).f₂₄ (openSquare U V).f₃₄ ∈
      Opens.grothendieckTopology X (openSquare U V).X₄ := by
  intro x hx
  have h : x ∈ U ∨ x ∈ V := by
    change x ∈ U ⊔ V
    rw [hc]
    exact hx
  rcases h with h | h
  · refine ⟨U, homOfLE le_top, ?_, h⟩
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk WalkingPair.left)
  · refine ⟨V, homOfLE le_top, ?_, h⟩
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk WalkingPair.right)

/-- The free-sheaf two-open complex is short exact for a cover.
Source: Stacks Project, Tag 01EB; Mathlib's MayerVietorisSquare.shortComplex_shortExact.
(blueprint: lem-pc-free-mayer-vietoris-short-exact) -/
theorem H.openFreeShortComplex_shortExact {X : Scheme.{u}} (U V : X.Opens)
    (hc : U ⊔ V = ⊤) : (H.openFreeShortComplex U V).ShortExact := by
  have hs : (openSquare U V).IsPullback := by
    apply Square.IsPullback.mk
    apply PullbackCone.IsLimit.mk _
      (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    all_goals intros; apply Subsingleton.elim
  let sq := GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := Opens.grothendieckTopology X) (openSquare U V) hs
    (openSquare_cover U V hc)
  exact sq.shortComplex_shortExact

end AlgebraicGeometry.Scheme.Modules
