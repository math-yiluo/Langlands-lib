/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Existence of the transition transformations and their adjunct equations.
Source: Stacks Project, Sites, Tag 0A35, adjunction paragraph.
(blueprint: lem-weil-pbc-stage-section-transition-existence).

Proof: Write S_t for inverse image, R_t for restriction, and R_b for restriction
along F(b.right). The under-category equation and F.map_comp give the equality
f_t followed by F(b.right) = f_t'. Precomposition therefore identifies R_b
followed by R_t with R_t'; use the isomorphism induced by this equality.
Compose the unit at t' with the inverse of this restriction isomorphism,
whiskered by S_t'. This is a natural transformation from the identity to
S_t' followed by R_b and R_t. Transpose it through S_t adjoint to R_t in the
functor category, obtaining theta_b : S_t to S_t' followed by R_b. The hom-set
bijection proves its unit equation, and working in the functor category gives
naturality in G automatically. Evaluate at X. The restriction isomorphism is
an equality transport; its evaluation is the corresponding transport in sets.
Composing a map with an equality transport preserves its Arrow object, by
eliminating the equality. This yields exactly the displayed Arrow equation.
-/
theorem stage_section_transition_existence
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (i : J) :
    ∃ (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⟶
        sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck ⋙
          (F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
            (P t.right).toGrothendieck (P t'.right).toGrothendieck),
      ∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
        Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
            (op X) ≫ ((θ t t' b).app G).hom.app
              (op ((F.map t.hom).toFunctor.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app
            (op X)) := by
  let A := Sheaf (P i).toGrothendieck (Type u)
  let L := fun t : Under i => sheafPullback (F.map t.hom).toFunctor (Type u)
    (P i).toGrothendieck (P t.right).toGrothendieck
  let Rb := fun (t t' : Under i) (b : t ⟶ t') =>
    (F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
      (P t.right).toGrothendieck (P t'.right).toGrothendieck
  let adj := fun t : Under i => sheafAdjunctionContinuous (F.map t.hom).toFunctor
    (Type u) (P i).toGrothendieck (P t.right).toGrothendieck
  have hf : ∀ (t t' : Under i) (b : t ⟶ t'),
      (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map t'.hom).toFunctor := by
    intro t t' b
    change (F.map t.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  let e := fun (t t' : Under i) (b : t ⟶ t') =>
    Functor.sheafPushforwardContinuousComp' (eqToIso (hf t t' b)) (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck (P t'.right).toGrothendieck
  let a := fun (t t' : Under i) (b : t ⟶ t') =>
    (adj t').unit ≫ Functor.whiskerLeft (L t') (e t t' b).inv
  let θ := fun (t t' : Under i) (b : t ⟶ t') =>
    ((adj t).whiskerRight A).homEquiv (𝟭 A) (L t' ⋙ Rb t t' b) |>.symm (a t t' b)
  refine ⟨θ, ?_⟩
  intro G t t' b X
  have h := (((adj t).whiskerRight A).homEquiv (𝟭 A) (L t' ⋙ Rb t t' b)).apply_symm_apply
    (a t t' b)
  rw [Adjunction.homEquiv_unit] at h
  have hX := congrArg (fun α => (α.app G).hom.app (op X)) h
  dsimp [a] at hX
  simp only [Adjunction.whiskerRight_unit_app_app] at hX
  change ((adj t).unit.app G).hom.app (op X) ≫
    ((θ t t' b).app G).hom.app (op ((F.map t.hom).toFunctor.obj X)) =
    ((adj t').unit.app G).hom.app (op X) ≫
      ((e t t' b).inv.app ((L t').obj G)).hom.app (op X) at hX
  change Arrow.mk (((adj t).unit.app G).hom.app (op X) ≫
    ((θ t t' b).app G).hom.app (op ((F.map t.hom).toFunctor.obj X))) = _
  rw [hX]
  simp only [e, Functor.sheafPushforwardContinuousComp'_inv_app_hom_app]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_op, eqToHom_map]
  exact Arrow.arrow_mk_comp_eqToHom _ _

end CategoryTheory
