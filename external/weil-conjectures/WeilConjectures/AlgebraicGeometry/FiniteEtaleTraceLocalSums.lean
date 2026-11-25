/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: def-weil-pbc-finite-etale-trace-local-sums)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A trace has the local sum characterization if, on every object `W` whose pullback
of `Y` is a finite clopen coproduct of copies of `W`, its transported component is the
sum of restrictions along the sections. The index type may be empty.
Source: Stacks Project, Section 03SH, after Definition 03SE; SGA 4, Exposé IX, 5.1.
(blueprint: def-weil-pbc-finite-etale-trace-local-sums)

This is the local characterization used in the descent construction, not a choice of
trace: it is a predicate on an already given sheaf morphism. -/
def FiniteEtaleTraceLocalSums {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Etale f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (τ : (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⟶ F) : Prop :=
  let A := AddCommGrpCat.{u + 1}
  let B := fun (W : X.Etale) ↦ (MorphismProperty.Over.map ⊤ hf).obj
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
  ∀ (W : X.Etale) (J : Type u) [Fintype J]
    (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ pullback W.hom f)
    (t : ∀ j, W.left ⟶ V j) (_ : IsColimit (Cofan.mk (pullback W.hom f) i))
    (hinv₁ : ∀ j, t j ≫ i j ≫ pullback.fst W.hom f = 𝟙 W.left)
    (_ : ∀ j, i j ≫ pullback.fst W.hom f ≫ t j = 𝟙 (V j))
    (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j)),
    (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
        τ.hom.app (op W) = ∑ j, F.obj.map (MorphismProperty.Over.homMk
          (A := W) (B := B W) (t j ≫ i j)
          (by
            change (t j ≫ i j) ≫ pullback.snd W.hom f ≫ f = W.hom
            rw [← pullback.condition]
            simpa [← Category.assoc] using
              congrArg (fun k ↦ k ≫ W.hom) (hinv₁ j))).op

end AlgebraicGeometry.Etale
