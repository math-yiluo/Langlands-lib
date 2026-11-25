/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

/-!
# Exact inverse image of set-valued small etale sheaves

Source: Stacks Project, Lemma 59.36.2 (Tag 03Q1), assertion (2), and Definition
59.36.1 (Tag 03PZ); Sites, Definition 00X1
(blueprint: lem-weil-pbc-sets-etale-inverse-image-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Lemma 03Q1(2), Definition 59.36.1 in Section 03PZ,
and Sites, Definition 00X1 (blueprint: lem-weil-pbc-sets-etale-inverse-image-exact).

The inverse image is Mathlib's left Kan extension followed by sheafification,
exactly the construction used by `Scheme.etaleSetPullback`. The direct image is
precomposition with base change, hence its sections over `V` are `F(V ×_T T')`.
Continuity and the two preservation properties are the morphism-of-sites condition
of def-weil-pbc-sites-and-cohomology(3); no separate site-morphism structure is needed.

Proof:
1. Base change sends etale coverings to coverings and preserves the relevant
   fibre products. By situation-conventions its sectionwise
   direct image is a sheaf and its base-change functor is continuous.
2. The sheafified presheaf inverse image is left adjoint to this direct image and
   preserves finite limits by situation-conventions(1).
   This includes the terminal sheaf and binary products.
3. By situation-conventions the left adjoint preserves all
   small colimits, in particular finite colimits.
4. Steps 1--3 give a continuous base-change functor with exact inverse image,
   which is a morphism of sites by def-weil-pbc-sites-and-cohomology(3), Tag 00X1. -/
theorem etaleSetInverseImage_exact {T T' : Scheme.{u}} (h : T' ⟶ T) :
    (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale) ∧
    Nonempty
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale) ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
        (Type (u + 1)) (T.smallGrothendieckTopology @Etale)
        (T'.smallGrothendieckTopology @Etale)) ∧
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)) ∧
    PreservesFiniteColimits
      (Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
        (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)) := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
    (T.smallGrothendieckTopology @Etale) (T'.smallGrothendieckTopology @Etale)
  have := a.isLeftAdjoint
  refine ⟨inferInstance, ⟨a⟩, ?_, inferInstance⟩
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
  infer_instance

end AlgebraicGeometry
