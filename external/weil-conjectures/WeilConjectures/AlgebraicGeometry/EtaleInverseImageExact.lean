/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Exactness of inverse image on abelian étale sheaves

Source: Stacks Project, Lemma 59.36.2(1) (Tag 03Q1), and Definition 4.23.1 (Tag 0034)
(blueprint: prop-weil-pbc-inverse-image-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Inverse image on abelian sheaves on the small étale site is exact, additive, preserves
kernels and cokernels, and carries short exact sequences to short exact sequences.
Source: Stacks Project, Tag 03Q1(1), with exactness as in Tag 0034
(blueprint: prop-weil-pbc-inverse-image-exact).

Proof:
1. Base change on the étale sites preserves finite limits
   (`situation-conventions`). Presheaf pullback is left adjoint to
   restriction (`lem-weil-pbc-presheaf-pullback-left-exact`), and sheafification is left
   adjoint to inclusion (`def-weil-pbc-sheafification`). The chain of adjunctions identifies
   inverse image (`def-weil-pbc-inverse-image`) with inclusion, presheaf pullback, then
   sheafification, using the restriction formula for `def-weil-pbc-direct-image`.
2. Inverse image preserves colimits as a left adjoint, hence finite colimits and cokernels.
3. The base-change functor preserves finite limits; its presheaf pullback is a filtered
   colimit and preserves finite limits (`lem-weil-pbc-presheaf-pullback-left-exact`).
4. Inclusion and sheafification preserve finite limits
   (`situation-conventions`). Thus their composite with presheaf pullback, and
   the naturally isomorphic inverse image, preserve finite limits, including kernels.
5. Finite products in the abelian categories (`situation-conventions`) are
   biproducts, giving additivity. Preservation of kernels and cokernels carries a short
   exact sequence to a short exact sequence. -/
theorem upperStar_abelian_exact {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
    PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f) ∧
    (upperStar AddCommGrpCat.{u + 1} f).Additive ∧
    (∀ (G H : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : G ⟶ H),
      PreservesLimit (parallelPair φ 0) (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesColimit (parallelPair φ 0) (upperStar AddCommGrpCat.{u + 1} f)) ∧
    (∀ (S : ShortComplex (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})),
      S.ShortExact → (S.map (upperStar AddCommGrpCat.{u + 1} f)).ShortExact) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro G H φ
    exact ⟨inferInstance, inferInstance⟩
  · intro S hS
    exact hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)

end AlgebraicGeometry.Etale
