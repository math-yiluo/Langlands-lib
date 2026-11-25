/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonCore
import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonNormalization

/-! # Objectwise canonical abelian Čech comparisons

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: lem-pc-abelian-cech-comparison-maps)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
/-- The quotient of beta by alpha exists for one coefficient sheaf, with its
canonical degree-zero value. Naturality in different coefficient sheaves and
compatibility with connecting maps are separate statements.

Source: Stacks Project, Tag 01EQ, proof of Lemma 20.11.2.
(blueprint: lem-pc-abelian-cech-comparison-maps)

Proof: Fix an injective resolution I of F. The supplied hα makes abelianCechAlpha a
quasi-isomorphism on every resolution. In each degree define c as H(beta)
followed by H(alpha) inverse
and the inverse of the canonical Ext-to-section-complex homology identification.
That identification is the constant-sheaf adjunction evaluated on 1, applied
termwise to I, followed by Mathlib's computation of Ext on I. It sends extMk(a)
to the class of the section cycle represented by a; cycles mapping to the same
section coincide because iCycles is monic. For any other injective resolution J,
lift the identity of F to I -> J. Both augmentation squares commute, and the
Ext cocycle computation commutes with the lift. The induced total map is an
isomorphism on homology, since the section map is one and both alpha maps are
quasi-isomorphisms. Cancel it to obtain the defining equation on J. Thus c
satisfies IsAbelianCechComparison for every resolution. In degree zero the two
augmentations send a section to the same restrictions in the (0,0) summand.
Cancel H(alpha) and the resolution identification: c is precisely gluing followed
by the inverse sections-to-H-zero identification. For an empty covering of an
empty space all section complexes are zero; the same argument applies. Finite
diagonals suffice for infinite covers; no finite-cover hypothesis is used. -/
theorem exists_abelianCechComparison_maps
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hα : ∀ I : InjectiveResolution F, QuasiIso (abelianCechAlpha U I)) :
    ∃ c : ∀ q, (TopCat.Sheaf.cechCohomologyFunctor U q).obj F ⟶
      (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F,
      (∀ q, IsAbelianCechComparison U F q (c q)) ∧
      c 0 = (TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv.app F ≫
        (Sheaf.functorHZeroIso (Opens.grothendieckTopology X) isTerminalTop).inv.app F := by
  classical
  have hq := exists_abelianCechComparison_core U F hα
  choose c hc using hq
  refine ⟨c, hc, ?_⟩
  exact abelianCechComparison_zero_normalization U hcover F (c 0) (hc 0)
end AlgebraicGeometry.Scheme.Modules
