/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion

/-!
# Canonical comparisons for ordinary etale compact support

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, and Stacks Project,
Tags 0F7I, 0F7J, 0F7K (blueprint: proposition-construction-independence-rf-shriek--7).

The existing bounded-below API supplies the natural isomorphisms and their coherence:
* `rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, with its `_id` and `_comp`;
* `rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`, `_refl`, `_trans`;
* `rightDerivedLowerShriekPlusCompIso`, its `_hom_eq`, and its `_assoc`.
These are used for `ModuleCat.{u + 1} Λ`, with finite commutative `Λ`.
`IsNoetherian` is exactly the finite affine Noetherian-cover condition, by Mathlib's
`isNoetherian_iff_of_finite_affine_openCover`.

The statement below identifies the refinement isomorphism with precisely the specified
proper/open alpha map, after applying the ambient pushforward and its canonical composition
identification. Together with the existing declarations recorded on this node, it supplies
all the clauses, without introducing a second comparison or composition construction.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical refinement comparison is the ambient proper pushforward of the specified
proper/open comparison, followed by the canonical direct-image composition identification.
No Cartesian-square or density assumption is placed on the refinement.

Source: Stacks Project, Tags 0F7I, 0F7J, 0F7K, and the blueprint
(blueprint: proposition-construction-independence-rf-shriek--7).

Proof plan for the full comparison and composition package:
1. A finite affine Noetherian cover gives local Noetherianity and quasi-compactness;
   local Noetherianity gives quasi-separatedness. Proper compactification ambients are
   Noetherian, and their source opens are quasi-compact. Apply proper/open comparison
   invertibility and transitivity. The adjoint of the specified restriction identification
   is alpha; identify its ambient pushforward with the canonical refinement comparison.
   For two common refinements, refine both and successively equalize their arrows to the
   two original compactifications (remark-base-change-compactification--1). Transitivity
   cancels the invertible refinement factors, proving independence and the cocycle law.
2. Choose a compactification of g and apply
   lem-weil-pbc-compatible-compactification-triangle to compactify f over its open part.
   The resulting candidates for f and fg are the actual Rp_* Dj_! constructions.
3. Apply lem-weil-pbc-etale-open-proper-interchange, compose extensions by zero using
   proposition-composition-base-change-rf-shriek--1, and compose proper derived direct images using
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition. On bounded-below injective
   representatives this last comparison is the underived direct-image identification,
   so its unit and associativity laws hold and the lower bound is preserved.
4. The compatible tower of lem-cbc-compactifiable-compatible-tower dominates any two
   triangles. Horizontal and vertical pasting in
   lem-cbc-proper-open-interchange-coherence, together with naturality, identify their
   model composition maps after conjugating by the three refinement comparisons.
   The independent cocycles from step 1 cancel these comparisons.
5. For three morphisms use successive compatible compactifications. In the three adjacent
   Cartesian squares, the two routes use horizontal and vertical pasting of the same
   exchange maps. Naturality commutes the middle transformations. Associativity of proper
   direct images and of open extension identifies their targets, giving the same map.
   Conjugate back by the independent comparisons to obtain associativity for all choices.
The existing coherence and composition declarations in this module implement steps 1--5;
this equation fixes their normalization to proposition-construction-independence-rf-shriek--7. -/
theorem etaleCompactSupport_refinementComparison_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlusRefinementIso Λ r).hom.app K =
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
        (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
      ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pfComp'
        r.hom d.g c.g r.hom_g).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K) := by
  have sq : IsPullback (𝟙 X) f f (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := (compactSupportFiniteTorsion Λ sq c).2 d r K
  simp only [compactSupportProperOpenRefinementMap] at h
  rw [derivedPlusFormalism_shriekIso] at h
  rw [rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq,
    rightDerivedLowerShriekOfCompactificationPlusIso_symm,
    derivedPlusFormalism_pfComp'_inv]
  exact h.symm

end AlgebraicGeometry.Etale
