/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Affine quasi-coherent acyclicity with lifted coefficients

Source: Stacks Project, Tag 03P2, affine case
(blueprint: lemma-p-torsion-affine-curve-characteristic--4).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Affine acyclicity holds for the universe lift of the associated quasi-coherent sheaf.
Source: Stacks Project, Tag 03P2, affine case, and its Čech proof using Tag 03F9
(blueprint: lemma-p-torsion-affine-curve-characteristic--4).

Proof: Use the affine basis of the small étale site. A covering of an affine admits a
finite affine refinement; its finite disjoint union is a faithfully flat affine cover.
The pullback module is quasi-coherent. On its iterated fibre products the associated
sheaf's Čech complex is the Amitsur complex of the section module, hence is exact in
positive degrees by faithfully flat descent. Applying `ULift` to each group and map
preserves this exactness: a lifted cocycle has an underlying cocycle, choose an
underlying preimage and lift it to obtain the required coboundary. The lifted Čech
complex therefore has zero positive cohomology. The affine basis is stable under
fibre products over an affine object, and finite affine covers refine every cover.
The Čech vanishing criterion now gives vanishing of sheaf cohomology at the terminal
affine object in every positive degree. This is the same proof as
`etale_affine_qcoherent`, with coefficients in the larger universe; no assertion
that universe lift preserves injective objects is required. -/
theorem etale_affine_qcoherent_ulift (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf F)) q) := by
  classical
  let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (Scheme.Modules.etaleTensorSectionsSheaf F)
  obtain ⟨hB, hcofinal⟩ := Scheme.finiteAffineEtaleCechCover_basis X
  have hvan := Scheme.isZero_rightDerived_etale_of_cech_vanishing X
    {U | IsAffine U.left} (Scheme.finiteAffineEtaleCechCover X) G
    (fun _ _ _ _ hf ↦ hf.2.2.2) hB hcofinal
    (fun U I V f hf p hp ↦
      Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech X F U I V f hf p hp)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hT : CategoryTheory.Limits.IsTerminal T := by
    exact CategoryTheory.MorphismProperty.Over.mkIdTerminal _ _
  have hz := hvan T (by change IsAffine X; infer_instance) (n + 1) (Nat.zero_lt_succ n)
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT G n
  let := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  exact Function.Injective.subsingleton e.injective

end AlgebraicGeometry.Etale
