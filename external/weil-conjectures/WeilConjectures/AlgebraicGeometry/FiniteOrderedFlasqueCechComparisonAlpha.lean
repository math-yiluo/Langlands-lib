/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.FlasqueAlternatingCechRowAugmentation
import all WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation

/-!
# Augmentation comparison for finite ordered Čech complexes

Source: Stacks Project, Cohomology, Tags 09SZ and 01ET.
(auxiliary; not a blueprint node)

Flasque Čech row exactness and the finite-strip row augmentation theorem give
the quasi-isomorphism from global sections into the ordered Čech total complex.
The negative resolution rows vanish by the nonnegative-complex hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- The augmentation map for a finite ordered flasque Čech resolution is a
quasi-isomorphism.
Source: Stacks Project, Cohomology, Tags 09SZ and 01ET.
(auxiliary; not a blueprint node)
Proof: every nonnegative row has the flasque row augmentation quasi-isomorphism.
Every negative row is zero; its coefficient is injective and the existing
injective row lemma applies. Columns outside 0,...,r-1 vanish because there
are no increasing tuples of the required length. Apply finite-strip row
augmentation to these rows and the canonical restriction components.
-/
theorem finiteOrderedFlasqueCechComparison_alpha
    (X : Scheme.{u})
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [G.IsStrictlyGE 0]
    (hfl : ∀ q : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (G.X (q : ℤ))))
    (r : ℕ) (V : Fin r → X.Opens) (hcover : iSup V = ⊤) :
    QuasiIso (alternatingCechAugmentationMap V G) := by
  let K := (alternatingCechDoubleFunctor V).obj G
  let A := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj G
  apply HomologicalComplex₂.quasiIso_of_finite_strip_row_augmentation K r
    (alternatingCechDouble_isZero_column V G) A
    (fun n ↦ alternatingCechZero V (G.X n))
    (alternatingCechAugmentationMap V G) (fun _ ↦ rfl)
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have := hfl q
    exact flasque_alternatingCech_row_augmentation X r V hcover (G.X (q : ℤ))
  · have : Injective (G.X n) := (G.isZero_of_isStrictlyGE 0 n (by omega)).injective
    exact injective_alternatingCech_row_augmentation X r V hcover (G.X n)

end AlgebraicGeometry
