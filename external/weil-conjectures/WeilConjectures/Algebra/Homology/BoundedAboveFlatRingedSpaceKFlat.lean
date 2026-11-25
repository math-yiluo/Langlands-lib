/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk

/-!
# Bounded-above flat complexes on a ringed space are K-flat

Source: Stacks Project, Cohomology, Lemma 20.26.9 (Tag 06YD),
label `lemma-bounded-flat-K-flat` (blueprint: lem-pc-bounded-above-flat-kflat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace CochainComplex

/-- Every bounded-above complex of flat module sheaves on a ringed space is K-flat.
Source: Stacks Project, Cohomology, Lemma 20.26.9 (Tag 06YD)
(blueprint: lem-pc-bounded-above-flat-kflat).

Proof:
1. Fix a point `x`. By `lem-pc-flat-sheaf-stalk-flat`, each stalk of each term is
   flat over the stalk ring. The stalk complex remains bounded above because the
   stalk functor sends zero objects to zero objects.
2. Apply `lem-pc-module-bounded-flat-kflat` to this bounded-above complex of flat
   modules over the stalk ring. Its total tensor with every acyclic stalk complex
   is acyclic.
3. Apply the reverse implication of `lem-pc-kflat-stalk-criterion`: K-flatness of
   every stalk complex implies K-flatness of the original sheaf complex. -/
theorem isKFlat_of_boundedAbove_flat_ringedSpace
    (X : RingedSpace.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) : K.IsKFlatTensor := by
  apply (AlgebraicGeometry.RingedSpace.isKFlat_iff_stalk_isKFlat X K).2
  intro x F hF
  let S := (AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((S.obj K).X i) := by
    obtain ⟨b, hb⟩ := hbounded
    refine ⟨b, fun i hi ↦ ?_⟩
    exact (AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x).map_isZero (hb i hi)
  have hf : ∀ i : ℤ, Module.Flat (X.presheaf.stalk x) ((S.obj K).X i) := by
    intro i
    change Module.Flat (X.presheaf.stalk x)
      ((AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x).obj (K.X i))
    exact AlgebraicGeometry.RingedSpace.flat_stalk_of_isFlat X (K.X i) (hflat i) x
  exact CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat (S.obj K) hb hf F hF

end CochainComplex
