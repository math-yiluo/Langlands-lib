/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Relative Tor dimension bounds tensor with a derived pullback

Source: Stacks Project, Tag 08EV, proof, second displayed equality and hypothesis (3);
Cohomology, Lemma 20.27.4.
(blueprint: lem-pc-relative-tor-pullback-tensor-lower-bound)
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- The lower endpoint of relative Tor amplitude bounds tensor with every pulled-back module.
Source: Stacks Project, Tag 08EV, proof, second displayed equality and hypothesis (3);
Cohomology, Lemma 20.27.4.
(blueprint: lem-pc-relative-tor-pullback-tensor-lower-bound)

Proof: Choose the interval [a,b], a representative K of E and its K-flat resolution
P after restriction of scalars to f⁻¹O_S, from HasFiniteTorDimensionOver. Resolve a
module F on S by a bounded-above flat complex L zero above degree zero. Its termwise
pullback is K-flat and represents Lf*(F[0]). Inverse image is exact and takes the flat
terms of L to flat f⁻¹O_S-modules, so f⁻¹L is a K-flat resolution of f⁻¹F.
Associativity of extension of scalars identifies
E tensor^L_O_X Lf*(F[0]) with K|_{f⁻¹O_S} tensor^L_{f⁻¹O_S} f⁻¹F.
The latter is represented by P tensor f⁻¹F[0]. The defining interval makes its
cohomology zero below a. The K-flat derived tensor comparisons and isGE_iff transfer
this bound to the displayed derived object. The choice of a precedes F, so is uniform.
This uses neither coherence, support, nor quasi-coherence of F. -/
theorem exists_relativeTor_pullback_tensor_lower_bound
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X) (hTor : HasFiniteTorDimensionOver f E) :
    ∃ a : ℤ, ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      (E ⊗ (derivedPullback f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)).IsGE a := by
  obtain ⟨K, ⟨eK⟩, P, hP, q, hq, a, b, hab, hbound⟩ := hTor
  refine ⟨a, ?_⟩
  intro F
  apply (DerivedCategory.isGE_iff _ a).2
  intro i hi
  obtain ⟨e⟩ := relativeTensorPullback_homology_comparison f E K eK P hP q hq F i
  have hz := hbound (TopCat.Sheaf.inverseImageModule f.base S.sheaf F) i (Or.inl hi)
  have hz' := (SheafOfModules.toSheaf _).map_isZero hz
  have ht := hz'.of_iso e
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2
  apply (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact ht.eq_of_src (𝟙 _) 0

end AlgebraicGeometry.Scheme
