/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.Mathlib.CategoryTheory.Elements

@[expose] public section

open CategoryTheory Opposite
universe u v
namespace AlgebraicGeometry.Scheme
/-- Category equivalence induced by a morphism of geometric points.
Source: Stacks Project, Étale Cohomology, Remark 59.29.8, Tag 04FN.
(blueprint: new-geometric-point-morphism-category-equivalence)

Proof: Spec.homEquiv writes a as Spec of a field homomorphism i : k' → k, which is
injective. SpecToEquivOfField writes any map from a field spectrum to a scheme X as
(x, j), where j : κ(x) → K. Naturality of fromSpecResidueField shows that
precomposition with a sends (x, j) to (x, i ∘ j). Thus it is injective on maps to X.
For an étale U → S, a lift of s to U is (x, j) with x above the image of s and j
compatible with the residue-field map. The étale residue extension κ(x)/κ(s) is
separable algebraic. Every j(y) is therefore algebraic over i(k'): apply j to a
nonzero polynomial relation over κ(s), whose coefficients land in i(k'). Since
k' is algebraically closed, any element algebraic over i(k') lies in i(k'). Hence
j factors through i. The factor j' is a field map, uniquely determined by the
injectivity of i; it is compatible with the residue map by the same injectivity,
so it gives a lift of s'. This proves that the map of lifts is bijective for each U.
The category-of-elements functor fixes underlying étale objects and arrows. An
arrow h between two lifts satisfies the compatibility condition after composing
with a if and only if it did before, by injectivity of precomposition into the
codomain of h. Thus the functor is fully faithful, and bijectivity of lifts makes
it surjective on objects. It is consequently an equivalence. -/
theorem geometricPointMorphism_category_equivalence
    {S : Scheme.{u}} {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
    (a : Spec (.of k) ⟶ Spec (.of k')) (ha : a ≫ s' = s) :
    let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
    let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
      Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
    (NatTrans.mapElements α).IsEquivalence := by
  let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
  let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
    Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
  change (NatTrans.mapElements α).IsEquivalence
  obtain ⟨β, hβ⟩ := Spec.map_surjective a
  have hbij (U : S.Etale) : Function.Bijective (α.app U) := by
    constructor
    · intro x y hxy
      apply Over.OverMorphism.ext
      apply SpecMap_comp_injective β
      rw [hβ]
      exact congrArg Over.Hom.left hxy
    · intro x
      obtain ⟨y, hy, hys⟩ := U.hom.exists_SpecMap_comp_eq_of_isSepClosed β s' x.left
        (by simpa [hβ, ha] using x.w)
      refine ⟨Over.homMk y hys, ?_⟩
      apply Over.OverMorphism.ext
      change a ≫ y = x.left
      rwa [hβ] at hy
  have : IsIso α := by
    have (U : S.Etale) : IsIso (α.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
    exact NatIso.isIso_of_isIso_app _
  exact (NatIso.mapElements (asIso α)).isEquivalence_functor

end AlgebraicGeometry.Scheme
