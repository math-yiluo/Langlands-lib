/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
set_option autoImplicit false

/-!
# Unbounded comparison on the small etale and pro-etale sites

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: lem-sfb-unbounded-site-comparison).

The theorem states exactness, full faithfulness, and arbitrary small-coproduct preservation
of the canonical finite-coefficient comparison on unbounded derived categories.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a finite or algebraically closed field and a finite primary coefficient ring, the
termwise comparison from the etale to the pro-etale module derived category is exact,
fully faithful, and preserves arbitrary small direct sums.

Source: blueprint `sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`,
statement and proof (blueprint: proposition-unbounded-comparison-finite-coefficients--1).
Proof:
1. Write L for the exact comparison inverse image and E for finite coefficient
realization. Exactness induces the triangulated termwise derived functor, and E is
an equivalence by the existing coefficient realization theorem.
2. Form the canonical unbounded derived adjunction of L and comparison direct image.
Replace the nilpotence exponent n by n+1. Apply
proposition-unbounded-comparison-finite-coefficients--1: the derived image of L has classical
cohomology, and the actual derived counit is invertible on this image. That theorem
contains the geometric finite-cohomological-dimension and truncation argument.
3. The underived L is fully faithful and reflects isomorphisms. The natural
cohomology comparison identifies H^q(L(f)) with L(H^q(f)); hence L on derived
categories also reflects isomorphisms by DerivedCategory.isIso_iff.
4. The left triangle identity says that L of the derived unit, followed by the
counit on the image, is the identity. Cancel the invertible counit and reflect
isomorphisms through derived L. Thus the derived unit is invertible, and the
derived adjunction gives full faithfulness of L.
5. Compose with derived E and transport along the canonical derived composition
isomorphism. The left adjunction preserves colimits of every requested discrete
shape; derived E preserves them as an equivalence. The same composition
isomorphism transfers preservation to finiteCoefficientDerivedComparison.
-/
theorem finiteCoefficientDerivedComparison_fullyFaithful
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (finiteCoefficientComparison X A).mapDerivedCategory.IsTriangulated ∧
      Nonempty (finiteCoefficientDerivedComparison X A).FullyFaithful ∧
      ∀ (I : Type v),
        Nonempty (PreservesColimitsOfShape (Discrete I)
          (finiteCoefficientDerivedComparison X A)) := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let E := finiteCoefficientRealization X A
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  have hA' : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0 := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n + 1, by omega, by rw [pow_succ, hn, zero_mul]⟩
  obtain ⟨himage, hcounit⟩ :=
    comparisonUpperStar_isClassicalComplexFor k hbase ℓ hℓ A hA' X
  have hreflect : L.mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun f _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (L.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff (L.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ L
  have hunit : IsIso adj.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have : IsIso (adj.counit.app (L.mapDerivedCategory.obj K)) :=
      hcounit _ (himage K)
    have ht : L.mapDerivedCategory.map (adj.unit.app K) ≫
        adj.counit.app (L.mapDerivedCategory.obj K) = 𝟙 _ :=
      adj.left_triangle_components K
    have : IsIso (L.mapDerivedCategory.map (adj.unit.app K) ≫
        adj.counit.app (L.mapDerivedCategory.obj K)) := by
      rw [ht]
      infer_instance
    have : IsIso (L.mapDerivedCategory.map (adj.unit.app K)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app (L.mapDerivedCategory.obj K))
    exact isIso_of_reflects_iso _ L.mapDerivedCategory
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  let e := Functor.mapDerivedCategoryCompIso L E
  let f := (ff.comp (Functor.FullyFaithful.ofFullyFaithful E.mapDerivedCategory)).ofIso e
  refine ⟨inferInstance, ⟨f⟩, ?_⟩
  intro I
  have : PreservesColimitsOfShape (Discrete I) L.mapDerivedCategory :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) (L.mapDerivedCategory ⋙ E.mapDerivedCategory) :=
    inferInstance
  exact ⟨preservesColimitsOfShape_of_natIso e⟩

end AlgebraicGeometry.ProEtale
