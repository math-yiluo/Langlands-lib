/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# Bounded constructibility of finite-type direct images

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-dg-finite-type-constructibility.md`
(blueprint: proposition-six-operations-dctf--2).

The ordinary derived direct image preserves bounded constructibility, without a
separatedness hypothesis on the morphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Direct image for a morphism of finite-type schemes over a field preserves bounded
constructible complexes with finite allowable commutative coefficients.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-dg-finite-type-constructibility.md`
(blueprint: proposition-six-operations-dctf--2).

Proof:
1. Finite-type schemes over a field are Noetherian, using
`lem-wf-affine-noetherian-components` and finite affine covers. Choose a bounded-below
injective representative using `lem-weil-pbc-module-sheaves-enough-injectives` and
`lem-weil-pbc-dplus-injective-representative`. Open restriction is exact and preserves
injectives by `lem-pur-kinjective-restrict-localized-adjunction`. The section formula for
`def-weil-pbc-direct-image` identifies restricted direct images. Thus the assertion is
local on the target, and a finite affine cover glues constructibility and bounds.
2. Assume the target affine and choose a finite affine cover of the source. Each cover
member has the projective compactification of `lemma-affine-covers-dense-intersection--2`,
`lemma-affine-covers-dense-intersection--2` and `definition-compactification-refinement--1`. Every
nonempty intersection is open in such a compactification; it need not be affine. Apply
`corollary-open-direct-image-over-field--1`, `theorem-results-from-etale-theory--3` and
clause (5) of `lem-weil-derived-direct-image-composition` to obtain bounded constructible
intersection direct images. Empty intersections give zero.
3. Apply the finite alternating Cech resolution to the injective representative.
Insertion of a cover index contracts each augmented row locally. Restriction preserves
injectives and open direct image preserves them by its exact left adjoint
(`def-weil-pbc-inverse-image`). Finite sums preserve injectivity. Splitting successive
monomorphisms makes each augmented row split exact, hence exact after direct image.
The total augmentation is a quasi-isomorphism: eliminate successive lowest vertical
components using horizontal exactness, terminating in the finite horizontal range.
Shift the bounded-below vertical index to use `def-sp-double-complex-total` and reindex
back, retaining the differential d_h + (-1)^p d_v.
4. Filter the total complex by horizontal degree and apply
`lem-sp-bounded-filtered-page-core`. Quotient maps come from filtration inclusions.
Its first page is the finite sum of intersection direct-image cohomology; its finite
abutment filtration computes the original direct image. Column signs do not change
kernels or images. No composite-functor spectral sequence is used.
5. Take the minimum and maximum of the finitely many intersection bounds. The first
page lies in a finite rectangle. By `thm-constructible-serre`, finite sums, kernels,
cokernels and extensions preserve constructibility; induction gives constructible
stable pages and abutments. The finite filtration gives vanishing outside the total
rectangle. This is `def-weil-pbc-constructible-complexes`. A single cover member gives
one column, zero complexes give zero pages, and the empty source is immediate.
Finally glue over the finite target cover from step 1. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k)))
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K) := by
  have : HasInvertibleExponent A (Spec (.of k)) :=
    ⟨N, hA.1, hA.2.2.1, hA.2.2.2⟩
  have hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
    obtain ⟨hc, a, b, hab, hvan⟩ := hK
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ :=
    boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType A f aX aY hf K hK'
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
    min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb i (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.Etale
