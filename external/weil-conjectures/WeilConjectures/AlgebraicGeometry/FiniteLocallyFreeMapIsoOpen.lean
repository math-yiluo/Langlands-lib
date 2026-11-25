/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocusPullback
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback

/-! # The universal isomorphism open of a map of vector bundles

Source: Stacks Project, Tag 0BDP, final determinant sentence; Tag 05GD,
open loci defined by module maps.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The locus where a map of finite locally free modules becomes invertible is a
quasi-compact open immersion, with its universal property on arbitrary test schemes.
Source: Stacks Project, Tag 0BDP, final determinant sentence, and Tag 05GD.
(blueprint: lem-sc-finite-locally-free-map-iso-open)

Proof: Choose simultaneous local frames for M and N on affine opens. If their ranks
are equal, the isomorphism locus on such an open is the principal open of the matrix
determinant. If their ranks differ, it is empty: reduction at any point would otherwise
give an isomorphism between vector spaces of different dimensions. The inverse matrix
on the principal open is given by the adjugate divided by the determinant. Thus these
local opens agree on overlaps, since each is characterized by invertibility of the
restricted map. Glue them to an open U of W and take its open subscheme. On each affine
open of W, finitely many principal affine opens suffice to trivialize both bundles.
The intersections with U are principal opens in these finitely many affine opens,
hence quasi-compact; this proves that U is retrocompact and its inclusion is
quasi-compact. After any base change the same matrices are obtained by scalar
extension. Their determinants become units precisely when the test morphism factors
through their principal opens. These local factorizations glue uniquely, yielding the
asserted equivalence. This works over nonreduced rings: being a unit is equivalent to
membership in no prime ideal. When both ranks are zero the determinant is 1 and the
whole open is retained; the empty scheme imposes no condition. -/
theorem exists_finiteLocallyFreeMapIsoOpen {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N) :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ W), IsOpenImmersion k ∧ QuasiCompact k ∧
      ∀ {T : Scheme.{u}} (h : T ⟶ W),
        (∃ l : T ⟶ Z, l ≫ k = h) ↔ IsIso ((tensorPullback h).map φ) := by
  let U := moduleMapIsoLocus φ
  have hqc : QuasiCompact U.ι := by
    apply (quasiCompact_iff_forall_isAffineOpen (f := U.ι)).2
    intro V hV
    apply (U.ι.isOpenEmbedding.isEmbedding.isCompact_iff).2
    change IsCompact (U.ι '' (U.ι ⁻¹' (V : Set W)))
    simpa only [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι] using
      isCompact_moduleMapIsoLocus_inter M N φ V hV
  refine ⟨U.toScheme, U.ι, inferInstance, hqc, ?_⟩
  intro T h
  constructor
  · rintro ⟨l, hl⟩
    apply isIso_tensorPullback_of_range_subset_moduleMapIsoLocus φ h
    rw [← hl]
    exact Set.Subset.trans (Set.range_comp_subset_range l U.ι)
      (by simp [Scheme.Opens.range_ι, U])
  · intro hφ
    have hh := range_subset_moduleMapIsoLocus_of_isIso_tensorPullback M N φ h hφ
    have hh' : Set.range h ⊆ Set.range U.ι := by
      simpa only [Scheme.Opens.range_ι] using hh
    exact ⟨IsOpenImmersion.lift U.ι h hh', IsOpenImmersion.lift_fac U.ι h hh'⟩

end AlgebraicGeometry.Scheme.Modules
