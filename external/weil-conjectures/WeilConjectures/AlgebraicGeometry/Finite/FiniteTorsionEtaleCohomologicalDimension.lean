/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsSepClosed

import WeilConjectures.AlgebraicGeometry.Torsion.TorsionAbelianDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Finiteness of torsion étale cohomological dimension

Source: Stacks Project, Tag 0F10, Lemma 59.96.2; blueprint chap-Smooth-purity,
proposition-ordinary-external-kunneth--1 (blueprint: theorem-results-from-etale-theory--6).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism over a field between finite-type schemes has finite torsion étale
cohomological dimension; over a separably closed field each such scheme has finite dimension.
Source: Stacks Project, Tag 0F10 (blueprint: theorem-results-from-etale-theory--6).

Proof: Choose a natural uniform bound for the dimensions of all extensions of the
source's ground field, using a finite affine cover and finite algebra generators.
The torsion abelian higher-direct-image bound then vanishes above twice this bound:
its proof passes to a separable closure, applies absolute torsion cohomological
vanishing there, and descends through monic finite-separable transition maps.
Thus a finite natural number belongs to the set defining the relative dimension.
Over a separably closed field, the existing finite-type cohomology theorem gives
the absolute bound twice a natural upper bound for the dimension of X. Compare
Ext cohomology with derived global sections and again use the defining infimum.
Both arguments include empty schemes without a nonemptiness hypothesis. -/
theorem torsionEtaleCohomologicalDimension_finite_of_finiteType
    (K : Type u) [Field K]
    (X Y : Scheme.{u}) [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    (@Scheme.Hom.torsionEtaleCohomologicalDimension _ _ f
      (@quasiCompact_of_compactSpace X Y f
        ((quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance)
        (@IsLocallyNoetherian.quasiSeparatedSpace Y
          (LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K)))))
      (@QuasiSeparated.of_quasiSeparatedSpace X Y f
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K)))))) < ⊤ ∧
    (IsSepClosed K →
      (@Scheme.torsionEtaleCohomologicalDimension X
        ((quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance)
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))))) < ⊤) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of K))
  constructor
  · obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le_of_isPullback
      (X ↘ Spec (.of K))
    apply lt_of_le_of_lt (sInf_le ?_) (ENat.natCast_lt_top (2 * n))
    refine ⟨2 * n, rfl, ?_⟩
    intro F hF q hq
    exact Etale.isZero_torsion_higherDirectImage_of_forall_field_dimension_le
      (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)) f (comp_over f _) n hn F hF q
      (by exact_mod_cast hq)
  · intro hK
    have : IsSepClosed K := hK
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of K))
    apply lt_of_le_of_lt (sInf_le ?_) (ENat.natCast_lt_top (2 * d))
    refine ⟨2 * d, rfl, ?_⟩
    intro F hF q hq
    have hH := Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d
      (X ↘ Spec (.of K)) hd F hF q hq
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
    have : Subsingleton ((Sheaf.functorH X.smallEtaleTopology q).obj F) := hH
    exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry
