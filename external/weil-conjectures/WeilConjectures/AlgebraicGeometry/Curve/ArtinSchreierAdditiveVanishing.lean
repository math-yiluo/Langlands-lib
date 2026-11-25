/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
import WeilConjectures.AlgebraicGeometry.EtaleZariskiCohomology
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentCohomologyULift


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Vanishing of derived additive cohomology above degree one.
Source: blueprint `proposition-p-torsion-smooth-proper-curve--3`, step 2; Stacks 03P2 and 02UZ.
(blueprint: lem-sc-artin-schreier-additive-derived-vanishing)

Proof: The given isomorphism identifies G with the universe lift of the additive
etale structure sheaf. Compare derived global sections on a sheaf in degree zero
with ordinary sheaf cohomology, by injective resolutions (lem-sp-kinjective-computes).
To compare with the smaller-universe sheaf, use finite affine etale hypercovers:
quasi-compactness gives finite refinements in each degree needed to compute q.
Universe lift identifies their cochains, cocycles and coboundaries sectionwise,
since it preserves finite products and is exact. This does not assume
that universe lift preserves injective sheaves. By
proposition-p-torsion-smooth-proper-curve--3, ordinary additive etale cohomology agrees with Zariski
structure-sheaf cohomology and vanishes in degrees at least two: the curve is
Noetherian of dimension one, so use cohomology above dimension (Stacks 02UZ).
Transport zero across these comparisons and the given sheaf isomorphism. -/
theorem isZero_etaleCohomology_additive_of_two_le
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : G ≅ (sheafCompose C.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        G)) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : C.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  let F := Scheme.Modules.unitObj C
  obtain ⟨c⟩ := Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift C F q
  have hs := (subsingleton_etale_ga_and_structure_cohomology f q hq).1
  have : Subsingleton (Sheaf.H (Scheme.Modules.etaleTensorSectionsSheaf F) q) := hs
  have hl : Subsingleton (Sheaf.H
      ((sheafCompose C.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Scheme.Modules.etaleTensorSectionsSheaf F)) q) := c.injective.subsingleton
  let ce :=
    ((Sheaf.functorH.{u + 1} C.smallEtaleTopology q).mapIso e).addCommGroupIsoToAddEquiv
  have hg : Subsingleton (Sheaf.H.{u + 1} G q) := @Equiv.subsingleton _ _ ce.toEquiv hl
  obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso C q
  have hz : IsZero ((Sheaf.functorH.{u + 1} C.smallEtaleTopology q).obj G) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr hg
  exact hz.of_iso (a.app G).symm

end AlgebraicGeometry
