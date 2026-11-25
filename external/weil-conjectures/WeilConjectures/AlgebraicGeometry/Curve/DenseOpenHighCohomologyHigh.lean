/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomologyExtension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyBijective

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The higher-degree component of dense-open cohomology comparison.
Source: Stacks Project, Tag 0GJA. (blueprint: lem-pbc-s2-dense-open-high-cohomology-high)
-/
theorem dense_open_high_cohomology_high (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    ∀ q : ℕ, 1 < q → Function.Bijective (Sheaf.H.map ε q) := by
  let E := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hij : Set.range U.closedComplement.base = (Set.range U.ι.base)ᶜ := by
    rw [U.range_closedComplement, Scheme.Opens.range_ι]
  let S := openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι U.closedComplement
    (disjoint_range_of_range_eq_compl _ _ hij) F
  have hS : (S.map E).ShortExact := shortExact_map_forget₂ Λ
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) U.ι U.closedComplement F hij)
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).subscheme
  let i : Z ⟶ X := U.closedComplement
  have hdim : topologicalKrullDim Z ≤ 0 := by
    obtain ⟨n, V, hVU, _, _, _, hVdim, _⟩ := exists_dense_irreducible_opens f U hU
    let b : Z → ↥(⋃ a, (V a : Set X))ᶜ := fun z ↦ ⟨i.base z, by
      have hz : i.base z ∈ (U : Set X)ᶜ := U.range_closedComplement ▸ ⟨z, rfl⟩
      intro hv
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
      exact hz (hVU a ha)⟩
    have hb : Topology.IsInducing b :=
      (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp
        i.isClosedEmbedding.isInducing
    exact hb.topologicalKrullDim_le.trans hVdim
  have hboundary : ∀ n : ℕ, 0 < n → Subsingleton (Sheaf.H (S.map E).X₃ n) := by
    intro n hn
    let B := (sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj F)
    have hB := (zero_dimensional_etale_cohomology k Z (i ≫ f) hdim B
      (fun z ↦ AlgebraicClosure (Z.residueField z)) Z.algClosurePoint
      (fun z ↦ Z.algClosurePoint_base z default)).2.1 n hn
    let e := (Scheme.nonempty_sheafH_extDerivedIso Z n).some.app B
    have hB' : Subsingleton (Sheaf.H B n) := by
      constructor
      intro x y
      exact e.addCommGroupIsoToAddEquiv.injective (hB.elim _ _)
    have : Subsingleton (Sheaf.H
        ((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).obj B) n) := hB'
    change Subsingleton (Sheaf.H ((i)_*[AddCommGrpCat.{u + 1}].obj B) n)
    exact (bijective_edgeMap_of_isFinite i B n).injective.subsingleton
  dsimp only
  intro q hq
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have := hboundary m (by omega)
  have := hboundary (m + 1) (by omega)
  exact Sheaf.H.bijective_map_f hS m

end AlgebraicGeometry.IsCurve
