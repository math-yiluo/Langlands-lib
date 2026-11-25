/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections

/-!
# The comparison unit for sheaves of sets

## References

* Stacks Project, Tag 099T
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The comparison unit is invertible for every etale sheaf of sets, and comparison
inverse image induces a bijection on every Hom set. -/
theorem proEtaleClassicalSheavesUnit (X : Scheme.{u}) :
    (∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      IsIso ((proEtaleSiteComparison X).unit.app F)) ∧
    (∀ F F' : Sheaf X.smallEtaleTopology (Type (u + 1)),
      Function.Bijective
        (fun φ : F ⟶ F' ↦
          (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
            (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).map φ)) := by
  obtain ⟨A, e, p, _, _, hbij, hunit⟩ := proEtaleComparisonPullbackSections X
  have hη : ∀ F : Sheaf X.smallEtaleTopology (Type (u + 1)),
      IsIso ((proEtaleSiteComparison X).unit.app F) := by
    intro F
    have happ : ∀ U : X.Etaleᵒᵖ,
        IsIso (((proEtaleSiteComparison X).unit.app F).hom.app U) := by
      intro U
      apply (isIso_iff_bijective _).2
      let q := (p.app F).hom.hom.app (Opposite.op ((toProEt X).obj U.unop))
      have hq : Function.Bijective q := ConcreteCategory.bijective_of_isIso q
      have heq : (e F ((toProEt X).obj U.unop)) ∘ q ∘
          ((proEtaleSiteComparison X).unit.app F).hom.app U =
          proEtaleComparisonEtaleSection F U.unop := by
        funext s
        exact hunit F U.unop s
      have hcomp := hbij F U.unop
      rw [← heq] at hcomp
      exact (hcomp.of_comp_left (e F ((toProEt X).obj U.unop)).injective).of_comp_left hq.1
    have : IsIso ((sheafToPresheaf X.smallEtaleTopology (Type (u + 1))).map
        ((proEtaleSiteComparison X).unit.app F)) := by
      change IsIso ((proEtaleSiteComparison X).unit.app F).hom
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf X.smallEtaleTopology (Type (u + 1)))
  refine ⟨hη, ?_⟩
  have : IsIso (proEtaleSiteComparison X).unit := NatIso.isIso_of_isIso_app _
  intro F F'
  exact (proEtaleSiteComparison X).fullyFaithfulLOfIsIsoUnit.map_bijective F F'

end AlgebraicGeometry.Scheme
