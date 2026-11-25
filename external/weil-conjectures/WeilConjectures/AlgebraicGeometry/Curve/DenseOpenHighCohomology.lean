/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomologyPullback

/-! # Higher cohomology across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The counit from extension by zero induces bijections in degrees above one,
including degree two after restriction to any open immersion.
Source: Stacks Project, Tag 0GJA, proof, the higher-degree isomorphisms and remark (d)
(blueprint: lem-pbc-s2-dense-open-high-cohomology).

Proof: Give the closed complement Z its reduced induced scheme structure. A dense open
contains the generic points of every component of the Noetherian curve X. The complement
therefore has dimension zero, is a finite discrete union of closed points, and its residue
fields equal the algebraically closed base field. The open-closed short exact sequence has
first arrow the counit j_!j^*F -> F and last term i_*i^*F. Forgetting to abelian sheaves is
exact. Since the closed immersion i is finite, its higher direct images vanish, and Leray
identifies the cohomology of this last term with that of i^*F on Z. Each component of Z is
a spectrum of an algebraically closed field and has no positive-degree etale cohomology.
The long exact sequence thus makes the counit map bijective for q > 1. For any open
immersion a:W -> X, the inverse image of i_*i^*F is the corresponding closed direct image
from W times_X Z. This is again a union of algebraically closed points. Apply the pulled
back short exact sequence and the same argument in degree two. The maps are precisely
Sheaf.H.map of the counit and its inverse image, so no choice of cohomology comparison is
involved. If X or Z is empty the same exact sequence has zero terms; if U is all of X the
counit is an isomorphism. Neither constructibility nor torsion is needed. -/
theorem dense_open_high_cohomology (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    (∀ q : ℕ, 1 < q → Function.Bijective (Sheaf.H.map ε q)) ∧
      (∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a],
        Function.Bijective
          (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map ε) 2)) := by
  dsimp
  exact ⟨dense_open_high_cohomology_high Λ f F U hU,
    dense_open_high_cohomology_pullback Λ f F U hU⟩

end AlgebraicGeometry.IsCurve
