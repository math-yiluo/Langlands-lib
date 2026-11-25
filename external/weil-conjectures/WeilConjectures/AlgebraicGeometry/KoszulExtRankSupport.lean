/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank

import WeilConjectures.AlgebraicGeometry.KoszulExtOffRankStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Rank support of scalar Koszul Ext

Source: Stacks Project, Tag 0BQZ. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem isIso_rankSupport_unit {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) (M : X.Modules)
    (hM : ∀ x : X, x ∉ U →
      IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M)) :
    IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) := by
  let adj := Scheme.Modules.restrictAdjunction U.ι
  let α := adj.unit.app M
  have hlocal : IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map α ≫
        adj.counit.app ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
      exact (adj.left_triangle_components M).symm ▸
        inferInstanceAs (IsIso (𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj M)))
    exact IsIso.of_isIso_comp_right ((Scheme.Modules.restrictFunctor U.ι).map α)
      (adj.counit.app ((Scheme.Modules.restrictFunctor U.ι).obj M))
  apply Scheme.Modules.isIso_of_bijective_stalkLinearMap α
  intro x
  by_cases hx : x ∈ U
  · exact Scheme.Modules.bijective_stalk_of_isIso_restrict α x hx
  · have hsource := ModuleCat.isZero_iff_subsingleton.mp (hM x hx)
    have htarget := (closedImmersion_pushforward_stalks U.ι
      (Topology.IsClosedEmbedding.subtypeVal hU)
      ((Scheme.Modules.restrictFunctor U.ι).obj M)).1 x (by
        rintro ⟨y, rfl⟩
        exact hx y.property)
    exact ⟨fun a b _ ↦ hsource.elim a b,
      fun b ↦ ⟨0, htarget.elim _ b⟩⟩


/-- Scalar Ext pulled back to the closed subscheme is supported on its matching rank stratum.

Source: Stacks Project, Tag 0BQZ, proof of lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-ext-rank-support).

Proof: The off-rank stalk vanishing theorem makes the pulled-back degree-q
cohomology stalk zero outside the rank-q stratum. Nonnegativity of q identifies
q with the integer coercion of q.toNat. The stratum is closed as well as open
because r is locally constant. For its open inclusion j, the triangle identity
and invertible counit show that restriction of the unit M -> j_*j^*M is an
isomorphism on the stratum. Consequently its stalk maps there are bijective.
Off the stratum, M has zero stalk by off-rank vanishing and j_*j^*M has zero
stalk by the closed-embedding pushforward stalk theorem. The unique map between
these two zero stalks is bijective. Detection of module isomorphisms on stalks
proves that the unit is an isomorphism. Empty source and empty strata are
included: all the stalk assertions are vacuous or compare zero objects. -/
theorem koszulRegularImmersion_ext_rankSupport
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    {q : ℤ} (hq : 0 ≤ q) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    IsIso ((Scheme.Modules.restrictAdjunction
      (Scheme.Modules.exteriorRankOpen r q.toNat).ι).unit.app
        ((Scheme.Modules.tensorPullback i).obj F)) := by
  dsimp only
  apply isIso_rankSupport_unit _ (r.isLocallyConstant.isClosed_fiber q.toNat)
  intro z hz
  apply koszulRegularImmersion_ext_offRank_stalk i hregular r hr q z
  intro he
  apply hz
  change r z = q.toNat
  exact_mod_cast ((Int.toNat_of_nonneg hq).trans he).symm

end AlgebraicGeometry
