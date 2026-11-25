/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentLift
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.AlgebraicGeometry.PerfectHomGap
import WeilConjectures.AlgebraicGeometry.AffinePerfectTruncationTriangle

/-! # Extending perfect complexes after adjoining a shifted locally free sheaf

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, Lemma 36.13.6,
lemma-lift-perfect-complex-plus-locally-free
(blueprint: lem-sc-affine-perfect-plus-locally-free).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem qc_single (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (hM : M.IsQuasicoherent)
    (n : ℤ) : schemeDerivedQCohProperty Y ((DerivedCategory.singleFunctor _ n).obj M) := by
  have hzero : IsZero
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro j
  by_cases hj : j = n
  · subst j
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app M).symm hM
  · apply (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact DerivedCategory.isZero_of_isGE _ n j hj
    · exact DerivedCategory.isZero_of_isLE _ n j hj

set_option backward.isDefEq.respectTransparency false in
/-- A perfect object on a quasi-compact open of an affine scheme extends after adjoining
an integer shift of a finite locally free sheaf, whose rank is allowed to vary locally.
Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, Lemma 36.13.6,
lemma-lift-perfect-complex-plus-locally-free
(blueprint: lem-sc-affine-perfect-plus-locally-free).

Proof:
1. Perfectness implies pseudo-coherence and locally finite Tor-amplitude by
   lem-pc-perfect-pseudo-coherent-locally-finite-tor. A finite open cover of U gives
   a common Tor-amplitude interval [a,b]. By lem-sc-affine-pseudo-coherent-lift,
   represent F by the restriction of a bounded-above finite-free complex P on X.
2. Choose r < a and put K = image of the differential from degree r-1 to degree r.
   On U this is the kernel of the next differential. By
   lem-sc-affine-truncation-kernel-finite-locally-free, K restricted to U is finite
   locally free. The complex beginning with K in degree r-1 represents F on U.
   The bounded finite-free tail beginning in degree r is perfect on X. Stupid
   truncation gives the triangle tail|U → F → K|U[1-r] → (tail|U)[1].
3. Since U is quasi-compact and separated, lem-sc-perfect-ext-bounded-qcoh-vanishing
   gives an interval [a',b'] outside which a quasi-coherent target has no maps from F.
   Choose r additionally with r-1 < a'. The sheaf K|U[1-r] is in degree r-1,
   so the map from F to it vanishes.
4. The split-triangle lemma gives tail|U isomorphic to K|U[-r] direct sum F.
   Take the sheaf K|U and the perfect tail as the two existential witnesses.
-/
theorem exists_perfect_lift_plus_finiteLocallyFree
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F) :
    ∃ (r : ℤ) (M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      M.IsFiniteLocallyFree ∧ ∃ P : schemeDerivedCategory X, IsPerfect X P ∧
        Nonempty
          (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj P ≅
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj M)⟦-r⟧ ⊞ F) := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨a, b, hab, hgap⟩ := exists_subsingleton_hom_of_isPerfect U.toScheme F hF
  have hpc : IsPseudoCoherent U.toScheme F := by
    intro x
    obtain ⟨V, hxV, K, hK, e⟩ := hF x
    obtain ⟨W, hxW, _, _, L, ⟨c, d, hb⟩, hf, he⟩ :=
      exists_finiteFree_refinement_of_isStrictlyPerfect U.toScheme F V K hK e x hxV
    exact ⟨W, hxW, L, ⟨d, fun n hn ↦ hb n (Or.inr hn)⟩, hf, he⟩
  obtain ⟨K, hbounded, hfree, hrep⟩ :=
    exists_boundedAbove_finiteFree_lift X U hU F hpc
  obtain ⟨N, hN⟩ :=
    exists_low_perfect_truncation_triangle X U hU F hF K hbounded hfree hrep
  let r : ℤ := min N a
  obtain ⟨M, hM, P, hP, i, p, δ, hT⟩ := hN r (min_le_left _ _)
  let := hM
  let C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let e : ((DerivedCategory.singleFunctor C r).obj M)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor C (r - 1)).obj M :=
    ((DerivedCategory.singleFunctors C).shiftIso 1 (r - 1) r (by omega)).app M
  have hqc : schemeDerivedQCohProperty U.toScheme
      (((DerivedCategory.singleFunctor C r).obj M)⟦(1 : ℤ)⟧) := by
    intro j
    exact (SheafOfModules.isQuasicoherent (moduleRings U.toScheme.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor C j).mapIso e).symm
      (qc_single U.toScheme M inferInstance (r - 1) j)
  have hz : ∀ j : ℤ, a ≤ j → j ≤ b →
      IsZero ((DerivedCategory.homologyFunctor C j).obj
        (((DerivedCategory.singleFunctor C r).obj M)⟦(1 : ℤ)⟧)) := by
    intro j haj _
    apply IsZero.of_iso (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor C (r - 1)).obj M) (r - 1) j (by
        dsimp [r]
        omega))
    exact (DerivedCategory.homologyFunctor C j).mapIso e
  have hδ : δ = 0 := (hgap _ hqc hz).elim _ _
  obtain ⟨eP, _⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang
    (Pretriangulated.Triangle.mk i p δ) hT hδ
  refine ⟨r, M, hM, P, hP, ⟨eP ≪≫ biprod.mapIso ?_ (Iso.refl F)⟩⟩
  exact (((DerivedCategory.singleFunctors C).shiftIso (-r) r 0 (by omega)).app M).symm

end AlgebraicGeometry.Scheme
