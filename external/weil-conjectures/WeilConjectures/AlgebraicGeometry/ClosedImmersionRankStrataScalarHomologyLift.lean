/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Algebra.Homology.OpenSupportedHomologyApproximation
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Lifting scalar maps from one closed rank support

Source: Stacks Tags 0BQZ, 08BS, 08BT; rank-support reconstruction step 2.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

private theorem single_lift_of_concentrated
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    (n : ℤ) (S : C) (L : DerivedCategory C)
    (hL : ∀ m : ℤ, m ≠ n → IsZero ((DerivedCategory.homologyFunctor C m).obj L))
    (a : S ⟶ (DerivedCategory.homologyFunctor C n).obj L) :
    ∃ f : (DerivedCategory.singleFunctor C n).obj S ⟶ L,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app S ≫
        (DerivedCategory.homologyFunctor C n).map f = a := by
  have : L.IsGE n := (DerivedCategory.isGE_iff L n).mpr
    (fun m hm ↦ hL m (ne_of_lt hm))
  have : L.IsLE n := (DerivedCategory.isLE_iff L n).mpr
    (fun m hm ↦ hL m (ne_of_gt hm))
  obtain ⟨B, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L n
  let H := DerivedCategory.homologyFunctor C n
  let F := DerivedCategory.singleFunctor C n
  let η := DerivedCategory.singleFunctorCompHomologyFunctorIso C n
  let d : S ⟶ B := a ≫ H.map e.hom ≫ η.hom.app B
  refine ⟨F.map d ≫ e.inv, ?_⟩
  rw [Functor.map_comp, ← Category.assoc]
  have hd := η.inv.naturality d
  simp only [Functor.comp_map, Functor.id_map] at hd
  change (η.inv.app S ≫ H.map (F.map d)) ≫ H.map e.inv = a
  rw [← hd]
  simp only [d, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← H.map_comp, e.hom_inv_id, H.map_id, Category.comp_id]

private theorem rank_term_stalk_zero
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (r : LocallyConstant Z ℕ) (q : ℕ)
    (E : (Scheme.Modules.exteriorRankOpen r q).toScheme.Modules)
    (y : Y) (hy : y ∉ i.base '' {z | r z = q}) :
    IsZero ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r q).ι).obj E))) := by
  let j := (Scheme.Modules.exteriorRankOpen r q).ι
  have hj : Topology.IsClosedEmbedding j.base :=
    Topology.IsClosedEmbedding.subtypeVal (r.isLocallyConstant.isClosed_fiber q)
  have hij : Topology.IsClosedEmbedding (j ≫ i).base := i.isClosedEmbedding.comp hj
  have hy' : y ∉ Set.range (j ≫ i).base := by
    rintro ⟨z, hz⟩
    exact hy ⟨z.val, z.property, hz⟩
  have hs := (closedImmersion_pushforward_stalks (j ≫ i) hij E).1 y hy'
  have hz : IsZero ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (j ≫ i)).obj E)) := by
    have : Subsingleton ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward (j ≫ i)).obj E)) := hs
    exact ModuleCat.isZero_of_subsingleton _
  exact hz.of_iso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapIso
    ((Scheme.Modules.pushforwardComp j i).app E))


/-- A scalar map from one closed rank support lifts to the derived object when
its other cohomology degrees are supported on the other rank strata.

Source: Stacks, Tag 0BQZ (single-degree truncation), and Cohomology, Tags
08BS and 08BT (exact extension by zero and its adjunction).
(blueprint: lem-sc-closed-immersion-rank-strata-scalar-homology-lift)

Proof: For negative n the source is zero, and the zero morphism is a lift.
Otherwise let V be the complement in Y of the closed image of the complement
of the rank-n stratum. On V every other cohomology degree vanishes: its
support is a different rank stratum. Exact restriction therefore gives a
single-degree derived object. The canonical truncation isomorphism identifies
it with its degree-n homology placed in degree n, compatibly with homology.
Restrict a and compose with the inverse truncation isomorphism. Extension
by zero is exact and left adjoint to restriction, so this local morphism
extends to a morphism into K. The source sheaf is supported on the closed
image of the rank-n stratum, which is contained in V; hence the counit
from the extension by zero of its restriction is an isomorphism, as is
checked on stalks. Use this isomorphism to identify the extended source
with the original source. The homology of the resulting morphism is a:
on V this follows from the truncation comparison and counit naturality,
and off V both maps have zero source stalk. Equality of sheaf morphisms
is detected on stalks. Empty strata give zero source; no finiteness or
algebra action is used. -/
theorem closedImmersion_rankStrata_scalar_homology_lift
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings Y.toRingedSpace))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (n : ℤ)
    (hother : ∀ m : ℤ, m ≠ n → Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) m).obj K ≅
        (Scheme.Modules.pushforward i).obj (T m)))
    (a : (Scheme.Modules.pushforward i).obj (T n) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K) :
    ∃ f : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj
          ((Scheme.Modules.pushforward i).obj (T n)) ⟶ K,
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).inv.app
          ((Scheme.Modules.pushforward i).obj (T n)) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).map f = a := by
  by_cases hn : 0 ≤ n
  · let V : TopologicalSpace.Opens Y.toRingedSpace :=
      ⟨(i.base '' {z | r z ≠ n.toNat})ᶜ,
        (i.isClosedEmbedding.isClosedMap _
          (r.isLocallyConstant.isOpen_fiber n.toNat).isClosed_compl).isOpen_compl⟩
    have hsource : ∀ y : Y, y ∉ V →
        IsZero ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
          ((Scheme.Modules.pushforward i).obj (T n))) := by
      intro y hy
      rw [hT n, ite_eq_left hn]
      apply rank_term_stalk_zero i r n.toNat (E n.toNat) y
      rintro ⟨z, hz, rfl⟩
      apply hy
      change i.base z ∉ i.base '' {z | r z ≠ n.toNat}
      rintro ⟨z', hz', heq⟩
      exact hz' ((i.isClosedEmbedding.injective heq) ▸ hz)
    have hlocal : ∀ m : ℤ, m ≠ n → ∀ y : Y, y ∈ V →
        IsZero ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) m).obj K)) := by
      intro m hm y hy
      obtain ⟨e⟩ := hother m hm
      apply IsZero.of_iso _ ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapIso e)
      by_cases hm0 : 0 ≤ m
      · rw [hT m, ite_eq_left hm0]
        apply rank_term_stalk_zero i r m.toNat (E m.toNat) y
        rintro ⟨z, hz, heq⟩
        apply hy
        refine ⟨z, ?_, heq⟩
        change r z ≠ n.toNat
        intro hz'
        apply hm
        have hnat : m.toNat = n.toNat := hz.symm.trans hz'
        omega
      · rw [hT m, ite_eq_right hm0]
        exact (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map_isZero
          ((Scheme.Modules.pushforward i).map_isZero (isZero_zero _))
    obtain ⟨L, b, hL, hfactor⟩ := open_supported_homology_approximation
      Y.toRingedSpace V ((Scheme.Modules.pushforward i).obj (T n)) K n hsource hlocal
    obtain ⟨c, hc⟩ := hfactor a
    obtain ⟨g, hg⟩ := single_lift_of_concentrated n _ L hL c
    refine ⟨g ≫ b, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hg, hc]
  · have hzero : IsZero ((Scheme.Modules.pushforward i).obj (T n)) := by
      rw [hT n, ite_eq_right hn]
      exact (Scheme.Modules.pushforward i).map_isZero (isZero_zero _)
    refine ⟨0, ?_⟩
    rw [Functor.map_zero, comp_zero]
    exact hzero.eq_of_src _ _


end AlgebraicGeometry
