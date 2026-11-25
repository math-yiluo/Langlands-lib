/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import WeilConjectures.Mathlib.RingTheory.Localization.Ideal
public import WeilConjectures.Mathlib.Topology.Connected.Clopen
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Connected locally noetherian schemes with integral local rings

## Main statements

- `AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`: a connected locally noetherian scheme
  all of whose local rings are integral domains is irreducible.
- `AlgebraicGeometry.IsLocallyNoetherian.locallyConnectedSpace`: a locally noetherian scheme is
  locally connected.
- `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`: a scheme quasi-compact and locally of
  finite type over a noetherian scheme is noetherian.
- `AlgebraicGeometry.isNoetherian_left`: a scheme quasi-compact and locally of finite type over a
  field is noetherian.
- `AlgebraicGeometry.Scheme.exists_pow_eq_zero_of_isNilpotent`: on a quasi-compact locally
  noetherian scheme the nilpotency index of nilpotent sections is uniformly bounded.
-/

@[expose] public section

universe u

open TopologicalSpace Topology

namespace AlgebraicGeometry

/-- A connected locally noetherian scheme all of whose local rings are integral domains is
irreducible.

Each point `x` lies in a unique irreducible component of a noetherian affine open neighbourhood,
since the generic points of these components are generalizations of `x`, and the set of
generalizations of `x` is irreducible, being the image of `Spec 𝒪_{X, x}`. So every point has an
irreducible open neighbourhood, and a connected locally irreducible space is irreducible. -/
theorem irreducibleSpace_of_isDomain_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    [ConnectedSpace X] (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IrreducibleSpace X := by
  refine irreducibleSpace_of_forall_exists_isPreirreducible fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hVN : NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  have hS : IsIrreducible {y | y ⤳ x} := by
    rw [← X.range_fromSpecStalk, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (X.fromSpecStalk x).continuous.continuousOn
  have hS' : IsPreirreducible (((↑) : V → X) ⁻¹' {y | y ⤳ x}) :=
    hS.isPreirreducible.preimage V.2.isOpenEmbedding_subtypeVal
  obtain ⟨U, hU, hxU, hUirr⟩ := @NoetherianSpace.exists_isOpen_isPreirreducible V _ hVN
    (⟨x, hxV⟩ : V) fun Z₁ hZ₁ Z₂ hZ₂ hx₁ hx₂ ↦ by
      have hirr : IsIrreducible (closure (((↑) : V → X) ⁻¹' {y | y ⤳ x})) :=
        IsIrreducible.closure ⟨⟨⟨x, hxV⟩, specializes_rfl⟩, hS'⟩
      obtain ⟨W, hW, hSW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
      have key : ∀ Z ∈ irreducibleComponents V, (⟨x, hxV⟩ : V) ∈ Z → Z = W := fun Z hZ hxZ ↦ by
        obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents _ hZ)
        refine (hZ.eq_of_ge hW.1 ?_).symm
        refine hη.symm.trans_subset (subset_trans ?_ hSW)
        exact closure_mono (Set.singleton_subset_iff.mpr
          ((hη.specializes hxZ).map continuous_subtype_val))
      exact (key Z₁ hZ₁ hx₁).trans (key Z₂ hZ₂ hx₂).symm
  exact ⟨((↑) : V → X) '' U, V.2.isOpenMap_subtype_val U hU, ⟨_, hxU, rfl⟩,
    hUirr.image _ continuous_subtype_val.continuousOn⟩

/-- A locally noetherian scheme is locally connected, since it is covered by noetherian open
subspaces. -/
instance (priority := 100) IsLocallyNoetherian.locallyConnectedSpace {X : Scheme.{u}}
    [IsLocallyNoetherian X] : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
  have : LocallyConnectedSpace W := NoetherianSpace.locallyConnectedSpace
  have hU' : ((↑) : W → X) ⁻¹' U ∈ 𝓝 (⟨x, hxW⟩ : W) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU, hV, hxV, hVc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp this) _ _ hU'
  refine ⟨((↑) : W → X) '' V, ?_, W.2.isOpenMap_subtype_val _ hV, ⟨_, hxV, rfl⟩,
    hVc.image _ continuous_subtype_val.continuousOn⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hVU hv

/-- A scheme that is quasi-compact and locally of finite type over a noetherian scheme is
noetherian. -/
theorem isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  {}

/-- A scheme quasi-compact and locally of finite type over a field is noetherian. -/
theorem isNoetherian_left {k : Type u} [Field k] (Y : CategoryTheory.Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] : IsNoetherian Y.left :=
  isNoetherian_of_locallyOfFiniteType Y.hom

/-- On a quasi-compact locally noetherian scheme the nilpotency index of nilpotent sections is
uniformly bounded: every local ring is a localization of a noetherian ring of sections over one
of finitely many affine opens, whose nilradical is nilpotent. -/
theorem Scheme.exists_pow_eq_zero_of_isNilpotent (X : Scheme.{u}) [CompactSpace X]
    [IsLocallyNoetherian X] :
    ∃ N : ℕ, ∀ (U : X.Opens) (a : Γ(X, U)), IsNilpotent a → a ^ N = 0 := by
  have key (x : X) : ∃ (V : X.Opens) (N : ℕ), x ∈ V ∧
      ∀ y ∈ V, _root_.nilradical (X.presheaf.stalk y) ^ N = ⊥ := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, V)
    refine ⟨V, N, hxV, fun y hy ↦ ?_⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have := hV.isLocalization_stalk ⟨y, hy⟩
    exact nilradical_pow_eq_bot_of_isLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hN
  choose V N hxV hN using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨t.sup N, fun U a ha ↦ TopCat.Presheaf.section_ext X.sheaf U _ _ fun y hy ↦
    (?_ : (X.presheaf.germ U y hy).hom (a ^ t.sup N) = 0).trans (map_zero _).symm⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ V x := by simpa using ht (Set.mem_univ y)
  have hmem := Ideal.pow_mem_pow (mem_nilradical.mpr (ha.map (X.presheaf.germ U y hy).hom))
    (t.sup N)
  rw [map_pow]
  exact (Ideal.mem_bot.mp ((Ideal.pow_le_pow_right (Finset.le_sup hxt)).trans
    (hN x y hyx).le hmem))


end AlgebraicGeometry
