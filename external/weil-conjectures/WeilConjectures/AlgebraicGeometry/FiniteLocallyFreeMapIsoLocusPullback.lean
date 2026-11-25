/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkBaseChangeReflectsIso
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkIsoNeighborhood

/-! # Arbitrary base change detects the isomorphism locus

Source: Stacks Project, Tag 00O0, Lemma 10.79.4(3), matrix proof; Tag 0BDP,
final determinant sentence; Tag 0098, tensor formula for pullback stalks.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If a pulled-back vector bundle map is invertible, its topological image lies in
the explicitly constructed locally invertible open.
Source: Stacks Project, Tags 00O0, 05GF and 0098.
(blueprint: lem-sc-finite-locally-free-map-iso-locus-pullback)

Proof: Take a point t of T whose image is the point in the range. The stalk
functor takes the pulled-back map to an isomorphism. The natural tensor-pullback
stalk comparison identifies this with extension of the original stalk map along
O_{W,h(t)} to O_{T,t}; NatIso.isIso_map_iff transports invertibility. The local
finite-free reflection theorem makes the original map invertible at h(t). The
stalk inverse extension theorem supplies an open neighbourhood U of h(t) on which
tensor pullback of the map is invertible. The membership criterion for the union
moduleMapIsoLocus inserts h(t) into that union. For empty T there is no point in
the range. The two intermediate arguments allow zero ranks and nonreduced schemes. -/
theorem range_subset_moduleMapIsoLocus_of_isIso_tensorPullback {W : Scheme.{u}}
    (M N : W.Modules) [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    {T : Scheme.{u}} (h : T ⟶ W) (hφ : IsIso ((tensorPullback h).map φ)) :
    Set.range h ⊆ (moduleMapIsoLocus φ : Set W) := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  have := hφ
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso h t
  have hp : IsIso ((tensorPullback h ⋙
      RingedSpace.moduleStalkFunctor T.toRingedSpace t).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have he := (NatIso.isIso_map_iff e φ).mp hp
  have hs := isIso_moduleStalkMap_of_isIso_extendScalars M N φ h t he
  obtain ⟨U, htU, hU⟩ :=
    exists_isIso_tensorPullback_of_isIso_moduleStalkMap M N φ (h t) hs
  exact (mem_moduleMapIsoLocus φ (h t)).2 ⟨U, hU, htU⟩

end AlgebraicGeometry.Scheme.Modules
