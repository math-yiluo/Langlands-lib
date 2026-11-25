/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
public import Mathlib.Topology.Connected.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-! # A coefficient-sized contractible cover subordinate to connected components

Source: Stacks Project, Tags 09C6, 0990 and 098F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem small_pushforward_eq_pullback (X : Scheme.{u})
    (W : X.ProEt) (S : Sieve
      ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj W)) :
    S.functorPushforward AsSmall.down = S.functorPullback AsSmall.up := by
  ext Y f
  constructor
  · rintro ⟨Z, a, b, ha, hab⟩
    have hh := S.downward_closed ha
      (show AsSmall.up.obj Y ⟶ Z from ⟨b⟩)
    change S (show AsSmall.up.obj Y ⟶ AsSmall.up.obj W from ⟨f⟩)
    have he : (show AsSmall.up.obj Y ⟶ Z from ⟨b⟩) ≫ a = ⟨f⟩ :=
      ULift.ext hab.symm
    exact he ▸ hh
  · intro hf
    exact ⟨AsSmall.up.obj Y, ⟨f⟩, 𝟙 _, hf, by simp⟩

/-- An affine w-contractible ring gives weak contractibility on the actual model slice,
in every coefficient universe. Source: Stacks Tags 0990 and 090K.
(auxiliary; not a blueprint node).

Proof: every cover of its spectrum has a disjoint open refinement, by splitting a
faithfully flat ind-etale affine cover. Lift that refinement through AsSmall and into
the slice. Its members remain monomorphisms, and distinct members have empty intersection.
Sheaf gluing therefore lifts any section through an epimorphism. -/
theorem coefficientSliceWeaklyContractible_of_wContractible
    (X : Scheme.{u}) (W : X.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R]
    (e : W.left ≅ Spec R) :
    AdicResidueSliceWeaklyContractible.{u, v} X (AsSmall.up.obj W) := by
  have : (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  let J := coefficientProEtaleModelTopology.{u, v} X
  let U : coefficientProEtaleSiteModel.{u, v} X := AsSmall.up.obj W
  have hweak : (J.over U).IsWeaklyContractible.{max v (u + 1)} (Over.mk (𝟙 U)) := by
    apply GrothendieckTopology.isWeaklyContractible_of_forall_mem
    intro S hS
    let S₀ := Sieve.overEquiv (Over.mk (𝟙 U)) S
    have hS₀ : S₀ ∈ J U := hS
    have hS₁ : S₀.functorPullback AsSmall.up ∈ ProEt.topology X W := by
      rw [← small_pushforward_eq_pullback X W S₀]
      exact (CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense
        (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt)
        (ProEt.topology X) S₀).mp hS₀
    obtain ⟨κ, V, g, s, hs, hV⟩ :=
      ProEt.exists_comp_sigmaDesc_eq_id_of_forall_exists_retraction
        (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) e hS₁
    obtain ⟨ι, Y, f, hcover, hmem, hmono, hdisj⟩ :=
      ProEt.exists_disjoint_cover_of_comp_sigmaDesc_eq_id g s hs _ hV
    let Y' (i : ι) : Over U := Over.mk (AsSmall.up.map (f i))
    let f' (i : ι) : Y' i ⟶ Over.mk (𝟙 U) := Over.homMk (AsSmall.up.map (f i))
    refine ⟨ι, Y', f', ?_, ?_, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      rw [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense
          (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt)
          (ProEt.topology X),
        Sieve.functorPushforward_ofArrows]
      exact hcover
    · intro i
      exact (Sieve.overEquiv_iff _ _).mp (hmem i)
    · intro i
      have := hmono i
      have : Mono (AsSmall.up.map (f i)) := inferInstance
      exact (Over.forget U).mono_of_mono_map inferInstance
    · intro i j hij Z a b hab
      rw [GrothendieckTopology.mem_over_iff]
      simp only [map_bot]
      rw [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense
        (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt)
        (ProEt.topology X)]
      have he := congrArg
        (fun k : Z ⟶ Over.mk (𝟙 U) ↦ AsSmall.down.map k.left) hab
      have he' : AsSmall.down.map a.left ≫ f i = AsSmall.down.map b.left ≫ f j := by
        dsimp [f', Over.homMk, AsSmall.up, AsSmall.down] at he
        exact he
      simpa only [Sieve.functorPushforward_bot] using
        hdisj i j hij (AsSmall.down.obj Z.left)
          (AsSmall.down.map a.left) (AsSmall.down.map b.left)
          he'
  intro F G φ hφ
  have : Epi φ := hφ
  exact hweak φ ((Sheaf.isLocallySurjective_iff_epi' (Type (max v (u + 1))) φ).mpr hφ)

/-- A Noetherian scheme has an affine, slice-weakly-contractible cover, each member
mapping into the connected component of a specified point of the base. The index lies
in the coefficient universe. Source: Stacks Tags 09C6, 0990 and 098F.
(auxiliary; not a blueprint node).

Proof: connected components of a locally Noetherian scheme are open and cover it.
Refine each component by spectra of w-contractible rings, then compose the covers.
The spectrum is affine; the preceding disjoint-refinement argument gives the slice
condition at the required universe. Its map factors through the component's open
immersion, so its image lies in that component. Empty schemes use the empty family. -/
theorem exists_coefficient_connected_contractible_cover
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ (I : Type (max v (u + 1)))
      (V : I → coefficientProEtaleSiteModel.{u, v} X)
      (f : ∀ i : I, V i ⟶
        (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      Sieve.ofArrows V f ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ i : I,
        IsAffine ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
          (V i)).left ∧
        AdicResidueSliceWeaklyContractible.{u, v} X (V i) ∧
        ∃ z : X, Set.range
          (((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj
            (V i)).hom.base) ⊆ connectedComponent z := by
  classical
  have : (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  let O (z : X) : X.Opens := ⟨connectedComponent z,
    TopologicalSpace.NoetherianSpace.isOpen_connectedComponent z⟩
  let U (z : X) : X.ProEt := ProEt.mk (O z).ι
  let T₀ : X.ProEt := ProEt.mk (𝟙 X)
  let hT₀ : IsTerminal T₀ := MorphismProperty.Over.mkIdTerminal _ _
  let g (z : X) : U z ⟶ T₀ := MorphismProperty.Over.homMk (O z).ι (by exact Category.comp_id _)
  have hU : Sieve.ofArrows U g ∈ ProEt.topology X T₀ := by
    apply ProEt.mem_topology_of_openImmersion _ (fun z ↦ (O z).ι)
    · intro z
      exact ⟨z, by rw [Opens.range_ι]; exact mem_connectedComponent⟩
    · intro z
      exact Sieve.ofArrows_mk U g z
  choose κ W h hcover hW using fun z : X ↦ (ProEt.weaklyContractible_basis X).1 (U z)
  let I := ULift.{max v (u + 1)} (Σ z : X, κ z)
  let V (i : I) : coefficientProEtaleSiteModel.{u, v} X :=
    AsSmall.up.obj (W i.down.1 i.down.2)
  let f (i : I) : V i ⟶ AsSmall.up.obj (⊤_ X.ProEt) :=
    AsSmall.up.map (terminal.from (W i.down.1 i.down.2))
  refine ⟨I, V, f, ?_, ?_⟩
  · rw [CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense
          (AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt)
          (ProEt.topology X),
      Sieve.functorPushforward_ofArrows]
    let W' (i : I) := W i.down.1 i.down.2
    let f' (i : I) : W' i ⟶ T₀ := h i.down.1 i.down.2 ≫ g i.down.1
    have hc : Sieve.ofArrows W' f' ∈ ProEt.topology X T₀ := by
      apply (ProEt.topology X).transitive hU
      rintro Y a ⟨_, b, _, ⟨z⟩, rfl⟩
      rw [Sieve.pullback_comp]
      apply (ProEt.topology X).pullback_stable b
      apply (ProEt.topology X).superset_covering _
        (Precoverage.generate_mem_toGrothendieck (hcover z))
      rintro Z c ⟨_, d, _, ⟨j⟩, rfl⟩
      have hm : Sieve.ofArrows W' f' (f' (ULift.up ⟨z, j⟩)) :=
        Sieve.ofArrows_mk W' f' (ULift.up ⟨z, j⟩)
      exact (Sieve.ofArrows W' f').downward_closed hm d
    have ht : (ProEt.topology X).CoversTop W' := by
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT₀]
      rw [← Sieve.ofArrows_eq_ofObjects hT₀ W' f']
      exact hc
    change Sieve.ofArrows W' (fun i ↦ terminal.from (W' i)) ∈ ProEt.topology X _
    rw [Sieve.ofArrows_eq_ofObjects terminalIsTerminal]
    exact ht _
  · intro i
    obtain ⟨R, hR, ⟨e⟩⟩ := hW i.down.1 i.down.2
    let := hR
    have : IsAffine (W i.down.1 i.down.2).left :=
      IsAffine.of_isIso e.inv
    refine ⟨this, coefficientSliceWeaklyContractible_of_wContractible X _ R e.symm,
      i.down.1, ?_⟩
    rintro _ ⟨y, rfl⟩
    have he := MorphismProperty.Over.w (h i.down.1 i.down.2)
    have hy := congrArg (fun k ↦ k.base y) he
    exact hy ▸ ((h i.down.1 i.down.2).left y).property

end AlgebraicGeometry.Scheme
