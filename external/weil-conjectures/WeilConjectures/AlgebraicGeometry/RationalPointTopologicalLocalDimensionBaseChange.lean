/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension

/-! Auxiliary reductions for rational point local dimension base change. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) (_hX : Nonempty X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  apply le_antisymm
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens X := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
    refine (iInf₂_le V hx).trans ?_
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun p : V ↦ (⟨f p.1, p.2⟩ : U))
      (.of_comp (g := Subtype.val) (by fun_prop) ?_ ?_)
    · exact continuous_subtype_val
    · exact hf.toIsInducing.comp Topology.IsInducing.subtypeVal
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens Y := ⟨f '' U, hf.isOpenMap _ U.isOpen⟩
    let g : U → Y := fun p ↦ f p.1
    have hg : Topology.IsEmbedding g := hf.toIsEmbedding.comp
      Topology.IsEmbedding.subtypeVal
    have hr : Set.range g = (V : Set Y) := by
      ext y
      simp [g, V, Set.mem_image]
    refine (iInf₂_le V ⟨x, hx, rfl⟩).trans_eq ?_
    rw [hg.topologicalKrullDim_eq_range, hr]
    rfl


/-- The topological local dimensions at compatible rational points are preserved by scalar
extension.

Source: Stacks Project, Lemma 10.116.6, Tag 00P4.
Proof: Write x for the image of the unique point under p, and y for its image under q.
The compatibility hqp implies that the first pullback projection takes y to x. Choose
an affine open U = Spec A containing x. The restriction of f gives a finite type
k-algebra structure on A, since f is locally of finite type and Spec k is affine.
Its inverse image V in the pullback is open, contains y, and is canonically isomorphic
to Spec (A tensor_k K). Under these identifications the first projection is the prime
contraction along a -> a tensor 1, so the prime corresponding to y contracts to the
prime corresponding to x. Apply topologicalKrullDimAt_spec_tensorProduct_field_extension
to this upper prime. Finally, open immersions preserve local topological dimension:
open neighbourhoods contained in an open chart are cofinal among all neighbourhoods,
and the chart isomorphisms give homeomorphisms. Transport the affine equality through
these two charts. Neither maximality nor reducedness nor separatedness is used.
(blueprint: lem-ag-rational-point-topological-local-dimension-base-change)
-/
theorem topologicalKrullDimAt_rationalPoint_field_baseChange
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (K : Type u) [Field K] [Algebra k K]
    (q : Spec (.of K) ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hq : q ≫ pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) = 𝟙 _)
    (hqp : q ≫ pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ p) :
    topologicalKrullDimAt (p (IsLocalRing.closedPoint k)) =
      topologicalKrullDimAt (q (IsLocalRing.closedPoint K)) := by
  have _ := hp
  have _ := hq
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let y := q (IsLocalRing.closedPoint K)
  let x := p (IsLocalRing.closedPoint k)
  have hxy : pullback.fst f g y = x := by
    change (q ≫ pullback.fst f g) (IsLocalRing.closedPoint K) = x
    rw [hqp, Scheme.Hom.comp_apply]
    exact congrArg p (Subsingleton.elim _ _)
  obtain ⟨R, a, ha, ⟨z, hz⟩, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : IsOpenImmersion a := ha
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ f)
  have hft : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
  have hft' : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp hft
  let : Algebra k R := φ.hom.toAlgebra
  let : Algebra.FiniteType k R := hft'
  have hy : y ∈ Set.range (pullback.snd a (pullback.fst f g)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    change pullback.fst f g y ∈ Set.range a
    rw [hxy]
    exact ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hy
  let e := pullbackRightPullbackFstIso f g a ≪≫ pullback.congrHom hφ.symm rfl ≪≫
    pullbackSpecIso k R K
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K))) =
        pullback.fst a (pullback.fst f g) := by
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, Category.assoc, pullbackSpecIso_hom_fst]
    change (pullbackRightPullbackFstIso f g a).hom ≫
      (pullback.congrHom hφ.symm rfl).hom ≫ pullback.fst (Spec.map φ) g = _
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst]
  have hwz : pullback.fst a (pullback.fst f g) w = z := by
    apply a.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw, hxy, hz]
  have hd := topologicalKrullDimAt_spec_tensorProduct_field_extension (e.hom w)
  have hew : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K))
      (e.hom w) = z := by
    change (e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := R) (B := K)))) w = z
    rw [he]
    exact hwz
  rw [hew] at hd
  calc
    topologicalKrullDimAt x = topologicalKrullDimAt z :=
      hz ▸ (localDim_openEmbedding a.isOpenEmbedding z ⟨z⟩).symm
    _ = topologicalKrullDimAt (e.hom w) := hd
    _ = topologicalKrullDimAt w :=
      (localDim_openEmbedding e.hom.isOpenEmbedding w ⟨w⟩).symm
    _ = topologicalKrullDimAt y :=
      hw ▸ localDim_openEmbedding (pullback.snd a (pullback.fst f g)).isOpenEmbedding w ⟨w⟩


end AlgebraicGeometry
