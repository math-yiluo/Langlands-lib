/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Base change to a field does not increase the dimension

The base change of a finitely generated algebra over a field to a larger field does not increase
the Krull dimension (`ringKrullDim_tensorProduct_le_of_finiteType`). Globalising, the base change
of a scheme locally of finite type over a field to a larger field has no larger dimension, and
hence for `f : X ⟶ Y` locally of finite type and a point `Spec K ⟶ Y` with values in a field,
`X ×_Y Spec K` has dimension at most `dim X`.

## Main statements

- `AlgebraicGeometry.topologicalKrullDim_pullback_le_of_field`: base change of a scheme locally
  of finite type over a field `k` to a field extension of `k` does not increase the dimension.
- `AlgebraicGeometry.topologicalKrullDim_pullback_eq_of_field`: base change of a scheme locally
  of finite type over a field `k` to a field extension of `k` preserves the dimension.
- `AlgebraicGeometry.topologicalKrullDim_pullback_le`: `dim (X ×_Y Spec K) ≤ dim X` for
  `X ⟶ Y` locally of finite type.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- The affine case of `topologicalKrullDim_pullback_le_of_field`: for `Spec A` of finite type
over a field `k` and a field `K` over `k`, `Spec (A ⊗[k] K)` has dimension at most `dim A`. -/
theorem topologicalKrullDim_pullback_le_of_field_of_spec {k K : Type u} [Field k] [Field K]
    {A : CommRingCat.{u}} (p : Spec A ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) ≤ topologicalKrullDim (Spec A) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective q
  have hφ : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom, ψ.hom]
  calc topologicalKrullDim (pullback (Spec.map φ) (Spec.map ψ) : Scheme.{u})
      _ = topologicalKrullDim (Spec (.of (A ⊗[k] K))) :=
        IsHomeomorph.topologicalKrullDim_eq _ (pullbackSpecIso k A K).hom.homeomorph.isHomeomorph
      _ = ringKrullDim (A ⊗[k] K) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ ringKrullDim A := ringKrullDim_tensorProduct_le_of_finiteType k A K
      _ = topologicalKrullDim (Spec A) := (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm

/-- **Base change to a field extension does not increase dimension.** For a scheme `Z` locally of
finite type over a field `k` and a field `K` over `k`, `dim (Z ×_k K) ≤ dim Z`: on an affine
open `Spec A` of `Z` this is `dim (A ⊗[k] K) ≤ dim A`. -/
theorem topologicalKrullDim_pullback_le_of_field {Z : Scheme.{u}} {k K : Type u} [Field k]
    [Field K] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) ≤ topologicalKrullDim Z := by
  let 𝒰 := Z.affineCover
  let j i := pullback.snd (𝒰.f i) (pullback.fst p q)
  refine topologicalKrullDim_le_of_iSup_eq_top (fun i ↦ (j i).opensRange) ?_ _ fun i ↦ ?_
  · refine eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (𝒰.iUnion_range.ge (Set.mem_univ (pullback.fst p q z)))
    refine ⟨i, ?_⟩
    rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, Scheme.Pullback.range_snd]
    exact hi
  · calc topologicalKrullDim (j i).opensRange
        _ = topologicalKrullDim (pullback (𝒰.f i) (pullback.fst p q) : Scheme) :=
          (j i).isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm
        _ = topologicalKrullDim (pullback (𝒰.f i ≫ p) q : Scheme) :=
          IsHomeomorph.topologicalKrullDim_eq _
          (pullbackRightPullbackFstIso p q (𝒰.f i)).hom.homeomorph.isHomeomorph
        _ ≤ topologicalKrullDim (𝒰.X i) := topologicalKrullDim_pullback_le_of_field_of_spec _ q
        _ ≤ topologicalKrullDim Z := (𝒰.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The affine case of `topologicalKrullDim_pullback_eq_of_field`: for `Spec A` of finite type
over a field `k` and a field `K` over `k`, `Spec (A ⊗[k] K)` has the same dimension as `A`. -/
theorem topologicalKrullDim_pullback_eq_of_field_of_spec {k K : Type u} [Field k] [Field K]
    {A : CommRingCat.{u}} (p : Spec A ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) = topologicalKrullDim (Spec A) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective q
  have hφ : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom, ψ.hom]
  calc topologicalKrullDim (pullback (Spec.map φ) (Spec.map ψ) : Scheme.{u})
      _ = topologicalKrullDim (Spec (.of (A ⊗[k] K))) :=
        IsHomeomorph.topologicalKrullDim_eq _ (pullbackSpecIso k A K).hom.homeomorph.isHomeomorph
      _ = ringKrullDim (A ⊗[k] K) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ = ringKrullDim A := ringKrullDim_tensorProduct_of_finiteType k A K
      _ = topologicalKrullDim (Spec A) := (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm

/-- **Base change to a field extension preserves dimension.** For a scheme `Z` locally of finite
type over a field `k` and a field `K` over `k`, `dim (Z ×_k K) = dim Z`; for instance the base
change `X_K` of a curve `X` over `k` has dimension `1`. On an affine open `Spec A` of `Z` this is
`dim (A ⊗[k] K) = dim A` (`ringKrullDim_tensorProduct_of_finiteType`).

(blueprint: `lem-pc-dim-base-change`) -/
theorem topologicalKrullDim_pullback_eq_of_field {Z : Scheme.{u}} {k K : Type u} [Field k]
    [Field K] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (q : Spec (.of K) ⟶ Spec (.of k)) :
    topologicalKrullDim (pullback p q : Scheme.{u}) = topologicalKrullDim Z := by
  refine le_antisymm (topologicalKrullDim_pullback_le_of_field p q) ?_
  let 𝒰 := Z.affineCover
  refine topologicalKrullDim_le_of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange)
    𝒰.iSup_opensRange _ fun i ↦ ?_
  calc topologicalKrullDim (𝒰.f i).opensRange
      _ = topologicalKrullDim (𝒰.X i) :=
        (𝒰.f i).isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm
      _ = topologicalKrullDim (pullback (𝒰.f i ≫ p) q : Scheme) :=
        (topologicalKrullDim_pullback_eq_of_field_of_spec _ q).symm
      _ = topologicalKrullDim (pullback (𝒰.f i) (pullback.fst p q) : Scheme) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (pullbackRightPullbackFstIso p q (𝒰.f i)).inv.homeomorph.isHomeomorph
      _ ≤ topologicalKrullDim (pullback p q : Scheme) :=
        (pullback.snd (𝒰.f i) (pullback.fst p q)).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- **Fibres over field-valued points have dimension at most that of the source.** For
`f : X ⟶ Y` locally of finite type and `s : Spec K ⟶ Y` with `K` a field,
`dim (X ×_Y Spec K) ≤ dim X`: `s` factors through `Spec κ(y)` for `y` its image point, so
`X ×_Y Spec K` is the base change of the fibre `f⁻¹(y)` along `κ(y) → K`.

Used for blueprint `sk-prop-sf-fullcd-etale-origin`: the geometric fibres of base changes of `X`
have dimension at most `dim X`. -/
theorem topologicalKrullDim_pullback_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y) :
    topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ topologicalKrullDim X := by
  obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
  calc topologicalKrullDim (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u})
      _ = topologicalKrullDim (pullback (pullback.snd f (Y.fromSpecResidueField y)) (Spec.map t) :
          Scheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
          (Y.fromSpecResidueField y) (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim (f.fiber y) :=
        topologicalKrullDim_pullback_le_of_field (k := Y.residueField y) _ _
      _ = topologicalKrullDim (f ⁻¹' {y}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
      _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le _ _

/-- **Dimension of a field-valued fibre.** For `f : X ⟶ Y` locally of finite type and
`s : Spec K ⟶ Y` with `K` a field, lying over `y ∈ Y`, `dim (X ×_Y Spec K) ≤ dim f⁻¹(y)`:
`X ×_Y Spec K` is the base change of the fibre `f⁻¹(y)` along `κ(y) → K`. -/
theorem topologicalKrullDim_pullback_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y) :
    topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤
      topologicalKrullDim (f ⁻¹' {s.base (IsLocalRing.closedPoint K)}) := by
  obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective s
  have hy : ((Scheme.SpecToEquivOfField K Y).symm ⟨y, t⟩).base (IsLocalRing.closedPoint K) = y := by
    simp [Scheme.SpecToEquivOfField_symm_apply]
  calc topologicalKrullDim (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u})
      _ = topologicalKrullDim (pullback (pullback.snd f (Y.fromSpecResidueField y)) (Spec.map t) :
          Scheme) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
          (Y.fromSpecResidueField y) (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim (f.fiber y) :=
        topologicalKrullDim_pullback_le_of_field (k := Y.residueField y) _ _
      _ = _ := by
        rw [hy]
        exact IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph

end AlgebraicGeometry
