/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.Dimension
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers

/-!
# Dimension under field extension and base change

Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-dim-base-change.md`,
node order 733; Stacks Project, Tag 00P3 (blueprint: lem-pc-dim-base-change).
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem ring_dim_base_change
    (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (A ⊗[k] K) = ringKrullDim A := by
  have h := topologicalKrullDim_spec_tensorProduct_of_field_extension k K A
  change topologicalKrullDim (PrimeSpectrum (K ⊗[k] A)) =
    topologicalKrullDim (PrimeSpectrum A) at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  rw [← h]
  exact RingEquiv.ringKrullDim (Algebra.TensorProduct.comm k A K).toRingEquiv

/-- Dimension is unchanged by scalar extension, and curves remain one-dimensional.
Source: blueprint `sec-picard-framework/sk-thm-picard-rr/lem-pc-dim-base-change.md`,
node order 733; Stacks Project, Tags 00P3 and 04MU (blueprint: lem-pc-dim-base-change).

Proof:
1. Apply `lem-weil-pbc-dimension-preserved-field-extension` (00P3) to `A`: Noether
   normalization gives a finite injective polynomial algebra map, which remains finite
   and injective after the flat extension to `K`; integral extensions preserve dimension.
   By `def-weil-pbc-krull-dimension-ring`, spectrum dimension is ring dimension. Swap
   the tensor factors using the ring isomorphism; prime ideals and inclusions correspond.
2. By `def-pc-curve`, `X` is integral, nonempty, separated and of finite type, with
   dimension one. By `def-weil-finite-type-morphism`, choose a finite affine open cover
   by spectra of finite type algebras (`def-weil-pbc-finite-type-algebra`). Its inverse
   images cover the pullback (`def-pc-base-change`); `lem-weil-pbc-open-fibre-product`
   (01JR) and `lem-weil-pbc-fibre-product-affine-spectra` (01JQ) identify them with the
   spectra of the scalar extensions. Some chart is nonzero; step 1 shows its scalar
   extension has nonnegative dimension and is nonzero, so the pullback is nonempty.
3. Apply `lem-pc-dimension-affine-open-cover` (04MU) to both nonempty schemes. Their
   dimensions are the maxima of the chart dimensions, which agree by step 1, hence one.
-/
theorem dim_base_change :
    (∀ (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [Algebra.FiniteType k A],
      ringKrullDim (A ⊗[k] K) = ringKrullDim A) ∧
    (∀ (k K : Type z) [Field k] [Field K] [Algebra k K]
      {X : Scheme.{z}} (f : X ⟶ Spec (.of k)) [IsIntegralCurve f],
      Scheme.dim (Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = 1) := by
  constructor
  · intro k K A _ _ _ _ _ _
    exact ring_dim_base_change k K A
  · intro k K _ _ _ X f _
    let : IsIntegral X := IsVariety.isIntegral (f := f)
    obtain ⟨hY, I, A, rings, algebras, hft, U, V, hU, hV, ⟨eU⟩, ⟨eV⟩⟩ :=
      exists_field_baseChange_affine_covers k K f
    let := rings
    let := algebras
    let := hft
    let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let : Nonempty Y := hY
    have hX := Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover X U hU
      (fun i ↦ CommRingCat.of (A i)) eU
    have hdim := Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover Y V hV
      (fun i ↦ CommRingCat.of (A i ⊗[k] K)) eV
    calc
      Y.dim = ⨆ i, ringKrullDim (A i ⊗[k] K) := hdim
      _ = ⨆ i, ringKrullDim (A i) := by
        congr 1
        funext i
        exact ring_dim_base_change k K (A i)
      _ = X.dim := hX.symm
      _ = 1 := by
        rw [Scheme.dim_eq_topologicalKrullDim]
        exact IsIntegralCurve.topologicalKrullDim_eq_one (f := f)

end AlgebraicGeometry
