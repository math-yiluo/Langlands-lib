/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Comparing affine fibre dimensions

## References

* Stacks Project, Tag 01I4 and Remark 00E6
* Stacks Project, Tag 01I4 (affine fibre products), Remark 00E6 (topology of the ring fibre)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem dimensionAt_inducing_le {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {g : A → B}
    (hg : Topology.IsInducing g) (a : A) :
    topologicalKrullDimAt a ≤ topologicalKrullDimAt (g a) := by
  refine le_iInf₂ fun U ha ↦ ?_
  let V : TopologicalSpace.Opens A := ⟨g ⁻¹' U, U.isOpen.preimage hg.continuous⟩
  exact (iInf₂_le V ha).trans
    ((hg.restrictPreimage (U : Set B)).topologicalKrullDim_le)

private theorem dimensionAt_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (a : A) :
    topologicalKrullDimAt a = topologicalKrullDimAt (e a) := by
  apply le_antisymm (dimensionAt_inducing_le e.isEmbedding.toIsInducing a)
  simpa using dimensionAt_inducing_le e.symm.isEmbedding.toIsInducing (e a)

/-- The local dimension of an affine scheme fibre equals that of the coordinate-ring fibre. -/
theorem affine_coordinate_fibre_dimension_eq
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T] (f : X ⟶ T) (y : X) :
    let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    let q : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom y
    topologicalKrullDimAt (f.asFiber y) =
      topologicalKrullDimAt
        ((PrimeSpectrum.preimageHomeomorphFiber Γ(T, ⊤) Γ(X, ⊤)
          (q.comap (algebraMap Γ(T, ⊤) Γ(X, ⊤)))) ⟨q, rfl⟩) := by
  let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let q : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom y
  let p := q.comap (algebraMap Γ(T, ⊤) Γ(X, ⊤))
  have hcomm (x : X) :
      (X.isoSpec.hom x).comap (algebraMap Γ(T, ⊤) Γ(X, ⊤)) = T.isoSpec.hom (f x) := by
    exact congrArg (fun k : X ⟶ Spec Γ(T, ⊤) ↦ k x) (X.isoSpec_hom_naturality f)
  let E : (f ⁻¹' {f y}) ≃ₜ
      (PrimeSpectrum.comap (algebraMap Γ(T, ⊤) Γ(X, ⊤)) ⁻¹' {p}) :=
    (Scheme.homeoOfIso X.isoSpec).subtype fun x ↦ by
      change f x = f y ↔ (X.isoSpec.hom x).comap _ = p
      rw [hcomm x, show p = T.isoSpec.hom (f y) from hcomm y]
      exact (Scheme.homeoOfIso T.isoSpec).injective.eq_iff.symm
  have h₁ := dimensionAt_homeomorph (f.fiberHomeo (f y)) (f.asFiber y)
  have h₂ := dimensionAt_homeomorph E (⟨y, rfl⟩ : f ⁻¹' {f y})
  have h₃ := dimensionAt_homeomorph
    (PrimeSpectrum.preimageHomeomorphFiber Γ(T, ⊤) Γ(X, ⊤) p) ⟨q, rfl⟩
  simp only [Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] at h₁
  exact h₁.trans (h₂.trans h₃)

end AlgebraicGeometry
