/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.Etale.Weakly

/-!
# Weakly étale morphisms of affine schemes

For an `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is weakly étale if and only if `S` is a
weakly étale `R`-algebra: it is flat if and only if `S` is flat over `R`, and its diagonal is
the spectrum of the multiplication `S ⊗[R] S → S`.

A weakly étale morphism `f : V ⟶ Spec K` to the spectrum of an algebraically closed field with
nonempty source has a section: an affine open of `V` is the spectrum of a nonzero weakly étale
`K`-algebra, which has a `K`-point
(`Algebra.WeaklyEtale.nonempty_algHom_of_isAlgClosed`).

## Main results

- `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`
- `AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale`: a weakly étale scheme over an
  algebraically closed field `K` with a point has a `K`-point.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- For a weakly étale `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is weakly étale. -/
instance weaklyEtale_SpecMap_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.WeaklyEtale R S] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have hflat : RingHom.Flat (algebraMap R S) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat
  have : Flat (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (Algebra.WeaklyEtale.flat_lmul' R S)
  refine ⟨inferInstance, ?_⟩
  rw [diagonal_SpecMap]
  infer_instance

/-- For an `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is weakly étale if and only if `S` is
a weakly étale `R`-algebra. -/
theorem weaklyEtale_SpecMap_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔ Algebra.WeaklyEtale R S := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun _ ↦ inferInstance⟩
  · rw [← RingHom.flat_algebraMap_iff]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (algebraMap R S))).1 h.flat
  · have e : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom) =
        Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          (pullbackSpecIso R S S).hom := by
      rw [diagonal_SpecMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) := by
      rw [e]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this

/-- A weakly étale scheme `V` over an algebraically closed field `K` with a point has a
`K`-point: a section of `f : V ⟶ Spec K`. An affine open neighbourhood of the point is the
spectrum of a nonzero weakly étale `K`-algebra, which has a `K`-algebra map to `K`
(`Algebra.WeaklyEtale.nonempty_algHom_of_isAlgClosed`). -/
theorem exists_comp_eq_id_of_weaklyEtale {K : Type u} [Field K] [IsAlgClosed K] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of K)) [WeaklyEtale f] (v : V) :
    ∃ σ : Spec (.of K) ⟶ V, σ ≫ f = 𝟙 _ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hv, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have : Nonempty U := ⟨⟨v, hv⟩⟩
  let φ := Spec.preimage (hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f)
  let := φ.hom.toAlgebra
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K Γ(V, U)))) := by
    change WeaklyEtale (Spec.map φ)
    rw [Spec.map_preimage]
    infer_instance
  have := weaklyEtale_SpecMap_algebraMap_iff.1 this
  obtain ⟨ψ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isAlgClosed (K := K) (R := Γ(V, U))
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U, ?_⟩
  have hφ : hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f = Spec.map φ := (Spec.map_preimage _).symm
  rw [Category.assoc, Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact ψ.commutes x

end AlgebraicGeometry
