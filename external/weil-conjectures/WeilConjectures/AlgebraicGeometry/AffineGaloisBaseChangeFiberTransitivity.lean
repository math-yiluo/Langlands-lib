/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.TensorGaloisPrimeTransitivity

/-!
# Galois orbits in an affine base-change fibre

The fibres of a Galois base change are single Galois orbits. This is the scheme-level
form of transitivity of a profinite group on primes above its invariant ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two points of a Galois base change with the same projection differ by a Galois
 automorphism. No closed subset, finiteness of the extension, or finite-type assumption
 on the scheme is required.

Source: Mathlib, `RingTheory/Invariant/Profinite.lean`,
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`; Stacks, Tag 0BRI for the
finite-group case, and Tag 038A for the contravariant scheme action.
(blueprint: lem-weil-pbc-affine-galois-base-change-fiber-transitivity).

Proof:
1. Write the affine scheme as `Spec A`, using its canonical `isoSpec`, and give `A`
   its `k`-algebra structure through the ring map corresponding to `f`. The pullback
   is `Spec (A ⊗[k] K)`, by `pullbackSpecIso`. The two points correspond to prime
   ideals with the same contraction to `A`; the action is `Spec (id_A ⊗ σ)`.
2. Equip `G = Aut(K/k)` with its Krull topology, which is profinite for any Galois
   algebraic extension, including an infinite one. Equip `A ⊗[k] K` with the discrete
   topology and let `G` act on the right tensor factor. Each tensor is a finite sum of
   pure tensors. The subgroup fixing its finitely many right-hand coefficients is
   open, so the action is continuous. The action commutes with the `A`-scalars.
3. The fixed field of `G` is `k`. Apply
   `TensorProduct.injective_and_range_eq_invariants` with the full automorphism group
   to the underlying vector space of `A`. Thus the invariant ring of the tensor
   product is precisely the image of `A`, giving `Algebra.IsInvariant A (A ⊗[k] K) G`.
4. Apply `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` to the two primes.
   Its ideal action is direct image under the ring automorphism, whereas `Spec` uses
   inverse image. Replace the supplied automorphism by its inverse. Transport the
   resulting equality through the affine comparison. This gives exactly the displayed
   equality of points. -/
theorem exists_galois_map_eq_of_affine_projection_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k))
    (x y : ↥(pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hxy : (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x =
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) :
    ∃ σ : K ≃ₐ[k] K,
      (baseChangeMap f (specAlgEquivOver σ)) x = y := by
  let A := Γ(X, ⊤)
  let φ : CommRingCat.of k ⟶ A :=
    (Spec.fullyFaithful.preimage (X.isoSpec.inv ≫ f)).unop
  let : Algebra k A := φ.hom.toAlgebra
  let a := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have ha : X.isoSpec.inv ≫ f = a := by
    exact (Spec.fullyFaithful.map_preimage (X.isoSpec.inv ≫ f)).symm
  have ha' : f = X.isoSpec.hom ≫ a := by
    rw [← ha, ← Category.assoc, X.isoSpec.hom_inv_id, Category.id_comp]
  let j : pullback f b ≅ pullback a b :=
    { hom := pullback.map f b a b X.isoSpec.hom (𝟙 _) (𝟙 _)
        (by simpa using ha') (by simp)
      inv := pullback.map a b f b X.isoSpec.inv (𝟙 _) (𝟙 _)
        (by simpa using ha.symm) (by simp)
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let e := j ≪≫ pullbackSpecIso k A K
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom) =
      pullback.fst f b ≫ X.isoSpec.hom := by
    change j.hom ≫ (pullbackSpecIso k A K).hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    rw [pullbackSpecIso_hom_fst]
    change j.hom ≫ pullback.fst a b = _
    simp [j]
  have hcon : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom (e.hom x) =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom (e.hom y) := by
    have hx := congrArg (fun q ↦ q x) he
    have hy := congrArg (fun q ↦ q y) he
    change PrimeSpectrum.comap _ (e.hom x) = X.isoSpec.hom ((pullback.fst f b) x) at hx
    change PrimeSpectrum.comap _ (e.hom y) = X.isoSpec.hom ((pullback.fst f b) y) at hy
    exact hx.trans ((congrArg X.isoSpec.hom hxy).trans hy.symm)
  obtain ⟨σ, hσ⟩ := Algebra.TensorProduct.exists_comap_eq_of_galois k K A
    (e.hom x) (e.hom y) hcon
  refine ⟨σ, ?_⟩
  have he₁ : e.inv ≫ pullback.fst f b = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom) ≫
      X.isoSpec.inv := by
    rw [← cancel_mono X.isoSpec.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← he, Iso.inv_hom_id_assoc]
  have he₂ : e.inv ≫ pullback.snd f b = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : K →ₐ[k] TensorProduct k A K).toRingHom) := by
    change (pullbackSpecIso k A K).inv ≫ j.inv ≫ pullback.snd f b = _
    have hj : j.inv ≫ pullback.snd f b = pullback.snd a b := by simp [j]
    rw [hj]
    exact pullbackSpecIso_inv_snd k A K
  let m := Algebra.TensorProduct.map (AlgHom.id k A) σ.toAlgHom
  have hm₁ : Spec.map (CommRingCat.ofHom m.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A K).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext a
    simp [m, Algebra.TensorProduct.includeLeft_apply]
  have hm₂ : Spec.map (CommRingCat.ofHom m.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] TensorProduct k A K).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] TensorProduct k A K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
  have haction : baseChangeMap f (specAlgEquivOver σ) ≫ e.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id k A) σ.toAlgHom).toRingHom) := by
    rw [← cancel_mono e.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · change baseChangeMap f (specAlgEquivOver σ) ≫ pullback.fst f b =
        (e.hom ≫ Spec.map (CommRingCat.ofHom m.toRingHom) ≫ e.inv) ≫
          pullback.fst f b
      simp only [Category.assoc]
      rw [he₁, ← Category.assoc _ _ X.isoSpec.inv, hm₁]
      rw [← Category.assoc, he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      change baseChangeMap f (specAlgEquivOver σ) ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) = _
      exact baseChangeMap_fst f (specAlgEquivOver σ)
    · change baseChangeMap f (specAlgEquivOver σ) ≫ pullback.snd f b =
        (e.hom ≫ Spec.map (CommRingCat.ofHom m.toRingHom) ≫ e.inv) ≫
          pullback.snd f b
      simp only [Category.assoc]
      rw [he₂, hm₂]
      have he₂' : e.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : K →ₐ[k] TensorProduct k A K).toRingHom) =
          pullback.snd f b := by
        rw [← he₂, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, he₂']
      exact baseChangeMap_snd f (specAlgEquivOver σ)
  apply e.hom.homeomorph.injective
  have hx := congrArg (fun q ↦ q x) haction
  change e.hom ((baseChangeMap f (specAlgEquivOver σ)) x) =
    PrimeSpectrum.comap _ (e.hom x) at hx
  exact hx.trans hσ

end AlgebraicGeometry
