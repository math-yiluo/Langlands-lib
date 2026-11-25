/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity

/-!
# Galois orbits in a base-change fibre

The fibres of a Galois base change are single Galois orbits. This is the scheme-level
form of transitivity of a profinite group on primes above its invariant ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Galois transitivity on fibres is local on the original scheme.
Source: Stacks, Tag 038A; affine reduction as in Tag 038B.
(blueprint: lem-weil-pbc-galois-base-change-fiber-transitivity).

Proof: choose an affine cover member containing the common projection. Both points
lift to its base change, since the pullback of the open immersion has precisely the
inverse image as its range. Injectivity of the open immersion gives equality of the
lifted projections. Apply the affine transitivity theorem and use compatibility of
the Galois action with the map of pullbacks to obtain the equality globally. -/
theorem exists_galois_map_eq_of_projection_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (x y : ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hxy : (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x =
      (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y) :
    ∃ σ : K ≃ₐ[k] K,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) x = y  := by
  let f := X ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let i := X.affineCover.idx (pullback.fst f g x)
  let U := X.affineCover.X i
  let j : U ⟶ X := X.affineCover.f i
  let m : pullback (j ≫ f) g ⟶ pullback f g :=
    pullback.map (j ≫ f) g f g j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hrange : Set.range m = (pullback.fst f g) ⁻¹' Set.range j := by
    simpa [m] using Scheme.Pullback.range_map (j ≫ f) g f g j (𝟙 _) (𝟙 _)
      (show (j ≫ f) ≫ 𝟙 _ = j ≫ f by simp)
      (show g ≫ 𝟙 _ = 𝟙 _ ≫ g by simp)
  have hx : x ∈ Set.range m := by
    rw [hrange]
    exact X.affineCover.covers (pullback.fst f g x)
  have hy : y ∈ Set.range m := by
    rw [hrange]
    change pullback.fst f g y ∈ Set.range j
    rw [← hxy]
    exact X.affineCover.covers (pullback.fst f g x)
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  have hproj (z : ↥(pullback (j ≫ f) g)) :
      j (pullback.fst (j ≫ f) g z) = pullback.fst f g (m z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp [m]
  have hxy' : pullback.fst (j ≫ f) g x' = pullback.fst (j ≫ f) g y' := by
    apply j.isOpenEmbedding.injective
    rw [hproj, hproj, hx', hy']
    exact hxy
  obtain ⟨σ, hσ⟩ := exists_galois_map_eq_of_affine_projection_eq k K U (j ≫ f) x' y' hxy'
  have hcomm : baseChangeMap (j ≫ f) (specAlgEquivOver σ) ≫ m =
      m ≫ baseChangeMap f (specAlgEquivOver σ) := by
    apply pullback.hom_ext <;> simp [baseChangeMap, m, g, Category.assoc]
  refine ⟨σ, ?_⟩
  rw [← hx', ← hy']
  change (m ≫ baseChangeMap f (specAlgEquivOver σ)) x' = m y'
  rw [← hcomm, Scheme.Hom.comp_apply]
  exact congrArg m hσ


end AlgebraicGeometry
