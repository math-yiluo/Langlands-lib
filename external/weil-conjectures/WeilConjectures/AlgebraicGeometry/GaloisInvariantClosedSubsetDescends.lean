/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity

/-!
# Descent of Galois-invariant closed subsets

Source: Stacks Project, Varieties, Tag 038B, Lemma `lemma-closed-fixed-by-Galois`,
and equation `equation-galois-action-base-change-kbar`
(blueprint: lem-weil-pbc-galois-invariant-closed-subset-descends).

The base change is the chosen fibre product, with `pullback.fst` as its projection to `X`.
The existing `specAlgEquivOver` and `baseChangeMap` give the contravariant Galois action.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection of a Galois field base change is a closed map.
Source: Mathlib, integral morphisms and stability of universal closedness under base change.
(blueprint: lem-weil-pbc-galois-base-change-closed-map).
Proof: a Galois extension is algebraic, hence integral; its spectrum map is integral and
universally closed, and universal closedness is preserved by base change. -/
theorem isClosedMap_pullback_fst_of_isGalois
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    IsClosedMap (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    IsIntegralHom.SpecMap_iff.mpr
      (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral k K))
  exact (pullback.fst (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isClosedMap

/-- (blueprint: lem-weil-pbc-galois-invariant-closed-subset-descends) -/
theorem exists_closed_subset_of_galois_invariant
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Tbar : Set ↥(pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hclosed : IsClosed Tbar)
    (hinvariant : ∀ σ : K ≃ₐ[k] K,
      (baseChangeMap (X ↘ Spec (.of k)) (specAlgEquivOver σ)) '' Tbar = Tbar) :
    ∃ T : Set X, IsClosed T ∧
      (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T = Tbar := by
  let p := pullback.fst (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    IsIntegralHom.SpecMap_iff.mpr
      (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral k K))
  have hp : IsClosedMap p := isClosedMap_pullback_fst_of_isGalois k K X
  refine ⟨p '' Tbar, hp Tbar hclosed, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨σ, hσ⟩ := exists_galois_map_eq_of_projection_eq k K X x y hxy
    rw [← hinvariant σ]
    exact ⟨x, hx, hσ⟩
  · intro hy
    exact ⟨y, hy, rfl⟩

end AlgebraicGeometry
