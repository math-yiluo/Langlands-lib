/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.Finite.FiniteExtensionTensorAlgebraicClosureReduced
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# Separability of global sections of a proper geometrically reduced scheme

The `k`-algebra structure on `Γ(X, ⊤)` is the structure map
`AlgebraicGeometry.Scheme.globalSectionsRingHom`, and the field structure is the one given by
`IsField` on the ring `Γ(X, ⊤)`, so both agree with the scheme's own ring structure.

## Implementation details

`A = Γ(X, ⊤)` is finite-dimensional over `k`. For an algebraic closure `k̄` of `k`, flat base
change identifies `A ⊗_k k̄` with `Γ(X_k̄, 𝒪)`, which is reduced since `X_k̄` is reduced; a
finite field extension whose tensor product with `k̄` is reduced is separable.

## References

* Stacks Project, Varieties, Lemma 0BUG (clause (4))
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `X` is proper and geometrically reduced over a field `k`, and the structure map makes
`A = Γ(X, ⊤)` a field extension of `k`, then `A/k` is separable. -/
theorem proper_geometricallyReduced_globalSections_isSeparable
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))]
    (hA : IsField Γ(X, ⊤)) :
    @Algebra.IsSeparableExtension k Γ(X, ⊤) _ hA.toField
      (Scheme.globalSectionsRingHom k (X := X)).toAlgebra := by
  let : Field Γ(X, ⊤) := hA.toField
  let : Algebra k Γ(X, ⊤) := (Scheme.globalSectionsRingHom k (X := X)).toAlgebra
  have : FiniteDimensional k Γ(X, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper
  -- Base change to an algebraic closure preserves reducedness.
  let K := AlgebraicClosure k
  let iX := X ↘ Spec (.of k)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hpb := IsPullback.of_hasPullback iX f
  have : IsReduced (Limits.pullback iX f) :=
    GeometricallyReduced.geometrically_isReduced f _ _ hpb
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace iX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated iX
  -- Flat base change identifies the global sections with a tensor product.
  have H := isPushout_appTop_of_flat f iX
  let A := Γ(X, ⊤)
  let B := Γ(Limits.pullback iX f, ⊤)
  let : Algebra K B :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop).hom.toAlgebra
  let : Algebra A B := (Limits.pullback.fst iX f).appTop.hom.toAlgebra
  let : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  have hw : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (algebraMap K B) =
      CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (algebraMap A B) := by
    change _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop) ≫ (Limits.pullback.fst iX f).appTop
    rw [reassoc_of% Scheme.ΓSpecIso_inv_naturality, Category.assoc, H.w]
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' congr($(hw).hom).symm
  have : Algebra.IsPushout k K A B := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    refine H.flip.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of K)) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
      simp [f]
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ iX.appTop
      simp
    · change _ = _ ≫ (Scheme.ΓSpecIso (.of K)).inv ≫ (Limits.pullback.snd iX f).appTop
      simp
    · simp
      rfl
  -- Transport reducedness across the pushout equivalence and tensor symmetry.
  have : _root_.IsReduced (TensorProduct k K A) :=
    isReduced_of_injective (Algebra.IsPushout.equiv k K A B).toRingHom
      (Algebra.IsPushout.equiv k K A B).injective
  have : _root_.IsReduced (TensorProduct k A K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A K).toRingHom
      (Algebra.TensorProduct.comm k A K).injective
  exact Algebra.finiteExtension_tensor_algebraicClosure_reduced_isSeparable k A K

end AlgebraicGeometry
