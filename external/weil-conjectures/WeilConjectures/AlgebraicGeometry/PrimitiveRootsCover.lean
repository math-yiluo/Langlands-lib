/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Adjoining a primitive root of unity

For a commutative ring `B` and `n ∈ ℕ`, the `B`-algebra
`B[ζ] = B[T]/(Tⁿ - 1)[(1 - ζᵏ)⁻¹, 0 < k < n]` (`AlgebraicGeometry.PrimitiveRootsAlgebra`) is
the universal `B`-algebra with an `n`-th root of unity `ζ` all of whose differences
`ζ ^ i - ζ ^ j`, `i ≠ j < n`, are invertible. When `n` is invertible in `B` it is étale over `B`,
and every separably closed point of `Spec B` lifts to it: a primitive `n`-th root of unity of
the separably closed field is such a root. So `Spec B[ζ] ⟶ Spec B` is an étale cover over which
the sheaf of `n`-th roots of unity becomes constant
(`AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub`).

## Main definitions

- `AlgebraicGeometry.PrimitiveRootsAlgebra`: the algebra `B[ζ]`.
- `AlgebraicGeometry.PrimitiveRootsAlgebra.zeta`: the root of unity `ζ`.

## Main statements

- `AlgebraicGeometry.PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow`: the differences of
  the powers of `ζ` are invertible.
- `AlgebraicGeometry.PrimitiveRootsAlgebra.etale`: `B[ζ]` is étale over `B` when `n` is
  invertible in `B`.
- `AlgebraicGeometry.PrimitiveRootsAlgebra.exists_lift`: ring homomorphisms from `B` to a
  separably closed field in which `n` is invertible extend to `B[ζ]`.
-/

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry

variable (B : Type u) [CommRing B] (n : ℕ)

/-- The element `∏_{0 < k < n} (1 - ζᵏ)` of `B[T]/(Tⁿ - 1)`, `ζ` being the class of `T`. -/
noncomputable abbrev PrimitiveRootsAlgebra.denominator : AdjoinRoot (X ^ n - C (1 : B)) :=
  ∏ k ∈ Finset.Ioo 0 n, (1 - AdjoinRoot.root (X ^ n - C (1 : B)) ^ k)

/-- The `B`-algebra `B[ζ] = B[T]/(Tⁿ - 1)[(1 - ζᵏ)⁻¹, 0 < k < n]`: the universal `B`-algebra
with an `n`-th root of unity `ζ` whose powers have invertible differences. -/
abbrev PrimitiveRootsAlgebra : Type u :=
  Localization.Away (PrimitiveRootsAlgebra.denominator B n)

namespace PrimitiveRootsAlgebra

/-- The `n`-th root of unity `ζ` of `B[ζ]`. -/
noncomputable def zeta : PrimitiveRootsAlgebra B n :=
  algebraMap (AdjoinRoot (X ^ n - C (1 : B))) _ (AdjoinRoot.root _)

lemma zeta_pow : zeta B n ^ n = 1 := by
  have h : AdjoinRoot.root (X ^ n - C (1 : B)) ^ n = 1 := by
    have := AdjoinRoot.eval₂_root (X ^ n - C (1 : B))
    simpa [sub_eq_zero] using this
  rw [zeta, ← map_pow, h, map_one]

lemma isUnit_one_sub_zeta_pow {k : ℕ} (hk₀ : 0 < k) (hkn : k < n) :
    IsUnit (1 - zeta B n ^ k) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := PrimitiveRootsAlgebra B n)
    (denominator B n)
  change IsUnit (algebraMap _ _ (∏ k ∈ Finset.Ioo 0 n,
    (1 - AdjoinRoot.root (X ^ n - C (1 : B)) ^ k))) at h
  rw [map_prod, IsUnit.prod_iff] at h
  simpa [zeta] using h k (Finset.mem_Ioo.2 ⟨hk₀, hkn⟩)

lemma isUnit_zeta (hn : 0 < n) : IsUnit (zeta B n) :=
  isUnit_iff_exists_inv.2 ⟨zeta B n ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn, zeta_pow]⟩

/-- The differences `ζ ^ i - ζ ^ j`, `i ≠ j < n`, are invertible in `B[ζ]`. -/
lemma isUnit_zeta_pow_sub_zeta_pow {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    IsUnit (zeta B n ^ i - zeta B n ^ j) := by
  have hn : 0 < n := (Nat.zero_le i).trans_lt hi
  have hζ := isUnit_zeta B n hn
  rcases lt_or_gt_of_ne hij with h | h
  · have e : zeta B n ^ i - zeta B n ^ j = zeta B n ^ i * (1 - zeta B n ^ (j - i)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [e]
    exact (hζ.pow i).mul (isUnit_one_sub_zeta_pow B n (Nat.sub_pos_of_lt h)
      ((Nat.sub_le j i).trans_lt hj))
  · have e : zeta B n ^ i - zeta B n ^ j = -(zeta B n ^ j * (1 - zeta B n ^ (i - j))) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le, neg_sub]
    rw [e]
    exact ((hζ.pow j).mul (isUnit_one_sub_zeta_pow B n (Nat.sub_pos_of_lt h)
      ((Nat.sub_le i j).trans_lt hi))).neg

/-- `B[ζ]` is étale over `B` when `n ≠ 0` is invertible in `B`: it is a localization of the
Kummer algebra `B[T]/(Tⁿ - 1)`. -/
theorem etale (hn₀ : n ≠ 0) (hn : IsUnit (n : B)) :
    Algebra.Etale B (PrimitiveRootsAlgebra B n) := by
  have : Algebra.Etale B (AdjoinRoot (X ^ n - C (1 : B))) :=
    AdjoinRoot.etale_X_pow_sub_C hn₀ hn isUnit_one
  infer_instance

/-- A ring homomorphism from `B` to a separably closed field `Ω` in which `n` is invertible
extends to `B[ζ]`, by sending `ζ` to a primitive `n`-th root of unity of `Ω`. -/
theorem exists_lift {Ω : Type*} [Field Ω] [IsSepClosed Ω] [NeZero (n : Ω)] (φ : B →+* Ω) :
    ∃ ψ : PrimitiveRootsAlgebra B n →+* Ω, ψ.comp (algebraMap B _) = φ := by
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  have hroot : eval₂ φ ξ (X ^ n - C (1 : B)) = 0 := by
    simp [hξ.pow_eq_one]
  let f : AdjoinRoot (X ^ n - C (1 : B)) →+* Ω := AdjoinRoot.lift φ ξ hroot
  have hd : IsUnit (f (denominator B n)) := by
    change IsUnit (f (∏ k ∈ Finset.Ioo 0 n, (1 - AdjoinRoot.root (X ^ n - C (1 : B)) ^ k)))
    rw [map_prod, IsUnit.prod_iff]
    intro k hk
    obtain ⟨hk₀, hkn⟩ := Finset.mem_Ioo.1 hk
    rw [map_sub, map_one, map_pow, AdjoinRoot.lift_root]
    exact (sub_ne_zero.2 (hξ.pow_ne_one_of_pos_of_lt hk₀.ne' hkn).symm).isUnit
  refine ⟨IsLocalization.Away.lift (denominator B n) hd, ?_⟩
  ext b
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B (AdjoinRoot (X ^ n - C (1 : B)))
    (PrimitiveRootsAlgebra B n), IsLocalization.Away.lift_eq]
  exact AdjoinRoot.lift_of hroot

end PrimitiveRootsAlgebra

open CategoryTheory

/-- The étale cover `Spec B[ζ] ⟶ Spec B` adjoining a primitive `n`-th root of unity. -/
noncomputable def primitiveRootsCover :
    Spec (.of (PrimitiveRootsAlgebra B n)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (PrimitiveRootsAlgebra B n)))

/-- The cover `Spec B[ζ] ⟶ Spec B` is étale when `n ≠ 0` is invertible in `B`. -/
theorem etale_primitiveRootsCover (hn₀ : n ≠ 0) (hn : IsUnit (n : B)) :
    Etale (primitiveRootsCover B n) := by
  have := PrimitiveRootsAlgebra.etale B n hn₀ hn
  rw [primitiveRootsCover, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- Every separably closed point of `Spec B` lifts to `Spec B[ζ]` when `n` is invertible in `B`.
-/
theorem exists_comp_primitiveRootsCover_eq (hn : IsUnit (n : B)) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of B)) :
    ∃ t : Spec (.of Ω) ⟶ Spec (.of (PrimitiveRootsAlgebra B n)),
      t ≫ primitiveRootsCover B n = s := by
  let φ := Spec.preimage s
  have : NeZero (n : Ω) := ⟨by simpa using (hn.map φ.hom).ne_zero⟩
  obtain ⟨ψ, hψ⟩ := PrimitiveRootsAlgebra.exists_lift B n φ.hom
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [primitiveRootsCover, ← Spec.map_comp, ← Spec.map_preimage s]
  congr 1
  ext b
  exact congr($hψ b)

/-- The cover `Spec B[ζ] ⟶ Spec B` is surjective when `n` is invertible in `B`. -/
theorem surjective_primitiveRootsCover (hn : IsUnit (n : B)) :
    Function.Surjective (primitiveRootsCover B n).base := by
  intro x
  let Ω := AlgebraicClosure ((Spec (.of B)).residueField x)
  let s : Spec (.of Ω) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of B)).residueField x) Ω)) ≫
      (Spec (.of B)).fromSpecResidueField x
  obtain ⟨t, ht⟩ := exists_comp_primitiveRootsCover_eq B n hn s
  refine ⟨t (IsLocalRing.closedPoint Ω), ?_⟩
  rw [← Scheme.Hom.comp_apply, ht]
  simp only [s, Scheme.Hom.comp_apply, Scheme.SpecMap_apply_closedPoint]
  exact Scheme.fromSpecResidueField_apply x _

end AlgebraicGeometry
