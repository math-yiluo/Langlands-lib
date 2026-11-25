/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Polynomial.Basic
public import WeilConjectures.AlgebraicGeometry.GenericFiber.ProjectiveCoordinate
public import WeilConjectures.RingTheory.MvPolynomial.CoordinateZeroLocus

/-!

# Points of affine space with coordinates in finite sets of closed points

Let `K` be a field and `ι` a finite type. For each `i : ι` let `Sᵢ` be a finite set of closed
points of the affine line. The points of the affine space `𝔸(ι; Spec K)` whose image under every
coordinate projection to the line lies in `Sᵢ` form a finite set of closed points.

## Main statements

- `PrimeSpectrum.exists_finset_comap_aeval_X_mem`: the statement for `Spec K[X_i : i ∈ ι]` and
  the coordinate maps to `Spec K[X]` induced by `X ↦ X i`.
- `PrimeSpectrum.exists_finset_comap_rename_mem`: the statement for the coordinate maps to
  `Spec K[X_u : u ∈ n]` (`n` a singleton) induced by `MvPolynomial.rename`.
- `AlgebraicGeometry.AffineSpace.exists_finset_reindex_mem`: the statement for `𝔸(ι; Spec K)`
  and the coordinate projections `AffineSpace.reindex` to the line `𝔸(n; Spec K)`.

This is the scheme-level form of `MvPolynomial.finite_zeroLocus_range_aeval_X`: the "finite
product of finite sets" in the finite-support step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`).

-/

@[expose] public section

open Polynomial

namespace PrimeSpectrum

/-- In a domain which is not a field, every finite set of closed points of the spectrum lies in
the zero locus of a single nonzero element. -/
lemma exists_ne_zero_forall_mem_asIdeal {R : Type*} [CommRing R] [IsDomain R]
    (hR : ¬ IsField R) (S : Finset (PrimeSpectrum R))
    (hS : ∀ y ∈ S, IsClosed ({y} : Set (PrimeSpectrum R))) :
    ∃ f : R, f ≠ 0 ∧ ∀ y ∈ S, f ∈ y.asIdeal := by
  have hne : ∀ y ∈ S, ∃ g ∈ y.asIdeal, g ≠ 0 := fun y hy ↦
    Submodule.exists_mem_ne_zero_of_ne_bot (Ring.ne_bot_of_isMaximal_of_not_isField
      ((isClosed_singleton_iff_isMaximal y).1 (hS y hy)) hR)
  classical
  choose! g hgmem hgne using hne
  refine ⟨∏ y ∈ S, g y, Finset.prod_ne_zero_iff.2 hgne, fun y hy ↦ ?_⟩
  rw [← Finset.mul_prod_erase S g hy]
  exact Ideal.mul_mem_right _ _ (hgmem y hy)

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] {n : Type*} [Unique n]

/-- Let `φ i : A →+* K[X_i : i ∈ ι]` be ring maps out of a domain `A` which is not a field, each
sending nonzero elements to nonzero polynomials in the single variable `X i`. The points of
`Spec K[X_i : i ∈ ι]` whose image under each `Spec (φ i)` lies in a given finite set of closed
points form a finite set of closed points. -/
theorem exists_finset_comap_mem_of_forall_eq_aeval_X {A : Type*} [CommRing A] [IsDomain A]
    (hA : ¬ IsField A) (φ : ι → A →+* MvPolynomial ι K)
    (hφ : ∀ i, ∀ a ≠ 0, ∃ f : K[X], f ≠ 0 ∧ φ i a = Polynomial.aeval (MvPolynomial.X i) f)
    (S : ι → Finset (PrimeSpectrum A))
    (hS : ∀ i, ∀ y ∈ S i, IsClosed ({y} : Set (PrimeSpectrum A))) :
    ∃ T : Finset (PrimeSpectrum (MvPolynomial ι K)),
      (T : Set (PrimeSpectrum (MvPolynomial ι K))) = {x | ∀ i, comap (φ i) x ∈ S i} ∧
      ∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum (MvPolynomial ι K))) := by
  choose g hg0 hgmem using fun i ↦ exists_ne_zero_forall_mem_asIdeal hA (S i) (hS i)
  choose f hf0 hf using fun i ↦ hφ i (g i) (hg0 i)
  set s := {x : PrimeSpectrum (MvPolynomial ι K) | ∀ i, comap (φ i) x ∈ S i}
  have hsub : s ⊆ zeroLocus (Set.range fun i ↦ Polynomial.aeval (MvPolynomial.X (R := K) i)
      (f i)) := by
    rintro x hx _ ⟨i, rfl⟩
    change Polynomial.aeval (MvPolynomial.X i) (f i) ∈ x.asIdeal
    rw [← hf i]
    exact hgmem i _ (hx i)
  refine ⟨((MvPolynomial.finite_zeroLocus_range_aeval_X hf0).subset hsub).toFinset, by simp,
    fun x hx ↦ ?_⟩
  rw [Set.Finite.mem_toFinset] at hx
  exact (isClosed_singleton_iff_isMaximal x).2
    (MvPolynomial.isMaximal_of_mem_zeroLocus_range_aeval_X hf0 (hsub hx))

/-- **Points with coordinates in finite sets of closed points.** For `K` a field and `ι` finite,
the points of `Spec K[X_i : i ∈ ι]` whose image under each coordinate map to `Spec K[X]` lies in
a given finite set of closed points form a finite set of closed points. -/
theorem exists_finset_comap_aeval_X_mem (S : ι → Finset (PrimeSpectrum K[X]))
    (hS : ∀ i, ∀ y ∈ S i, IsClosed ({y} : Set (PrimeSpectrum K[X]))) :
    ∃ T : Finset (PrimeSpectrum (MvPolynomial ι K)),
      (T : Set (PrimeSpectrum (MvPolynomial ι K))) =
        {x | ∀ i, comap (Polynomial.aeval (MvPolynomial.X (R := K) i)).toRingHom x ∈ S i} ∧
      ∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum (MvPolynomial ι K))) :=
  exists_finset_comap_mem_of_forall_eq_aeval_X (Polynomial.not_isField K) _
    (fun _ a ha ↦ ⟨a, ha, rfl⟩) S hS

omit [Finite ι] in
/-- `MvPolynomial.rename (fun _ ↦ i)` out of the polynomial ring in one variable is `aeval (X i)`
composed with `MvPolynomial.uniqueAlgEquiv`. -/
lemma _root_.MvPolynomial.rename_const_eq_aeval_uniqueAlgEquiv (i : ι)
    (g : MvPolynomial n K) :
    MvPolynomial.rename (fun _ ↦ i) g =
      Polynomial.aeval (MvPolynomial.X i) (MvPolynomial.uniqueAlgEquiv K n g) := by
  change MvPolynomial.rename (fun _ ↦ i) g =
    ((Polynomial.aeval (MvPolynomial.X i)).comp (MvPolynomial.uniqueAlgEquiv K n).toAlgHom) g
  congr 1
  refine MvPolynomial.algHom_ext fun _ ↦ ?_
  simp

/-- **Points with coordinates in finite sets of closed points**, with the coordinate maps to
`Spec K[X_u : u ∈ n]` (`n` a singleton) induced by `MvPolynomial.rename`. -/
theorem exists_finset_comap_rename_mem (S : ι → Finset (PrimeSpectrum (MvPolynomial n K)))
    (hS : ∀ i, ∀ y ∈ S i, IsClosed ({y} : Set (PrimeSpectrum (MvPolynomial n K)))) :
    ∃ T : Finset (PrimeSpectrum (MvPolynomial ι K)),
      (T : Set (PrimeSpectrum (MvPolynomial ι K))) =
        {x | ∀ i, comap (MvPolynomial.rename fun _ : n ↦ i).toRingHom x ∈ S i} ∧
      ∀ x ∈ T, IsClosed ({x} : Set (PrimeSpectrum (MvPolynomial ι K))) :=
  exists_finset_comap_mem_of_forall_eq_aeval_X
    (fun h ↦ Polynomial.not_isField K
      (MulEquiv.isField h (MvPolynomial.uniqueAlgEquiv K n).symm.toMulEquiv))
    _ (fun i a ha ↦ ⟨_, (MvPolynomial.uniqueAlgEquiv K n).injective.ne_iff' (map_zero _) |>.2 ha,
      MvPolynomial.rename_const_eq_aeval_uniqueAlgEquiv i a⟩) S hS

end PrimeSpectrum

namespace AlgebraicGeometry

universe u

open CategoryTheory

/-- **Points of affine space with coordinates in finite sets of closed points.** For `K` a field
and `ι` finite, the points of `𝔸(ι; Spec K)` whose image under each coordinate projection
`AffineSpace.reindex (fun _ ↦ i)` to the affine line `𝔸(n; Spec K)` (`n` a singleton) lies in a
given finite set of closed points form a finite set of closed points. -/
theorem AffineSpace.exists_finset_reindex_mem {K : Type u} [Field K] {ι : Type u} [Finite ι]
    {n : Type u} [Unique n] (S : ι → Finset 𝔸(n; Spec (.of K)))
    (hS : ∀ i, ∀ y ∈ S i, IsClosed ({y} : Set 𝔸(n; Spec (.of K)))) :
    ∃ T : Finset 𝔸(ι; Spec (.of K)),
      (T : Set 𝔸(ι; Spec (.of K))) =
        {x | ∀ i, reindex (fun _ : n ↦ i) (Spec (.of K)) x ∈ S i} ∧
      ∀ x ∈ T, IsClosed ({x} : Set 𝔸(ι; Spec (.of K))) := by
  let eι : PrimeSpectrum (MvPolynomial ι K) ≃ₜ 𝔸(ι; Spec (.of K)) :=
    (SpecIso ι (.of K)).inv.homeomorph
  let en : PrimeSpectrum (MvPolynomial n K) ≃ₜ 𝔸(n; Spec (.of K)) :=
    (SpecIso n (.of K)).inv.homeomorph
  obtain ⟨T, hT, hTc⟩ := PrimeSpectrum.exists_finset_comap_rename_mem (K := K) (n := n)
    (fun i ↦ (S i).map en.symm.toEquiv.toEmbedding) fun i y hy ↦
      en.isClosed_image.1 (by rw [Set.image_singleton]; exact hS i _ (by simpa using hy))
  refine ⟨T.map eι.toEquiv.toEmbedding, ?_, fun x hx ↦ ?_⟩
  · ext x
    have key (i : ι) : reindex (fun _ : n ↦ i) (Spec (.of K)) x =
        en (Spec.map (CommRingCat.ofHom (MvPolynomial.rename fun _ : n ↦ i).toRingHom)
          (eι.symm x)) := by
      have h := congr($(AffineSpace.SpecIso_inv_reindex (fun _ : n ↦ i) (.of K)) (eι.symm x))
      simp only [Scheme.Hom.comp_apply] at h
      exact (congrArg _ (eι.apply_symm_apply x).symm).trans h
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe,
      Set.mem_ofPred_eq, key]
    have hmem : (∃ y ∈ T, eι.toEquiv y = x) ↔ eι.symm x ∈ T :=
      ⟨fun ⟨y, hy, hyx⟩ ↦ by rw [← hyx]; simpa using hy, fun h ↦ ⟨_, h, eι.apply_symm_apply x⟩⟩
    rw [hmem, ← Finset.mem_coe, hT, Set.mem_ofPred_eq]
    simp only [Finset.mem_map_equiv]
    exact Iff.rfl
  · rw [Finset.mem_map_equiv] at hx
    exact eι.symm.isClosed_image.1 (by rw [Set.image_singleton]; exact hTc _ hx)

end AlgebraicGeometry
