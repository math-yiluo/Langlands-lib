/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import WeilConjectures.Topology.ConstructibleGenericPoint

/-!

# Constructible subsets of the affine line avoiding the generic point

Let `X` be a scheme isomorphic to `Spec R`, for `R` a noetherian domain of dimension at most one.
A constructible subset of `X` containing no generic point of `X` is a finite set of closed points
(`AlgebraicGeometry.exists_finset_of_isConstructible_of_isIso`). In particular this holds for the
affine line `𝔸(n; Spec K)` over a field `K`, with `n` a singleton
(`AlgebraicGeometry.AffineSpace.exists_finset_of_isConstructible`).

This is the first half of the finite-support step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`): the image of the support in a coordinate line
is constructible and omits the generic point, so is a finite set of closed points.

-/

@[expose] public section

universe u

open CategoryTheory Set Topology TopologicalSpace

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The point of a scheme isomorphic to the spectrum of a domain corresponding to the zero ideal
is a generic point. -/
lemma isGenericPoint_of_isIso_of_asIdeal_eq_bot (f : X ⟶ Spec (.of R)) [IsIso f] {x : X}
    (hx : (f x).asIdeal = ⊥) :
    IsGenericPoint x univ := by
  have h1 : closure ({f x} : Set (Spec (.of R))) = univ := by
    rw [PrimeSpectrum.closure_singleton, hx, PrimeSpectrum.zeroLocus_bot]
  have h2 : f.homeomorph ⁻¹' {f.homeomorph x} = {x} := by
    rw [← Set.image_singleton, f.homeomorph.preimage_image]
  change closure {x} = univ
  rw [← h2, ← f.homeomorph.preimage_closure]
  simp only [Scheme.Hom.homeomorph_apply, h1, preimage_univ]

/-- In a scheme isomorphic to the spectrum of a domain of dimension at most one, every point
which is not a generic point is closed. -/
lemma isClosed_singleton_of_isIso_of_not_isGenericPoint [IsDomain R] [Ring.KrullDimLE 1 R]
    (f : X ⟶ Spec (.of R)) [IsIso f] {x : X}
    (hx : ¬ IsGenericPoint x univ) : IsClosed {x} := by
  have hne : (f x).asIdeal ≠ ⊥ := fun h ↦ hx (isGenericPoint_of_isIso_of_asIdeal_eq_bot f h)
  have hmax : (f x).asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot (f x).2 hne
  have hcl : IsClosed ({f x} : Set (Spec (.of R))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h2 : f.homeomorph ⁻¹' {f.homeomorph x} = {x} := by
    rw [← Set.image_singleton, f.homeomorph.preimage_image]
  rw [← h2]
  exact hcl.preimage f.homeomorph.continuous

/-- **Constructible sets avoiding the generic point of a curve.** Let `X` be a scheme isomorphic
to the spectrum of a noetherian domain of dimension at most one. A constructible subset of `X`
containing no generic point of `X` is a finite set of closed points. -/
theorem exists_finset_of_isConstructible_of_isIso [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R]
    (f : X ⟶ Spec (.of R)) [IsIso f]
    {s : Set X} (hs : IsConstructible s) (hgen : ∀ x ∈ s, ¬ IsGenericPoint x univ) :
    ∃ S : Finset X, (S : Set X) = s ∧ ∀ x ∈ S, IsClosed {x} := by
  have : NoetherianSpace X := f.homeomorph.isEmbedding.isInducing.noetherianSpace
  let η : X := f.homeomorph.symm ⟨⊥, Ideal.isPrime_bot⟩
  have hη : IsGenericPoint η univ := by
    refine isGenericPoint_of_isIso_of_asIdeal_eq_bot f ?_
    change (f.homeomorph (f.homeomorph.symm _)).asIdeal = ⊥
    rw [Homeomorph.apply_symm_apply]
  exact hs.exists_finset_of_notMem hη
    (fun x hx ↦ isClosed_singleton_of_isIso_of_not_isGenericPoint f fun h ↦
      hx (h.eq hη))
    fun h ↦ hgen η h hη

/-- The polynomial ring in one variable over a field has dimension at most one. -/
instance AffineSpace.krullDimLE_one_mvPolynomial (n : Type*) [Unique n] (K : Type*) [Field K] :
    Ring.KrullDimLE 1 (MvPolynomial n K) := by
  rw [Ring.krullDimLE_iff, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field K, Nat.card_unique]
  simp

/-- **Constructible subsets of the affine line avoiding the generic point.** A constructible
subset of the affine line `𝔸(n; Spec K)` over a field `K` (`n` a singleton) containing no generic
point is a finite set of closed points. -/
theorem AffineSpace.exists_finset_of_isConstructible (n : Type u) [Unique n] (K : Type u)
    [Field K] {s : Set 𝔸(n; Spec (.of K))} (hs : IsConstructible s)
    (hgen : ∀ x ∈ s, ¬ IsGenericPoint x univ) :
    ∃ S : Finset 𝔸(n; Spec (.of K)), (S : Set 𝔸(n; Spec (.of K))) = s ∧
      ∀ x ∈ S, IsClosed {x} :=
  exists_finset_of_isConstructible_of_isIso (AffineSpace.SpecIso n (.of K)).hom hs hgen

end AlgebraicGeometry
