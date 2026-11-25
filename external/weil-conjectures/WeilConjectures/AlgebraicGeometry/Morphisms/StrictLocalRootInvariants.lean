/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.GroupTheory.Index
public import WeilConjectures.Mathlib.RingTheory.Henselian

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import WeilConjectures.AlgebraicGeometry.Morphisms.RootPowerMapInvariants

/-! # Fixed rings of a strict local root algebra

## References

* Stacks Project, Tags 0EYG and 09EV, intermediate-root calculation
* Stacks Project, Tag 09EV, cyclic intermediate-root calculation
* Stacks Project, Tag 09EV, intermediate subextensions
* Stacks Project, Tag 0EYG, final intermediate-field paragraph, and Tag 09EV
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The endomorphism of a root algebra sending its root to `zeta * root`.
Its construction is polynomial evaluation, with no choice of algebra data. -/
noncomputable def rootRotation (H : Type u) [CommRing H] (h : H) (n : ℕ)
    (ζ : rootsOfUnity n H) :
    AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) →ₐ[H]
      AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (algebraMap H _ ((ζ : Hˣ) : H) * AdjoinRoot.root _) (by
      have hz := (mem_rootsOfUnity' n (ζ : Hˣ)).mp ζ.property
      have ht := AdjoinRoot.eval₂_root
        ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
      have ht' : AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) ^ n =
          algebraMap H _ h := by
        simpa [sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using ht
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, mul_pow, ← map_pow, hz, map_one, one_mul, ht']
      exact sub_self _)

/-- The actual fixed subalgebra for a subgroup of the root rotations. -/
noncomputable def rootFixedAlgebra (H : Type u) [CommRing H] (h : H) (n : ℕ)
    (K : Subgroup (rootsOfUnity n H)) :
    Subalgebra H (AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)) :=
  ⨅ ζ : K, AlgHom.equalizer (rootRotation H h n ζ.val) (AlgHom.id H _)

/-- A subgroup of the root rotations has an intermediate root algebra as its fixed ring. -/
theorem strict_local_root_invariants
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    (h : H) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H))
    (K : Subgroup (rootsOfUnity n H)) :
    0 < K.index ∧ K.index ∣ n ∧
      Nonempty (rootFixedAlgebra H h n K ≃ₐ[H]
        AdjoinRoot ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h)) := by
  obtain ⟨hcard, hcyclic, hsep⟩ := strict_local_roots_of_unity H n hn
  have : Finite (rootsOfUnity n H) :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne hn.1.ne')
  have : IsCyclic (rootsOfUnity n H) := hcyclic
  have he : 0 < K.index := Nat.pos_of_ne_zero K.index_ne_zero_of_finite
  have hdiv : K.index ∣ n := by
    simpa only [hcard] using K.index_dvd_card
  have hre : Nat.card K * K.index = n := K.card_mul_index.trans hcard
  let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
  let t : C := AdjoinRoot.root _
  have ht : t ^ n = algebraMap H C h := by
    simpa [t, C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
  have hrel : (((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h).eval₂
      (Algebra.ofId H C) (t ^ Nat.card K)) = 0 := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, ← pow_mul, hre, ht]
    exact sub_self _
  let φ := AdjoinRoot.liftAlgHom
    ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h)
    (Algebra.ofId H C) (t ^ Nat.card K) hrel
  have hρ : ∀ ζ, rootRotation H h n ζ t =
      algebraMap H C ((ζ : Hˣ) : H) * t := by
    intro ζ
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hφ : φ (AdjoinRoot.root _) = t ^ Nat.card K :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  obtain ⟨hinj, hrange⟩ := root_power_map_invariants H h n hn.1 hcard hsep K
    (rootRotation H h n) hρ φ hφ
  have hfixed : ∀ x : C, x ∈ rootFixedAlgebra H h n K ↔ x ∈ Set.range φ := by
    intro x
    simp only [rootFixedAlgebra, Algebra.mem_iInf, AlgHom.mem_equalizer]
    exact hrange x
  have hmem : ∀ y, φ y ∈ rootFixedAlgebra H h n K := by
    intro y
    exact (hfixed (φ y)).mpr ⟨y, rfl⟩
  let ψ := φ.codRestrict (rootFixedAlgebra H h n K) hmem
  have hbij : Function.Bijective ψ := by
    constructor
    · exact (φ.injective_codRestrict _ hmem).mpr hinj
    · intro x
      obtain ⟨y, hy⟩ := (hfixed x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨he, hdiv, ⟨(AlgEquiv.ofBijective ψ hbij).symm⟩⟩

end AlgebraicGeometry.Scheme
