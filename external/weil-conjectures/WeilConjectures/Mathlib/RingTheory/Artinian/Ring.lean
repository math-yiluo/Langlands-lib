/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-!
# Connected reduced finite algebras over an algebraically closed field

A finite reduced algebra `B` over an algebraically closed field `K` whose only idempotents are
`0` and `1` is `K` itself: `B` is Artinian and reduced, hence a finite product of fields, and
having no nontrivial idempotents it is a single field, finite over `K`, hence equal to `K`.

## Main statements

- `IsAlgClosed.finrank_eq_one_of_isReduced`: such an algebra has `finrank K B = 1`.
- `IsAlgClosed.exists_pow_eq_of_finite`: every unit of a finite algebra over an algebraically
  closed field `K` is an `n`-th power, for `n` invertible in `K`.
-/

@[expose] public section

/-- A nontrivial finite reduced algebra `B` over an algebraically closed field `K` whose only
idempotents are `0` and `1` has dimension `1` over `K`. This is the algebraic step of Stacks
0BUG (`Γ(X, 𝒪_X) = k` for `X` proper, geometrically connected and geometrically reduced). -/
theorem IsAlgClosed.finrank_eq_one_of_isReduced {K B : Type*} [Field K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] [Nontrivial B]
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : Module.finrank K B = 1 := by
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  have : Subsingleton (MaximalSpectrum B) := by
    refine ⟨fun I J ↦ by_contra fun hIJ ↦ ?_⟩
    classical
    let e := (IsArtinianRing.equivPi B).symm (Pi.single I 1)
    have he : IsIdempotentElem e := by
      simp only [IsIdempotentElem, e, ← map_mul, ← Pi.single_mul, one_mul]
    rcases hB e he with h | h
    · have := congr_fun ((IsArtinianRing.equivPi B).symm.injective (h.trans (map_zero _).symm)) I
      simp at this
    · have := congr_fun ((IsArtinianRing.equivPi B).symm.injective (h.trans (map_one _).symm)) J
      simp [Ne.symm hIJ] at this
  have : IsLocalRing B := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun n hn ↦ ?_⟩
    exact congrArg MaximalSpectrum.asIdeal (Subsingleton.elim (⟨n, hn⟩ : MaximalSpectrum B) ⟨m, hm⟩)
  have := (IsArtinianRing.isField_of_isReduced_of_isLocalRing B).isDomain
  exact ((LinearEquiv.ofBijective (Algebra.linearMap K B)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm).trans
    (Module.finrank_self K)

open Polynomial in
/-- Every unit of a finite algebra `A` over an algebraically closed field `k` is an `n`-th power,
for `n` invertible in `k`.

The reduced quotient `A ⧸ nilradical A` is a finite product of fields, each finite over `k` and
hence equal to `k`, so `u` has an `n`-th root there. That root lifts to `A` because
`A[T]/(Tⁿ - u)` is étale over `A` and the nilradical of the Artinian ring `A` is nilpotent.
This is the input "the units of `𝒪_C(C)` are `n`-divisible for `C` proper" of blueprint
`proposition-smooth-proper-curves-torsion-prime--2`. -/
theorem IsAlgClosed.exists_pow_eq_of_finite {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Module.Finite k A] {n : ℕ} (hn : (n : k) ≠ 0) (u : Aˣ) :
    ∃ v : Aˣ, v ^ n = u := by
  have hn₀ : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hnA : IsUnit (n : A) := by
    simpa using (hn.isUnit.map (algebraMap k A))
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  let N := nilradical A
  let B := A ⧸ N
  have : IsReduced B := (Ideal.isRadical_iff_quotient_reduced N).1 (Ideal.radical_isRadical _)
  -- An `n`-th root of `u` in the reduced quotient, componentwise in its product decomposition
  obtain ⟨w, hw⟩ : ∃ w : B, w ^ n = Ideal.Quotient.mk N u := by
    let e := IsArtinianRing.equivPi B
    have hroot (I : MaximalSpectrum B) (z : B ⧸ I.asIdeal) : ∃ y, y ^ n = z := by
      have : Module.Finite k (B ⧸ I.asIdeal) := Module.Finite.trans B _
      obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := k) (K := B ⧸ I.asIdeal)).2 z
      obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn₀)
      exact ⟨algebraMap k _ d, by rw [← map_pow, hd]⟩
    choose y hy using hroot
    refine ⟨e.symm fun I ↦ y I (e (Ideal.Quotient.mk N u) I), ?_⟩
    apply e.injective
    rw [map_pow, AlgEquiv.apply_symm_apply]
    funext I
    exact hy _ _
  -- Lift it along the nilpotent ideal `N` using that `A[T]/(Tⁿ - u)` is étale over `A`
  have : Algebra.Etale A (AdjoinRoot (X ^ n - C (u : A))) :=
    AdjoinRoot.etale_X_pow_sub_C hn₀ hnA u.isUnit
  let g : AdjoinRoot (X ^ n - C (u : A)) →ₐ[A] B :=
    AdjoinRoot.liftAlgHom (X ^ n - C (u : A)) (Algebra.ofId A B) w (by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hw, sub_eq_zero]
      rfl)
  let l := Algebra.FormallySmooth.lift N (IsArtinianRing.isNilpotent_nilradical) g
  have hl : l (AdjoinRoot.root _) ^ n = u := by
    have h0 := AdjoinRoot.eval₂_root (X ^ n - C (u : A))
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← AdjoinRoot.algebraMap_eq] at h0
    have := congrArg l h0
    rw [map_sub, map_pow, map_zero, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    exact sub_eq_zero.1 this
  exact ⟨(isUnit_pow_iff hn₀).1 (hl ▸ u.isUnit) |>.unit, Units.ext (by simpa using hl)⟩
