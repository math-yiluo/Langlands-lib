/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.LinearAlgebra.IdempotentCharpoly
import WeilConjectures.LinearAlgebra.IdempotentCharpolyLocalCharpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.LocalProperties.Submodule

/-! # Idempotent leading coefficient of a summand determinant

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial
paragraph, with the finite-projective local calculation made explicit.
(blueprint: lem-weil-pbc-idempotent-charpoly-leading-coeff)
-/

@[expose] public section

universe u v

namespace Matrix

/-- The leading coefficient of the determinant on a commuting idempotent summand
is itself idempotent.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph.
(blueprint: lem-weil-pbc-idempotent-charpoly-leading-coeff)

Proof: split the ambient finite free module into the images of P and 1-P. Both
summands are finite projective. Choose and refine finite standard free covers for
these two modules. On each nonzero cover localization an adapted basis identifies
1-P+(X-T)P with the block diagonal matrix diag(X-T_image,1), so its determinant is
monic of degree r, the rank of the image of P. Let d be the natural degree of the
original determinant. Degree cannot increase under localization, so r ≤ d. Its
coefficient at d is therefore 1 if r=d, and 0 if r<d. Thus the image of the original
leading coefficient is idempotent on every member of the cover. On a zero
localization the same equation holds trivially. Apply injectivity on the standard
cover to the element leadingCoeff²-leadingCoeff to conclude the equation over A.
For the zero ring the equation is automatic. -/
theorem isIdempotentElem_idempotentCharpoly_leadingCoeff
    {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]
    (T P : Matrix n n A) (hP : P * P = P) (hTP : T * P = P * T) :
    IsIdempotentElem (idempotentCharpoly T P).leadingCoeff := by
  obtain ⟨r, f, hspan, hchar⟩ := exists_standardCover_idempotentCharpoly_eq_charpoly T P hP hTP
  have hlocal (i : Fin r) :
      IsIdempotentElem (algebraMap A (Localization.Away (f i))
        (idempotentCharpoly T P).leadingCoeff) := by
    obtain ⟨d, U, hU⟩ := hchar i
    let q := (idempotentCharpoly T P).map (algebraMap A (Localization.Away (f i)))
    have hmonic : q.Monic := by rw [show q = U.charpoly from hU]; exact U.charpoly_monic
    have hle : q.natDegree ≤ (idempotentCharpoly T P).natDegree := Polynomial.natDegree_map_le
    have hc : algebraMap A (Localization.Away (f i)) (idempotentCharpoly T P).leadingCoeff =
        q.coeff (idempotentCharpoly T P).natDegree := by
      rw [Polynomial.leadingCoeff, Polynomial.coeff_map]
    rw [hc]
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp [IsIdempotentElem]
    · rw [← heq, hmonic.coeff_natDegree]
      simp [IsIdempotentElem]
  have hz : (idempotentCharpoly T P).leadingCoeff *
      (idempotentCharpoly T P).leadingCoeff - (idempotentCharpoly T P).leadingCoeff = 0 := by
    apply Module.eq_zero_of_isLocalized_span (Set.range f) hspan
      (fun a : {a // a ∈ Set.range f} ↦ Localization.Away (a : A))
      (fun a ↦ Algebra.linearMap A (Localization.Away (a : A)))
    rintro ⟨_, ⟨i, rfl⟩⟩
    change algebraMap A (Localization.Away (f i))
      ((idempotentCharpoly T P).leadingCoeff * (idempotentCharpoly T P).leadingCoeff -
        (idempotentCharpoly T P).leadingCoeff) = 0
    rw [map_sub, map_mul]
    exact sub_eq_zero.mpr (hlocal i)
  exact sub_eq_zero.mp hz

end Matrix
