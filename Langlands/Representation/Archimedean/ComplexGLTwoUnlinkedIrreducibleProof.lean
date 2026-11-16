import Langlands.Representation.Archimedean.ComplexGLTwoKFinite
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducible

/-!
# Proof: principal series of `GL_2(ℂ)` with unlinked characters are irreducible

`complexGLTwoUnlinkedIrreducible : ComplexGLTwoUnlinkedIrreducibleStatement`. For characters
`d`, `e` with `m = l_e - l_d` and `A = (t_e - t_d - 1) + m/2`, the `U(2)`-finite functions of
the standard module of `[d, e]` are bottom-row polynomials (`GLTwoKFinite.exists_isRealized`), and
unlinkedness gives the two nonvanishing conditions of `GLTwoCore.Setup`.
-/

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open LocalFactor.Archimedean GLTwoCore GLTwoKFinite

namespace GLTwoUnlinked

variable (d e : ComplexCharacterData)

/-- `x_d - x_e = -(A + 1)` with `x = t + l/2`. -/
theorem x_sub (A : ℂ) (hA : A = e0 d e + (((e.weight - d.weight : ℤ) : ℂ)) / 2) :
    (d.exponent + (d.weight : ℂ) / 2) - (e.exponent + (e.weight : ℂ) / 2) = -(A + 1) := by
  rw [hA, e0]; push_cast; ring

/-- `y_d - y_e = -(A + 1) + m` with `y = t - l/2`. -/
theorem y_sub (A : ℂ) (hA : A = e0 d e + (((e.weight - d.weight : ℤ) : ℂ)) / 2) :
    (d.exponent - (d.weight : ℂ) / 2) - (e.exponent - (e.weight : ℂ) / 2) =
      -(A + 1) + ((e.weight - d.weight : ℤ) : ℂ) := by
  rw [hA, e0]; push_cast; ring

theorem linked_of (A : ℂ) (hA : A = e0 d e + (((e.weight - d.weight : ℤ) : ℂ)) / 2)
    (p : ℤ) (hp : -(A + 1) = (p : ℂ)) (hpq : 0 < p * (p + (e.weight - d.weight))) :
    IsComplexLinked d e := by
  refine ⟨p, p + (e.weight - d.weight), hpq, ?_, ?_⟩
  · rw [x_sub d e A hA, hp]
  · rw [y_sub d e A hA, hp]; push_cast; ring

/-- The hypotheses of `GLTwoCore.Setup` for unlinked `d`, `e`. -/
theorem setup (h : ¬ IsComplexLinked d e) :
    Setup [d, e] (Phi d) (e0 d e + (((e.weight - d.weight : ℤ) : ℂ)) / 2)
      (e.weight - d.weight) where
  hΦ δ hδ := differentiableAt_unitChar _ _ hδ
  hΦ0 δ hδ := unitChar_ne_zero _ _ hδ
  hF1 x := exists_isRealized x
  hup j hj := by
    apply h
    set m : ℤ := e.weight - d.weight with hm
    have hA : e0 d e + ((m : ℤ) : ℂ) / 2 = ((m.toNat + j : ℕ) : ℂ) := by
      rw [ls, la, sub_eq_zero] at hj; exact hj
    refine linked_of d e _ rfl (-((m.toNat : ℤ) + j + 1)) ?_ ?_
    · rw [hA]; push_cast; ring
    · have h1 : (m.toNat : ℤ) - m = ((-m).toNat : ℤ) := by
        have := Int.toNat_sub_toNat_neg m; omega
      have hp : -((m.toNat : ℤ) + j + 1) < 0 := by omega
      have hq : -((m.toNat : ℤ) + j + 1) + m < 0 := by omega
      exact mul_pos_of_neg_of_neg hp hq
  hdown j hj1 hj := by
    apply h
    set m : ℤ := e.weight - d.weight with hm
    have hA : e0 d e + ((m : ℤ) : ℂ) / 2 = -(((-m).toNat + j : ℕ) : ℂ) - 1 := by
      rw [lb] at hj; linear_combination hj
    refine linked_of d e _ rfl (((-m).toNat : ℤ) + j) ?_ ?_
    · rw [hA]; push_cast; ring
    · have h1 : ((-m).toNat : ℤ) + m = (m.toNat : ℤ) := by
        have := Int.toNat_sub_toNat_neg m; omega
      have hp : 0 < ((-m).toNat : ℤ) + j := by omega
      have hq : 0 < ((-m).toNat : ℤ) + j + m := by omega
      exact mul_pos hp hq

end GLTwoUnlinked

open GLTwoUnlinked in
/-- **Principal series of `GL_2(ℂ)` with unlinked characters are irreducible.** -/
theorem complexGLTwoUnlinkedIrreducible : ComplexGLTwoUnlinkedIrreducibleStatement := by
  intro d e h
  exact (setup d e h).isIrreducible (complexStandardNontrivial 2 [d, e] rfl)

end Langlands.Archimedean
