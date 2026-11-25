/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.PopescuDelocalizeJacobianLocalization
import WeilConjectures.AlgebraicGeometry.PopescuDelocalizeDehomogenizationEquiv
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Smoothness of the localized auxiliary algebra in weak delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F9
(`smoothing.tex`, lemma-delocalize-weak), and Algebra, Definition Tag 00T6.
(blueprint: lem-weil-pbc-popescu-delocalize-weak-localization-smooth).
-/

@[expose] public section

universe u

open scoped BigOperators
open MvPolynomial

namespace Algebra

open Classical in
/-- Source: Stacks Project, proof of Lemma Tag 07F9, the construction of `B` and `b`;
Algebra, Definition Tag 00T6 and Lemma Tag 00T7.
(blueprint: lem-weil-pbc-popescu-delocalize-weak-localization-smooth)

The small polynomial ring numbers `x₁,...,xₙ₊ₘ` by `Fin (n+m)` starting at zero.
In the large ring, index zero is `x₀`, index `i+1` is the original variable `i`,
and index `n+m+1` is the homogenizing variable. The sum in `hdegree` counts only
exponents of the last `m` original variables. The formula in `hF` homogenizes
those variables and leaves the first `n` variables as coefficient variables.

Proof (the seven steps of the node):
1. Expand the finite monomial sum to obtain `Fⱼ(u,v*w,w) = w^dⱼ*fⱼ(u,v)`;
for a unit `w` this also gives the inverse dehomogenization identity. Use the
polynomial universal property (def-weil-pbc-mv-polynomial-ring).
2. Put `s = ∏ sⱼ` and form `C = R[x₀,...,xₙ₊ₘ₊₁,y,z]/(f,x₀*xₙ₊ₘ₊₁*y-1,s*z-1)`.
In `C`, `x₀`, `xₙ₊ₘ₊₁` and every `sⱼ` are units. The two ideal memberships imply
that the `gⱼ` vanish and that the Jacobian determinant is a unit.
3. The derivatives with respect to the first `c` original variables, `y`, `z`
give a block diagonal Jacobian with determinant `Δ*x₀*xₙ₊ₘ₊₁*s`, a unit.
Thus `C` is standard smooth (def-weil-pbc-polynomial-partial-derivative and
 def-weil-pbc-standard-smooth-algebra, Tag 00T6).
4. Map the large ring to `C` by `Xₙ₊ᵢ ↦ xₙ₊ᵢ*xₙ₊ₘ₊₁`, fixing the other variables.
Step 1 kills `x₀*Fⱼ`; Step 2 kills `gⱼ`. This factors through `B` and extends to
`B_b` since `b` maps to a unit (lem-weil-pbc-localization-away-universal-property).
5. Conversely send `xₙ₊ᵢ` to `Xₙ₊ᵢ/Xₙ₊ₘ₊₁` in `B_b`, and `y,z` to the inverses
of `x₀*Xₙ₊ₘ₊₁,s`. Step 1 kills `fⱼ` since `x₀` and `Xₙ₊ₘ₊₁` are units.
This gives `C → B_b` (def-weil-ring-localization-away).
6. The two maps agree with the identity on every polynomial generator, and
then on the quotients and localization by their universal properties. They
are inverse `R`-algebra maps.
7. Transport the standard smooth presentation along this isomorphism; standard
smooth implies smooth (lem-weil-pbc-standard-smooth-is-smooth, Tag 00T7;
 def-weil-pbc-smooth-ring-map). -/
theorem popescu_delocalize_weak_localization_smooth
    (R : Type u) [CommRing R]
    (n m c t : ℕ) (hc : c ≤ n + m)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (g : Fin t → MvPolynomial (Fin n) R)
    (s : Fin (t + 1) → R)
    (h : MvPolynomial (Fin (n + m)) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f))
    (hg : ∀ j : Fin t,
      C (s j.succ) * rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈
        Ideal.span (Set.range f))
    (d : Fin c → ℕ)
    (hdegree : ∀ j : Fin c, ∀ e ∈ (f j).support,
      (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j)
    (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
    (hF : ∀ j : Fin c, F j =
      ∑ e ∈ (f j).support,
        C ((f j).coeff e) *
          (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
          X (Fin.last (n + m + 1)) ^
            (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) :
    Algebra.Smooth R (Localization.Away
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun j : Fin t =>
            rename (fun i : Fin n =>
              (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ) (g j)) ∪
            Set.range (fun j : Fin c => X (0 : Fin (n + m + 2)) * F j)))
        (X (0 : Fin (n + m + 2)) * X (Fin.last (n + m + 1)) *
          C (∏ j : Fin (t + 1), s j)))) := by
  have := popescu_auxiliary_isStandardSmooth R (n + m) c t hc f s h hs
  obtain ⟨e⟩ := popescu_delocalize_dehomogenization_equiv_exists
    R n m c t f g s hg d hdegree F hF
  have := Algebra.IsStandardSmooth.of_algEquiv e.symm
  infer_instance

end Algebra
