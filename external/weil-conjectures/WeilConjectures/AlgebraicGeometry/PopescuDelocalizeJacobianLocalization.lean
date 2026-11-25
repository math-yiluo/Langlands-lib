/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.AlgebraicGeometry.PopescuAuxiliarySubmersivePresentation

/-!
# Standard smoothness of the dehomogenized Jacobian localization

Source: Stacks Project, proof of Tag 07F9, the final displayed localization;
Algebra, Definition Tag 00T6.
(blueprint: lem-weil-pbc-popescu-delocalize-jacobian-localization)
-/

@[expose] public section

universe u
open scoped BigOperators
open MvPolynomial
namespace Algebra

/-- Source: Stacks Project, proof of Tag 07F9, the final displayed localization,
and Definition Tag 00T6.
(blueprint: lem-weil-pbc-popescu-delocalize-jacobian-localization)

Proof: Write D = R[x₀,x₁,...,x_N,w]/(f), with f inserted into variables 1,...,N,
and a = x₀*w*∏sⱼ. In D[1/a], x₀, w and every sⱼ are units. The image of the
ideal membership gives s₀ = h*Δ, so Δ is a unit with inverse h/s₀. Present D[1/a]
as R[x₀,x₁,...,x_N,w,y]/(f,a*y-1). This identification sends y to the inverse of a
and is inverse on every generator by the quotient and localization universal
properties. Select the c original variables specified by hc, and y, for the
Jacobian minor. The derivatives of f with respect to y are zero. The final
row/column has diagonal entry a; its other entries need not vanish but do not
contribute to the determinant, which is Δ*a. Its image is a unit. The naive
presentation with this selected injective variable map is therefore submersive;
apply SubmersivePresentation.isStandardSmooth. The inequality c+1 ≤ N+3 follows
from hc. Empty relation sets give Δ = 1; if a maps to zero the localization is
the zero ring and the same inverse relation presentation still applies. -/
theorem popescu_auxiliary_isStandardSmooth
    (R : Type u) [CommRing R] (N c t : ℕ) (hc : c ≤ N)
    (f : Fin c → MvPolynomial (Fin N) R)
    (s : Fin (t + 1) → R) (h : MvPolynomial (Fin N) R)
    (hs : C (s 0) - h * Matrix.det
      (fun i j : Fin c => pderiv (Fin.castLE hc i) (f j)) ∈
        Ideal.span (Set.range f)) :
    Algebra.IsStandardSmooth R (Localization.Away (Ideal.Quotient.mk
      (Ideal.span (Set.range (fun j : Fin c =>
        rename (fun i : Fin N => i.castSucc.succ) (f j))))
      (X (0 : Fin (N + 2)) * X (Fin.last (N + 1)) * C (∏ j : Fin (t + 1), s j)))) := by
  obtain ⟨P⟩ := popescu_auxiliary_submersivePresentation R N c t hc f s h hs
  exact P.isStandardSmooth

end Algebra
