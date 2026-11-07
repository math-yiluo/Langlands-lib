# Unramified twists of the actual abelian epsilon expression

This internal construction supports the common-closure existence argument. For
every supplied topological realization `T` of a finite p-adic field, every
continuous multiplicative quasicharacter `ω`, nontrivial unitary additive
character `ψ`, and natural number `a`, `abelianUnramifiedTwistFactor` is the
complex unit `ω(c)`, where the already constructed scale `c` has order
`n(ψ) + a`. There is no assumption of a nonabelian local-constant system.

If `ω` is unramified, the file proves:

- Twisting any quasicharacter `χ` by `ω` preserves its actual least conductor.
- Every unit `π` of order one gives the same factor, namely
  `ω(π)^(n(ψ) + a)`.
- The actual abelian epsilon expression of `χ * ω` equals the expression of
  `χ` multiplied by this factor at `a = a(χ)`, for every supplied regular
  additive Haar measure.
- The quotient of two factors is `ω(π)^(a - b)`. Consequently the quotient
  of epsilon expressions for `χ * ω` and `η * ω` is the original quotient
  multiplied by `ω(π)^(a(χ) - a(η))`. The additive conductor cancels.

The implemented proof uses the published explicit-level conductor and Gauss
integral results. `conductorAt_iff` identifies their exact conductor predicate
with the intrinsic conductor. The proved unramified conductor law then allows
`epsilonAt_mul_unramified` to be evaluated at the intrinsic conductor and at
spectral parameter zero. The published identity
`deligneConstant_eq_abelianEpsilonExpression` identifies that value with the
actual expression. The factor calculation uses the valuation formula for an
unramified character and the proved order of `abelianScale`. Integer exponent
subtraction proves the quotient formula.

This is a derived adapter for Deligne, *Les constantes des équations
fonctionnelles des fonctions L* (1973), §3.4, formula (3.4.3.5), printed
page 528, PDF page 28 of the registered source
`deligne-1973-local-constants`. The ratio calculation is the rank-one
calculation used in §4.5, printed page 539, PDF page 39. These pages were read
from the original, and the formula on page 528 was checked in its rendered
image. This file does not assert conductor compatibility with induction,
the vanishing of epsilon evaluations on Brauer relations, or existence of
a nonabelian system.
