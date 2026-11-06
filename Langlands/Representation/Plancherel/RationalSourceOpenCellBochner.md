# Actual weighted source measure and Bochner integration

Author: Worker 200.

This is a derived continuation of Waldspurger (2003), I.1, second formula
(2), printed p.240 / PDF p.6. The actual rational-point setting, canonical
topology and common compact-open Haar normalization are those of
`RationalSourceOpenCellCoordinates`. The local field and real normed target
have independent universes. The field has arbitrary characteristic.

The source multiplication map sends `(u,(m,v))` to `u*m*v`. The unweighted
product measure is the existing `du*(dm*dv)` at the common compact scale.
The density is the inverse of the actual radical conjugation modulus at
`m`. The source measure is the pushforward of this explicitly weighted
product; no scalar is selected to force an ambient measure identity.

The nonnegative pushforward formula follows from map and density
integration and Tonelli. Equality of ambient Haar with the original gamma
inverse times the weighted pushforward follows by extensionality from the
published source-coordinate formula. Connected reductivity and
compact-limit stability remain explicit hypotheses of this equality.

For every ambient Bochner-integrable function, the weighted coordinate
pullback is integrable with respect to the original product measure. This
follows by removing the finite positive gamma scalar, transporting
integrability along the measurable source multiplication, and the
finite-density integrability criterion. The product Bochner formula uses
this measure identity and change of variables. The iterated U,M,opposite-U
formula uses Fubini, with fiber integrability derived
almost everywhere from the proved product integrability, and moves the
real inverse-modulus scalar out of the innermost integral. The formulas use
Mathlib's Bochner integral, which is defined to be zero for an incomplete
target; for Banach targets these are the usual Bochner formulas.

These results retain compact-limit stability and the precise common
compact normalization. They do not assert a general special-compact
realization, the source Iwasawa expression for gamma, same-Levi
independence or the main Plancherel conclusions.

The local topology, measurability and countability instances have explicit
module-specific names, so sibling integration modules can be imported
together. Their types and bodies, every mathematical declaration and all
hypotheses are unchanged by this naming correction.
