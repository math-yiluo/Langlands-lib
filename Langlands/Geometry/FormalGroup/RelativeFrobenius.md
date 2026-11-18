# Actual relative Frobenius of formal groups and formal order modules

This internal construction gives the actual relative Frobenius formal maps,
including their original complete power series and order-equivariance. It
supplies the formal-map part of the Frobenius comparison needed in Drinfeld's
moduli action.

Let `R` be a commutative ring of exponential characteristic `p`, and let `n` be a
natural number. Exponential characteristic includes the characteristic-zero
case `p = 1`, when the maps are identities. For each coordinate set `σ`,
`CoordinateMap.frobeniusPow p n` has series exactly `X_i^(p^n)`. The exponent is
positive because exponential characteristic is nonzero, so each series has
zero constant coefficient. For finite coordinates, `frobeniusPow_zero` and
`frobeniusPow_add` prove the identity and composition equations for these actual
formal maps. Evaluation on a substitutable series point raises each original
series coordinate to `p^n`, as exposed by `eval_frobeniusPow`.

`frobeniusPow_natural` proves the complete formal-series equation
`Frob_τ ∘ f = f^(p^n) ∘ Frob_σ` for every pointed formal coordinate map `f`, where
the superscript on `f` means applying `iterateFrobenius R p n` to all its
coefficients. Its proof uses substitution of a power and Mathlib's
`MvPowerSeries.map_iterateFrobenius_expand`: coefficient Frobenius followed by
expanding variable exponents is the power-series `p^n`-th power. The proof
commutes coefficient mapping with expansion before replacing expansion by
actual formal substitution. Equality is in the full formal power series.
`map_frobeniusPow` also shows that the variable-power map is preserved under
arbitrary coefficient-ring extension to another ring of the same exponential
characteristic.

For an actual commutative formal group law `G`, `CommLaw.frobeniusHom` is an
actual formal group homomorphism to its coefficient-Frobenius twist. Its
coefficient map `φ` is required to be proved equal to the actual iterate
Frobenius. The addition equation is naturality for the actual group addition,
using the proved identity between the power map on a sum of coordinate sets
and the pair of its two projected power maps.

For an actual formal `O`-module `M`, the coefficient map is an actual
`O`-algebra endomorphism `θ` together with a proof
`θ.toRingHom = iterateFrobenius R p n`. This hypothesis ensures that the
coefficient Frobenius fixes the supplied scalar action. `ModuleLaw.frobeniusHom`
uses the same power series and proves scalar commutation by formal naturality.
`OrderAction.frobeniusHom` proves commutation with every element of an actual
acting order in the same way. Its `frobeniusHom_coordinates` lemma retains
exactly the original variable-power series.

The provenance is internal, derived from actual formal coordinate
substitution, the existing coefficient-change definitions, and Mathlib's
proved characteristic-power-series identity. The source motivation is the
natural Frobenius quasi-isogeny in Drinfeld 1976, §2 A, printed p.109. This file
constructs its relative formal-map ingredient. Finite locally free kernel
representations, affine fppf local surjectivity, the rational inverse,
kernel-rank height and the final residue-field/Frobenius normalization are
further obligations; none is assumed or asserted by these definitions.
