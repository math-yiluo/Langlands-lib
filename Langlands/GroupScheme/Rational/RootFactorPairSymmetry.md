# Equal opposite factors and torus squares from local inversion

This internal module implements the algebra and descent in the
nonmultipliable-root argument of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, second edition (2015), Proposition C.2.24(iii), printed pp.621–622
(PDF pp.647–648), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`.
It retains uniqueness, local inversion and root-negation premises
explicitly.

`HasEqualOppositeFactors i a` states that every normalizing opposite pair
for a nonidentity rational point of the actual `a`-root subgroup has equal
factors. It does not assert the existence of any pair.

Inverting a pair reverses its factors.
`IsOppositeFactorPair.inv_same_order_of_local_inversion` constructs the
same-order inverse pair: over an fpqc cover its product is the conjugate
of the original normalizer by a torus point that inverts the three
factors. This product is a restriction of a rational point.
Fpqc descent of normalization therefore makes it an actual rational
opposite pair. Rational uniqueness at the inverse point now equates
the two inverse pairs and gives equality of the original factors.
No extension-field uniqueness or persistence of maximal splitness under
field extension is assumed.

`square_mem_torus_of_local_inversion` proves that a rational normalizer
`m` inverted by a torus point `s` on an fpqc cover has its square in the
actual rational torus image. Locally, inversion gives
`m * m = m * s * m⁻¹ * s⁻¹`. Normalization puts the right side in the
torus image. The existing effective-epimorphism descent lemma descends
this factorization through the monomorphic torus map.

`IsOppositeFactorPair.fst_eq_conj_of_equal_factors` implements the last
algebraic step of the cited source argument. Write `m = v * x * v`.
Root negation puts `m⁻¹ * v * m` in the `a`-root subgroup and
`m⁻¹ * x * m` in its opposite. The identity
`v * (m⁻¹ * v * m) * (m⁻¹ * x * m) = m`
therefore gives another normalizing opposite pair. The universal
equal-factor hypothesis applied to that pair proves
`v = m⁻¹ * x * m`.

These reductions do not prove geometric pair existence, rational
uniqueness, the reflection property, existence of local inversion
points, or the source structural statements needed to produce inversion.
They do not yet prove the exact rank-one factorization target.
