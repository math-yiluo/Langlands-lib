# Characteristic-power root maps over arbitrary affine bases

This internal construction supplies the proposed maps on individual additive
root groups for the affine split isogeny theorem. It constructs no ambient
homomorphism and asserts no compatibility between distinct root groups.

`AdditiveLinePower.powerMap q` is the actual scheme map on the standard additive
line over `Spec R` whose pullback coordinate is `X^q`.
`AdditiveLinePower.powerHom` promotes it to a group homomorphism when `q` is
positive and that monomial is additive on every test scheme. Its point formula
is proved through the standard vector-group coordinate equivalence.

For `f : RootDatumIsogeny p Q P` on finite coordinate lattices, assume the
characteristic condition of the published affine isogeny statement:
`f.rootFactor j' ≠ 1` implies `(p : R) = 0`.
`add_pow_rootFactor` proves additivity of the root-factor monomial on every
`R`-algebra. For root factor one this is immediate. Otherwise `p` is prime,
`p` vanishes in the algebra, and the published arbitrary-ring prime-power
binomial identity applies. Applying this to the algebra of global sections
gives `add_pow_rootFactor_sections`; it also covers the zero ring.

`AffineRootDatumIsogeny.rootPower f hchar j'` is therefore an actual
endomorphism of the additive group over `R`. Composing it with a supplied
target root parametrization gives `rootMap f hchar j' u'`. The theorem
`rootPoint_rootMap` proves the formula `c ↦ u'(c^(f.rootFactor j'))`
on every test scheme.

`root_character` combines the prescribed torus-map character formula with
`f.root_weightMap` to prove the actual root-character equation.
`root_charValue` evaluates it on all test schemes.
Finally, `rootMap_equivariant` combines this equation, the supplied target
root parametrization's torus equivariance and the identity
`(a*c)^q = a^q*c^q`. Thus the powered target root map transforms under the
source torus with the source root `P.root (f.indexEquiv j')`.

The provenance is internal: the construction uses the published root-datum
isogeny data, the standard vector-group point model and the prescribed torus
map in `AffineSplitIsogenyTorusMap`. Additivity uses the existing arbitrary-ring
lemma in `Rational.TorusLinearization.AdditivePolynomials`. No field,
reducedness, locality, or nonzero-ring assumption is imposed on the base ring.

`AdditiveLinePower.coordinate` reuses `LocalSplitCell.gaCoord`.
