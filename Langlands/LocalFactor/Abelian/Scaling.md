# Additive-character scaling of the abelian epsilon expression

This internal proof module derives fixed-Haar scaling from the Library's concrete
abelian expression. Its input is any supplied finite p-adic topological datum;
the measure, additive character and multiplicative quasicharacter are actual
objects, with no analytic existence premise.

`abelianScalingFactor` bundles the correction as a multiplicative map from
field units to complex units. At a unit `a` its complex value is
`χ(a) |a|⁻¹`; positivity of the normalized absolute value makes this a unit.
The map laws follow from multiplicativity of the character and the normalized
absolute value. The final `abelianEpsilonExpression_scale_factor` theorem
expresses the scaling identity using this bundled correction.

The conductor transport uses the published valuation-lattice transport and
greatest-triviality characterization. It increases the additive conductor by
the order of the scalar. Multiplication therefore takes the new epsilon shell
to the old shell.

For an unramified character, the scale-independence theorem permits using the
scalar times the old chosen scale in the new expression. Multiplicativity of
the quasicharacter and normalized absolute value gives the required factor.

For the ramified integral, multiplication by the nonzero scalar is a measurable
embedding. The set-integral change-of-variables theorem identifies integration
over the new shell with integration over the old shell against the pushed
forward measure. The published scalar Haar theorem identifies that measure as
the original measure times the inverse normalized absolute value. The
quasicharacter extended by zero remains multiplicative under multiplication by
a field unit, including at zero. Consequently the transformed integrand is the
old integrand times the value of the quasicharacter at the scalar. This proves
`abelianGaussIntegral_scale` without a functional-equation premise.

The combined theorem `abelianEpsilonExpression_scale` splits according to
whether the multiplicative character is unramified and proves

```text
ε(χ, ψ(a·), μ) = χ(a) |a|⁻¹ ε(χ, ψ, μ).
```

Here `ε` denotes exactly `T.abelianEpsilonExpression`, the Haar measure stays
fixed, and the absolute value is `T.normalizedAbs`. Every result quantifies over
any prime, carrier universe and supplied `T`; the topological ring instances
are obtained from that same datum. No nonvanishing or system-existence
assertion is used.

This is an internal derivation for the nonabelian scaling proof. It is the
rank-one case of Deligne, *Les constantes des
équations fonctionnelles des fonctions L* (1973), formula (5.4), with fixed Haar
measure. The registered source is `deligne-1973-local-constants`; this module
uses its normalization through the existing abelian expression rather than
assuming the formula.
