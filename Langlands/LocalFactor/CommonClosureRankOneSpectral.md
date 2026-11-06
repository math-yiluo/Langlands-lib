# Rank-one spectral twists of common-closure local constants

Workers 1237 and 1749 derive this component from the published conductor,
abelian Gauss-expression, reciprocity and exact-character-line constructions.
It introduces no reciprocity family or local-constant system. Its internal
definitions package the actual comparisons used below.

`IsAbsTwist T η η' s` means that, on every nonzero field element,
`η' = η · exp(s log |·|_T)`. The normalized absolute value is one on every
principal-unit group. Thus the two characters have identical triviality
levels, and `multiplicativeConductor_eq_of_isAbsTwist` proves equality of
their intrinsic conductors.

`twistExponent T η ψ` is the integer `n(ψ) + a(η)`. The theorem
`abelianEpsilonExpression_of_isAbsTwist` proves

```
ε(η', ψ, μ) = ε(η, ψ, μ) · exp(-s · (n(ψ) + a(η)) · log q_T).
```

In the unramified branch the prescribed scale has absolute value
`q_T ^ (-(n(ψ) + a(η)))`, which gives the displayed factor directly.
In the ramified branch, the two convergent integrals use the same compact
valuation shell because their conductors coincide. The absolute value is
constant on that shell. Inverting the twist factor in the Gauss integrand
therefore extracts the displayed constant from the integral. The supplied
additive character and Haar measure remain the inputs throughout.

`fieldCharacterEquiv F e E` first descends a continuous character of the
actual common-closure Weil subgroup through its topological abelianization,
then transports it along the supplied reciprocity component. Its inverse
is exactly `CommonClosure.weilCharacter`. Surjectivity of the quotient
projection and of the reciprocity equivalence proves
`reciprocityUnits_surjective`.

`character_eq_norm_exp` uses the normalization conjunct of
`NormalizedReciprocity F e` at the image of the original Weil-group element.
It identifies the restricted base-degree spectral character with the
absolute-value exponential on `E`. In particular, no separately normalized
Weil group for `E`, residue-degree comparison, or extra transport law is
assumed. Surjectivity then proves that transporting a spectral product of
Weil characters is an `IsAbsTwist`.

The system's rank-one relation gives `value_characterClass` for every
continuous Weil character after that proved descent and transport.
`continuousTwist_characterClass` identifies the actual exact virtual twist
with the product character line. Applying the abelian formula expresses
the supplied system value as a constant times an exponential linear in
the complex parameter. `analyticAt_const_mul_exp` proves that function
analytic everywhere using the complex exponential's analyticity.

The resulting theorem `weilCharacter_analyticAt` applies to every
supplied system satisfying `IsSystem`, every finite intermediate field in
the specified closure, every supplied additive character and Haar measure,
and every continuous rank-one Weil character. It retains independent
field and representation-carrier universes. Extending this component to
arbitrary exact virtual classes still requires the generation and
induction arguments; the module does not claim the whole
`CommonClosureSpectralAnalyticStatement`.

The surjectivity wrapper reuses `CommonClosure.reciprocityUnits_surjective`.
