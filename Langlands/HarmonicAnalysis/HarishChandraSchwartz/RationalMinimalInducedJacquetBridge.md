# The represented model of the normalized Jacquet module of `I_{P₀}^G 1`

The canonical represented standard parabolics for `∅` and `J` have point images
equal to the corresponding standard parabolic, Levi, and radical subgroups.
The actual point map of the represented Levi, followed by transport along this
equality, gives `representedStandardLeviPointsEquiv`.

The represented normalized induction pulls back the trivial representation of
the minimal Levi to the trivial representation of its point image. The
identity on the coefficient field intertwines these two trivial actions.
Applying induction to this isomorphism and using the three point-image
equalities identifies the induced representation with `rationalMinimalInduced`.

The represented Jacquet functor sends this isomorphism to the normalized
Jacquet module of the actual induction. Under the point-image equalities, its
radical and Levi are the same closed subgroups as in
`rationalMinimalInducedJacquet`. The two actions use the same inverse half of
the Haar modulus. Twisting `Jacquet.Localization.trivialEquiv` by that
character identifies the localized quotient with the ordinary coinvariants.
Pullback along the represented Levi point isomorphism makes the identification
equivariant.

The filtration proof and the comparison use `representedTrivialInducedJacquet`
for the represented Jacquet functor applied to the normalized induction of the
trivial source Levi character, with the result viewed as a representation.

`rationalMinimalInducedJacquetUnipotent_of_represented` takes a uniform
nilpotence exponent on the center of the represented Levi. The inverse point
isomorphism carries each central point of the standard Levi to a central point
of the represented Levi. Conjugation by the linear equivalence of Jacquet
modules preserves subtraction, the identity and powers, so the same exponent
works in the target model.

This internal comparison supports the application of the represented geometric
lemma to Waldspurger's `I_{P₀}^G 1`. The source locators and normalization
conventions are recorded in `RationalMinimalInducedJacquetStatement.md`.
