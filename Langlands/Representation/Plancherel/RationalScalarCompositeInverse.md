# Explicit inverses from two scalar composition identities

This internal algebraic helper supports the inverse of the reverse induced
dual operator in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, V.3, formula (1), printed p.295 / PDF p.61 (registered source
`waldspurger-2003-plancherel`). Its displayed continuation uses the existing
IV.1 finite-expansion convention, printed pp.276–277 / PDF pp.42–43.
No composition identity of the standard integrals is proved here.

The two complex vector spaces have independent universes and may be infinite
dimensional. For specified linear maps `R : V → W`, `S : W → V` and scalar `c`,
`ScalarComposite.inverse c S` is the explicit map `c⁻¹ • S`.
The identities `S R = c id` and `R S = c id`, together with `c ≠ 0`, give its
left and right inverse identities respectively. Together they prove
bijectivity of the particular `R`. The explicit formula agrees with the
inverse obtained from any bijectivity witness for `R`. The proofs evaluate
the given linear-map identities and cancel the scalar; they use no
irreducibility or finite-dimensionality assumption.

For an existing `RationalOperatorContinuationData` presentation `p`, and two
elements `a,b` of the actual evaluation algebra `unramifiedRegularFunctions ν`,
`p.regularRatioSmul a b hb` presents `(a/b) • A` on the original starting
region. Its denominator is `b * p.denominator`, and its polynomial numerator
is `a • p.numerator`. Here `hb` says `b` is nonzero on the starting region.
The whole-operator denominator is fixed before any input vector. The regular
region is exactly the intersection of `b ≠ 0` with `p.regularRegion`.
The continued value is `(a/b) • p.continuedOperator`. It is also
`ScalarComposite.inverse (b/a) p.continuedOperator`, by inversion of the
displayed scalar ratio. These are identities of particular presentations;
they assert neither a maximal regular domain nor regularity at excluded points.

Thus, if the actual scalar-composition factor is displayed as `b/a`, the
presentation just constructed is the proposed inverse. To use it as the
inverse of an actual standard operator still requires both actual composition
identities, their scalar nonvanishing on the chosen locus, and actual
continuation data for the other map. Those are visible additional obligations,
not results of this module. No generic nonempty or dense locus, standard-family
identification, scalar-composition theorem or all-unitary extension is
asserted. The norm-character family `ν` remains an arbitrary displayed family;
specializing it to all rational-character norms belongs to the actual adapter.
