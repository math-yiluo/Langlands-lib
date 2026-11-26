# Induction for the parabolic vanishing criterion

For `R ≤ Q`, `constantTerm_constantTerm_of_le_of_rationalParabolicInvariant` proves that averaging along `Q` before averaging along `R` gives the same result as averaging along `R`. The input is continuous and left invariant by the rational points of `R`. The radicals are nested in the opposite order. Rational points of the outer radical preserve the normalized measure on the compact quotient of the inner radical by conjugation. The compact subgroup-averaging identity then removes the inner average. The proof descends the restricted function to the outer radical quotient using only the stated rational invariance.

`AdelicCuspidalAlongSeparation` asks whether a continuous moderate function on one parabolic quotient that is relatively cuspidal and in the annihilator along that parabolic must vanish. Assuming this separation, `eq_zero_of_cuspidalAlongSeparation` applies strong induction to the cardinality of the simple-root subset of `Q`. The term `C_Q f` is moderate and continuous on the `Q`-quotient. For `R < Q` its `R`-constant term is `C_R f` by transitivity, and this is zero by induction. The assumed separation applied with the given test along `Q` now gives `C_Q f = 0`. The mass-one average `C_P f` equals `f` because `f` is invariant under the adelic radical of `P`.

This implements the semisimple-rank induction in Mœglin–Waldspurger I.3.4, pp. 45–46, for the fibrewise parabolic tests of Bernstein–Lapid (6.8) and (8.1). `parabolicCuspidalVanishingReduction` packages the argument for the exact `ParabolicCuspidalVanishingStatement` with separation on the relatively cuspidal part as its premise.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, I.3.4, pp. 45–46.
- `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`, `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`, (6.8), p. 202, and (8.1), p. 221.
