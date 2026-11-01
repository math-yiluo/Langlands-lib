# Conditional quasicuspidal Jacquet class comparison

`Langlands.Aubert.quasicuspidalJacquetClass.{uF,uV} F T` proves exactly
`Langlands.Aubert.QuasicuspidalJacquetClassStatement.{uF,uV} F T`.
For actual finite-length smooth complex representations `π,τ`, it assumes
`D([π]) = ε • [τ]`, where `ε` is `1` or `-1`, and assumes the actual reversed
Jacquet module `J_{B.reverse}(π)` is nonzero and quasicuspidal. It concludes
`ε = (-1)^(n - B.length)` and equality of the actual Jacquet classes after
the specified reversed-to-original Levi transport.

The argument evaluates the published `jacquetCompatibility` identity on
the actual exact class of `π`. The generator formula for
`normalizedJacquetK0` identifies the reversed Jacquet value with the class of
the literal smooth object `JR`. Its finite length follows from the published
normalized Jacquet preservation theorem. Applying
`alternatingOperatorOnLevi_quasicuspidal` replaces its Levi Aubert image by
`(-1)^(n - B.reverse.length) • [JR]`. Reversal preserves the number of
blocks.

Write `JT` for the actual `B`-Jacquet module of `τ`, and `C` for the literal
transport of `JR` along `B.reversePermutation`. Both have finite length.
The transport is inverse-conjugation pullback and retains the original
carrier, so `C` is nonzero. The published `leviTransportK0` generator formula,
and integer linearity of both maps, turn the compatibility identity into

`ε • [JT] = (-1)^(n - B.length) • [C]`.

Two private helpers establish the needed positivity of the existing
integer-valued `FiniteLengthGrothendieckGroup.compositionLength`. Choose an
actual finite composition series. The published series formula says that
its class has integer composition length equal to the natural number of
steps, so this value is nonnegative. For a nonzero carrier, that number of
steps cannot be zero: the representation-length formula would give length
zero, and `repLength_eq_zero_iff` would make its carrier subsingleton.
Thus the value for `C` is strictly positive.

Applying this integer-linear invariant to the displayed class identity
gives an equality of signed integers with a nonnegative left length and a
strictly positive right length. The four cases of `ε` and the power of
`-1` rule out the two opposite-sign cases by integer arithmetic. The two
remaining cases give the asserted sign. Substituting it in the class
identity and cancelling scalar multiplication by `1` or `-1` gives the
required class equality.

This is an internal algebraic derivation from the published actual
Jacquet compatibility, quasicuspidal eigenvalue, finite-length transport
and composition-length results. It retains arbitrary primes, supplied
topological data, every rank including zero, independent `uF,uV`, and
saturated carriers `Type (max uF uV)`. The normalized induction convention
is upper-parabolic positive half-modulus covariance and right translation;
Jacquet restriction uses inverse half-modulus action on upper-unipotent
coinvariants.

No classification theorem, signed-image existence, admissibility,
irreducibility or analytic spectrum comparison is used. The conclusion is
equality of genuine exact classes; it asserts no equivalence of the actual
representations. It does not prove the host segment classification.
