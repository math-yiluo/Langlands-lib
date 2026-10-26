# The full unitary central character of actual normalized induction

`Langlands.GLNormalizedInductionUnitaryCentralCharacterStatement` is a closed
proposition defining the exact central-character prerequisite for analytic
temperedness of actual normalized parabolic induction. This module states the
assertion; it does not prove it.

Quantify over every prime `p`, algebraic `PadicField.{uF} p`, supplied
`F.TopologicalData T`, total rank `n`, actual ordered block shape `B`, complex
carrier `V : Type uV`, and representation `σ` of the actual product Levi
`B.Levi F.Carrier`. The universes `uF` and `uV` are independent. Use the
topologies induced by the supplied `T`. For every supplied
`c : UnitaryCentralCharacter σ`, the assertion gives

```text
cI : UnitaryCentralCharacter (T.normalizedParabolicInduced B σ)
```

with the prescribed value, for every element `z` of the full ambient center,

```text
cI.character z = c.character (B.centerToLeviCenter F.Carrier z).
```

The map on the right is the published restriction of the actual diagonal-block
projection from the full ambient center to the full Levi center. Thus the
assertion fixes the entire character. It does not assert uniqueness of all
central-character data, which need not hold on a zero carrier.

`UnitaryCentralCharacter` requires an open kernel, values of norm one, and the
actual scalar action on every vector. Consequently its existence here includes
all three properties on the full ambient center. No smoothness, admissibility,
irreducibility, nonzero carrier, finite length, positive form, or tensor
factorization is assumed. Rank zero is included. There are no Haar measures or
matrix-coefficient estimates in this assertion.

The representation is the published actual normalized induction from the
standard upper block parabolic, with covariance
`f(m u g) = δ_P(m)^(1/2) σ(m) f(g)` and right translation. The half modulus is
the actual positive square root of the explicit block modulus. Neither this
construction nor its normalization is altered.

The provenance is internal. This is the p-adic induction specialization of the
published full-center pullback construction in
[LeviCenterRestriction](LeviCenterRestriction.md), combined with the existing
scalar-action assertion `Parabolic.NormalizedInductionCentralClause` in
[NormalizedCompatibilityStatement](NormalizedCompatibilityStatement.md).
The intended deduction is as follows. Restrict `c.character` to the common
scalar tuple `(a I_(n_i))_i`. The scalar clause must prove that right translation
by the actual ambient scalar `a I_n` acts by this value, including cancellation
of the genuine positive half modulus. The full-center constructor then pulls
back the character, its open kernel, and its norm-one property and uses that
action identity. The statement contains no scalar-action premise: the
induction calculation remains a proof obligation and cannot be inferred from
the generic conditional constructor alone.

No additional literature assertion is made. This focused prerequisite does
not establish analytic temperedness, a Jacquet-exponent bound, or any
classification theorem, and does not change the hypotheses of the separate
analytic induction-preservation statement.
