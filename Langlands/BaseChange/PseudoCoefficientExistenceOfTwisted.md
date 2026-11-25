# Untwisted pseudo-coefficient existence from twisted existence

`Langlands.BaseChange.PseudoCoefficientExistenceOfTwistedStatement.{v,w}`
is the derived proposition

```lean
TwistedPseudoCoefficientExistenceStatement.{v, v, w} → PseudoCoefficientExistenceStatement.{v, w}
```

The field universe `v` and the representation-carrier universe `w` are
independent. The **only premise** is the Library's twisted pseudo-coefficient
existence statement in equal field universes. The conclusion is exactly the
unchanged Library statement for `GL_n(F)` over a characteristic-zero
nonarchimedean local field. It gives a Schwartz–Bruhat function with trace
one at the given irreducible admissible square-integrable representation
and trace zero at inequivalent irreducible admissible tempered tests with
the same central character, for the supplied Haar measure.

## Proof and remaining premise

`pseudoCoefficientExistenceOfTwisted` applies the previously proved
[`pseudoCoefficientExistenceReduction`](PseudoCoefficientExistenceReduction.md)
and discharges its `SquareIntegrableNotInducedStatement` premise using
[`squareIntegrableNotInduced`](SquareIntegrableNotInduced.md). In the reduction,
the non-induction theorem is used with square-integrable temperedness
and the identity intertwiner to produce the Library's `IsSigmaDiscreteSeries`
at `σ = 1`. The reduction then instantiates twisted existence at `E = F`,
`σ = 1`, `l = 1`, with the identity intertwiner. The ordinary and twisted
trace tests coincide for this choice, so the same function works; no
averaging of its support or change of Haar measure is needed in this step.

This is an internal conditional reduction for the ordinary form of
Henniart–Lemaire 2011, II.5.13 (printed pp. 113–114), with their identity-case
comparison in II.1.7 (p. 59) and trace formula in II.2.7 (p. 67). The new
proof is the non-induction argument detailed in
[`PadicSquareIntegrableNotInduced`](PadicSquareIntegrableNotInduced.md).
The `TwistedPseudoCoefficientExistenceStatement` premise is
not proved here. The module therefore does not assert unconditional
pseudo-coefficient existence.
